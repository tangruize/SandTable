//
// Created by tangruize on 2/14/23.
//
// WARN: we do not consider endian problem while serialization.
// WARN: we do not consider 32-bit or 64-bit memory.

#include <cassert>
#include <sys/time.h>
#include "Raft.h"
#include "Network.h"

extern "C" {
#include "deps/WRaft/include/raft.h"
#include "deps/WRaft/include/raft_log.h"
#include "deps/WRaft/include/raft_private.h"
}

// snapshot message
typedef struct
{
    /** currentTerm, to force other leader/candidate to step down */
    raft_term_t term;
    /** the snapshot replaces all entries up through and including this index */
    raft_index_t last_included_idx;
    /** term of lastIncludedIndex */
    raft_term_t last_included_term;
} msg_snapshot_t;

typedef msg_requestvote_t raft_requestvote_req_t;
typedef msg_requestvote_response_t raft_requestvote_resp_t;
typedef msg_appendentries_t raft_appendentries_req_t;
typedef msg_appendentries_response_t raft_appendentries_resp_t;
typedef raft_entry_t raft_entry_req_t;
typedef msg_snapshot_t raft_snapshot_req_t;
typedef msg_entry_response_t raft_entry_resp_t;

#define DATA_LEN 0

string state_machine = "init";

enum {
    MSG_AE,
    MSG_AER,
    MSG_RV,
    MSG_RVR,
    MSG_SNAP
};

string pack_msg(const string &msg, int type) {
    string ret;
    ret.resize(4);
    *(int*)&ret.front() = type;
    ret += msg;
    return ret;
}

string unpack_msg(const string &msg, int &type) {
    assert(msg.size() > sizeof(int));
    type = *(const int*)&msg.front();
    return msg.substr(sizeof(int));
}

static int raft_send_requestvote (
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node,
        raft_requestvote_req_t* msg
)
{
    string data;
    data.resize(sizeof(*msg));
    *(raft_requestvote_req_t*)&data.front() = *msg;
    data = pack_msg(data, MSG_RV);
    return net->send_to(raft_node_get_id(node), data) > 0 ? 0 : -1;
}

static string serialization_ae(raft_appendentries_req_t* msg) {
    string data;
    data.resize(sizeof(*msg) + msg->n_entries * (DATA_LEN + sizeof(raft_entry_req_t)));
    *(raft_appendentries_req_t*)&data.front() = *msg;
    for (long i = 0; i < msg->n_entries; i++) {
        auto *p = (msg_entry_t *)((char *)&data.front() + sizeof(*msg) + (sizeof(raft_entry_req_t) + DATA_LEN) * i);
        *p = msg->entries[i];
    }
    return data;
}

static raft_appendentries_req_t* deserialization_ae(string &data) {
    auto* msg = static_cast<raft_appendentries_req_t *>(calloc(1, sizeof(raft_appendentries_req_t)));
    *msg = *(raft_appendentries_req_t*)&data.front();
    // should be freed after use!
    msg->entries = static_cast<msg_entry_t *>(calloc(msg->n_entries, sizeof(msg_entry_t)));
    for (long i = 0; i < msg->n_entries; i++) {
        // should be freed by raft_entry_release()!
        auto *p = (msg_entry_t *)((char *)&data.front() + sizeof(*msg) + (sizeof(msg_entry_t) + DATA_LEN) * i);
        msg->entries[i] = *p;
    }
    return msg;
}

static void free_deserialization_ae(raft_appendentries_req_t* msg) {
    free(msg->entries);
    free(msg);
}

static int raft_send_appendentries (
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node,
        raft_appendentries_req_t* msg
)
{
    string data = pack_msg(serialization_ae(msg), MSG_AE);
    return net->send_to(raft_node_get_id(node), data) > 0 ? 0 : -1;
}

static int raft_send_installsnapshot(
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node)
{
    msg_snapshot_t msg;
    msg.term = raft_get_current_term(raft);
    msg.last_included_idx = raft_get_snapshot_last_idx(raft);
    msg.last_included_term = raft_get_snapshot_last_term(raft);

    string data;
    data.resize(sizeof(msg));
    *(msg_snapshot_t*)&data.front() = msg;
    data = pack_msg(data, MSG_SNAP);
    return net->send_to(raft_node_get_id(node), data) > 0 ? 0 : -1;
}

static bool raft_recv_installsnapshot(
        raft_server_t* me,
        raft_node_t* sender,
        msg_snapshot_t* m,
        msg_appendentries_response_t *r)
{
    r->success = false;
    r->current_idx = raft_get_current_idx(me);
    r->first_idx = r->current_idx;
    r->term = raft_get_current_term(me);

    // according to raft paper
    if (m->term < raft_get_current_term(me))
        return true;

    if (raft_begin_load_snapshot(me, m->last_included_term, m->last_included_idx) != 0)
        return true;

    // re-add other servers since servers have been removed after load snapshot.
    for (auto &i: config.get_all_nodes()) {
        Node &n = const_cast<Node&>(i);  // set data is not const, but will not affect sorting order
        cerr << "Raft re-add node, id: " << n.getid() << endl;
        auto node = raft_add_node(me, nullptr, n.getid(),  n.getid() == config.get_self_node().getid());
        if (!node)
            continue;
        raft_node_set_voting_committed(node, true);
        raft_node_set_active(node, true);
        n.set_data(node);
    }

    raft_end_load_snapshot(me);

    r->success = true;
    r->current_idx = m->last_included_idx;
    r->first_idx = r->current_idx;
    r->term = raft_get_current_term(me);
    return true;
}

//static int raft_recv_installsnapshot (
//        raft_server_t* raft,
//        void *user_data,
//        raft_node_t* node,
//        msg_installsnapshot_t* msg,
//        msg_installsnapshot_response_t* r
//)
//{
//    assert(false);
//    return 0;
//}

static int raft_applylog
        (
                raft_server_t* raft,
                void *user_data,
                raft_entry_t *entry,
                raft_index_t entry_idx
        )
{
    char buf[sizeof(void*)] = {};
    memcpy(buf, &(entry->data.buf), sizeof(void*)-1);
    state_machine += string(" ") + buf;
    return 0;
}

static int raft_persist_metadata
        (
                raft_server_t *raft,
                void *user_data,
                raft_term_t term,
                raft_node_id_t vote
        )
{
    // not implemented
    return 0;
}

static raft_node_id_t raft_get_node_id (
        raft_server_t* raft,
        void *user_data,
        raft_entry_t *entry,
        raft_index_t entry_idx
)
{
    assert(false);
    return -1;
}

static long raft_get_timestamp ()
{
    struct timeval curr;
    if (gettimeofday(&curr, NULL) == -1)
        throw_syserror("gettimeofday");
    return curr.tv_sec * 1000000 + curr.tv_usec;
}

static void print_raft_log(
        raft_server_t* raft,
        raft_node_t* node,
        void *user_data,
        const char *buf
)
{
    cerr_detail << buf << endl;
}

static int raft_persist_vote (
        raft_server_t* raft,
        void *user_data,
        raft_node_id_t vote
)
{
    return 0;
}

static int raft_persist_term (
        raft_server_t* raft,
        void *user_data,
        raft_term_t term,
        raft_node_id_t vote
)
{
    return 0;
}

static int raft_log_offer (
        raft_server_t* raft,
        void *udata,
        raft_entry_t *ety,
        raft_index_t ety_idx)
{
    return 0;
}

static int raft_log_poll (
        raft_server_t* raft,
        void *udata,
        raft_entry_t *ety,
        raft_index_t ety_idx)
{
    return 0;
}

static int raft_log_pop (
        raft_server_t* raft,
        void *udata,
        raft_entry_t *ety,
        raft_index_t ety_idx)
{
    return 0;
}

static int raft_log_clear (
        raft_server_t* raft,
        void *user_data,
        raft_entry_t *entries,
        raft_index_t entry_idx,
        int *n_entries
)
{
    return 0;
}

static int raft_log_get_node_id(
        raft_server_t* raft,
        void *user_data,
        raft_entry_t *entry,
        raft_index_t entry_idx
)
{
    assert(false);
    return -1;
}

static int raft_node_has_sufficient_logs (
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node
)
{
    return 0;
}

static void raft_notify_membership_event (
        raft_server_t* raft,
        void *user_data,
        raft_node_t *node,
        raft_entry_t *entry,
        raft_membership_e type
)
{
}

//static int raft_recv_installsnapshot_response(
//        raft_server_t* raft,
//        void *user_data,
//        raft_node_t* node,
//        msg_installsnapshot_response_t* r
//)
//{
//    assert(false);
//    return -1;
//}

void RaftPrintLog(
        raft_server_t* raft,
        raft_node_t* node, void *udata,
        const char *buf)
{
    cout << "- [RAFT] "
         << "Server id: " << raft_get_nodeid(raft)
         << ", peer id: " << (node ? raft_node_get_id(node) : -1)
         << ", info: " << buf;
    int len = strlen(buf);
    if (len > 0 && buf[len - 1] != '\n')
        cout << endl;
    else
        cout << flush;
}


raft_cbs_t raft_cbs = {
        .send_requestvote = raft_send_requestvote,
        .send_appendentries = raft_send_appendentries,
        .send_snapshot = raft_send_installsnapshot,
        .applylog = raft_applylog,
        .persist_vote = raft_persist_vote,
        .persist_term = raft_persist_term,
        .log_offer = raft_log_offer,
        .log_poll = raft_log_poll,
        .log_pop = raft_log_pop,
        .log_clear = nullptr,
        .log_get_node_id = raft_log_get_node_id,
        .node_has_sufficient_logs = raft_node_has_sufficient_logs,
        .notify_membership_event = raft_notify_membership_event,
        .log = RaftPrintLog
};

bool RaftInit() {
    raft_server_t *me = raft_new();
    if (!me)
        return false;
    if (FLAGS_detail)
        raft_cbs.log = print_raft_log;
    cerr_verbose << "Raft init, self id: " << config.get_self_node().getid() << endl;
    raft_set_callbacks(me, &raft_cbs, nullptr);
    cerr_verbose << "Raft set callbacks" << endl;
    for (auto &i: config.get_all_nodes()) {
        Node &n = const_cast<Node&>(i);  // set data is not const, but will not affect sorting order
        cerr << "Raft add node, id: " << n.getid() << endl;
//        n.set_data(raft_add_node(me, nullptr, n.getid(),  n.getid() == config.get_self_node().getid()));
        auto node = raft_add_node(me, nullptr, n.getid(),  n.getid() == config.get_self_node().getid());
        raft_node_set_voting_committed(node, true);
        raft_node_set_active(node, true);
        n.set_data(node);
    }
    config.set_raft_server(me);
//    for (unsigned x = 0; x < config.get_all_nodes().size(); x++) {
//        cerr << "node " << x + 1 << ", id: " << raft_node_get_id(raft_get_node(me, (int)x + 1)) << endl;
//    }
    return true;
}

static int raft_send_appendentries_resp(const Node &node, const raft_appendentries_resp_t &msg) {
    string data;
    data.resize(sizeof(msg));
    *(raft_appendentries_resp_t*)&data.front() = msg;
    data = pack_msg(data, MSG_AER);
    return net->send_to(node, data) > 0 ? 0 : -1;
}

static int raft_send_requestvote_resp(const Node &node, const raft_requestvote_resp_t &msg) {
    string data;
    data.resize(sizeof(msg));
    *(raft_requestvote_resp_t*)&data.front() = msg;
    data = pack_msg(data, MSG_RVR);
    return net->send_to(node, data) > 0 ? 0 : -1;
}

bool RaftRecvMsg(Node node) {
    if (!config.get_node(node)) {
        cerr_warning << "RaftRecvMsg cannot find node" << endl;
        return false;
    }
    string data;
    if (net->recv_from(node, data) < 0)
        return false;
    int type;
    string msg = unpack_msg(data, type);
    auto *me = static_cast<raft_server_t *>(config.get_raft_server());
    auto *raft_node = static_cast<raft_node_t *>(node.get_data());
    switch (type) {
        case MSG_AE: {
            cerr_verbose << "RaftRecvMsg MSG_AE" << endl;
            raft_appendentries_req_t *req = deserialization_ae(msg);
            raft_appendentries_resp_t resp{};
            raft_recv_appendentries(me, raft_node, req, &resp);
            free_deserialization_ae(req);
            raft_send_appendentries_resp(node, resp);
            break;
        }
        case MSG_AER: {
            cerr_verbose << "RaftRecvMsg MSG_AER" << endl;
            raft_recv_appendentries_response(me, raft_node, reinterpret_cast<raft_appendentries_resp_t *>(&msg.front()));
            break;
        }
        case MSG_RV: {
            cerr_verbose << "RaftRecvMsg MSG_RV" << endl;
            // raft servers only vote for candidate after election timeout,
            // however TLA does not model it and servers are always votable.
            // advance timeout_elapsed to make the server votable.
            if (((raft_server_private_t*)me)->state != RAFT_STATE_LEADER
                && raft_get_timeout_elapsed(me) < raft_get_election_timeout(me)) {
                raft_periodic(me, raft_get_election_timeout(me));
            }
            auto *req = reinterpret_cast<raft_requestvote_req_t *>(&msg.front());
            raft_requestvote_resp_t resp{};
            raft_recv_requestvote(me, raft_node, req, &resp);
            raft_send_requestvote_resp(node, resp);
            break;
        }
        case MSG_RVR: {
            cerr_verbose << "RaftRecvMsg MSG_RVR" << endl;
            raft_recv_requestvote_response(me, raft_node, reinterpret_cast<raft_requestvote_resp_t *>(&msg.front()));
            break;
        }
        case MSG_SNAP: {
            cerr_verbose << "RaftRecvMsg MSG_SNAP" << endl;
            msg_appendentries_response_t resp{};
            raft_recv_installsnapshot(me, raft_node, reinterpret_cast<msg_snapshot_t *>(&msg.front()), &resp);
            raft_send_appendentries_resp(node, resp);
            break;
        }
        default:
            assert(false);
    }
    return true;
}

bool RaftPeriodic(int msec = -1) {
    if (msec > 0) {
        return raft_periodic((raft_server_t*)config.get_raft_server(), msec) == 0;
    } else {
        static long prev = 0;
        long current = raft_get_timestamp(), period = (current - prev) / 1000;
        if (prev == 0) {
            period = 0;
        }
        prev = current;
        return raft_periodic((raft_server_t *) config.get_raft_server(), period) == 0;
    }
}

bool RaftClientOperation(string data) {
    auto *me = static_cast<raft_server_t *>(config.get_raft_server());
    raft_entry_resp_t resp;
    raft_entry_t *ety = (raft_entry_t *)calloc(1, sizeof(raft_entry_t));
    if (data.size() >= sizeof(void *))
        data.resize(sizeof(void *) - 1);
    mempcpy(&(ety->data.buf), data.c_str(), data.size());
    if (raft_recv_entry(me, ety, &resp) == 0) {
        cerr_verbose << "RaftClientOperation success, idx: " << resp.idx << " term: " << resp.term << endl;
        return true;
    } else {
        cerr_warning << "RaftClientOperation failed" << endl;
        return false;
    }
}

// server exec snapshot
bool RaftExecSnapshot() {
    bool ok = raft_begin_snapshot(static_cast<raft_server_t *>(config.get_raft_server()), 0) != RAFT_ERR_SHUTDOWN;
    ok = raft_end_snapshot(static_cast<raft_server_t *>(config.get_raft_server())) != RAFT_ERR_SHUTDOWN && ok;
    return ok;
}

bool RaftRepl(const string &cmd) {
    auto tokens = tokenize(cmd);
    if (tokens.empty()) {
        return false;
    }
    if (tokens[0] == "init") {
        return RaftInit();
    } else if (tokens[0] == "recvfrom") {
        return RaftRecvMsg(tokens[1]);
    } else if (tokens[0] == "periodic") {
        if (tokens.size() > 1) {
            return RaftPeriodic(std::stoi(tokens[1]));
        } else {
            return RaftPeriodic();
        }
    } else if (tokens[0] == "cli") {
        if (tokens.size() <= 1)
            return false;
        return RaftClientOperation(tokens[1]);
    } else if (tokens[0] == "statemachine" ) {
        cerr << state_machine << endl;
        return true;
    } else if (tokens[0] == "snapshot") {
        return RaftExecSnapshot();
    }
    else {
        return false;
    }
    return false;
}

string RaftGet(const string &variable) {
    auto *me = static_cast<raft_server_private_t *>(config.get_raft_server());
    if (variable == "commitIdx") {
        return to_string(me->commit_idx);
    } else if (variable == "currentTerm") {
        return to_string(me->current_term);
    } else if (variable == "log") {
        // [(2, 'Nil'), (2, 'v1')]
        auto base = log_get_base((log_t*)me->log);
        string res = "[";
//        cerr << "RAFT LOG COUNT: " << raft_log_count(log) << endl;
        for (int i = 1; true; i++) {  // starts from 1!
            raft_entry_t *ety = log_get_at_idx((log_t*)me->log, i + base);
            if (ety) {
                if (i != 1)
                    res += ", ";
                res += "(" + to_string(ety->term) + ", ";
                if (ety->type == RAFT_LOGTYPE_NORMAL)
                    res += "'" + string((char *)(&(ety->data.buf))) + "')";
                else
                    res += "'?UNKNOWN?')";
            } else {
                break;
            }
        }
        res += "]";
        return res;
    } else if (variable == "state") {
        int state = me->state;
//        if (state == 3)
//            state = 4;  // leader
//        else if (state == 2) {
//            if (!me->prevote)
//                state = 3;  // candidate
//        }
        return to_string(state);
    } else if (variable == "nextIdx" || variable == "matchIdx") {
        // {'n2': 2, 'n3': 2}
        vector<string> tokens;
        bool is_next_idx = variable == "nextIdx";
        for (int i = 0; i < me->num_nodes; i++) {
            auto n = (raft_node_t *)me->nodes[i];
            if (raft_node_get_id(n) == raft_node_get_id(me->node))
                continue;
            Node node(raft_node_get_id(n));
            if (!config.get_node(node)) {
                cerr_warning << "RaftGet cannot find node: id: " << raft_node_get_id(n) << ", node_str: " << node.to_string() << endl;
                for (int x = 0; x < me->num_nodes; x++) {
                    cerr_warning_cont << "node " << x + 1 << ", id: " << raft_node_get_id(me->nodes + x) << endl;
                }
                return "";
            }
            string token = "'" + node.name + "': ";
            if (is_next_idx) {
                token += to_string(raft_node_get_next_idx(n));
            } else {
                token += to_string(raft_node_get_match_idx(n));
            }
            tokens.push_back(std::move(token));
        }
        std::sort(tokens.begin(), tokens.end());
        return "{" + stringify(tokens, 0, ", ") + "}";
    }
    return "";
}
