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
#include "deps/RedisRaft/include/raft.h"
#include "deps/RedisRaft/include/raft_log.h"
#include "deps/RedisRaft/include/raft_private.h"
}

#define DATA_LEN 8

string state_machine = "init";

enum {
    MSG_AE,
    MSG_AER,
    MSG_RV,
    MSG_RVR
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
    return net->send_to(raft_node_get_id(node), data) == (ssize_t)data.size() ? 0 : -1;
}

static string serialization_ae(raft_appendentries_req_t* msg) {
    string data;
    data.resize(sizeof(*msg) + msg->n_entries * (DATA_LEN + sizeof(raft_entry_req_t)));
    *(raft_appendentries_req_t*)&data.front() = *msg;
    for (long i = 0; i < msg->n_entries; i++) {
        auto *p = (raft_entry_req_t *)((char *)&data.front() + sizeof(*msg) + (sizeof(raft_entry_req_t) + DATA_LEN) * i);
        *p = *(msg->entries[i]);
    }
    return data;
}

static raft_appendentries_req_t* deserialization_ae(string &data) {
    auto* msg = static_cast<raft_appendentries_req_t *>(raft_calloc(1, sizeof(raft_appendentries_req_t)));
    *msg = *(raft_appendentries_req_t*)&data.front();
    // should be freed after use!
    msg->entries = static_cast<raft_entry_req_t **>(raft_calloc(msg->n_entries, sizeof(raft_entry_req_t*)));
    for (long i = 0; i < msg->n_entries; i++) {
        // should be freed by raft_entry_release()!
        msg->entries[i] = raft_entry_new(DATA_LEN);
        auto *p = (raft_entry_req_t *)((char *)&data.front() + sizeof(*msg) + (sizeof(raft_entry_req_t) + DATA_LEN) * i);
        *(msg->entries[i]) = *p;
    }
    return msg;
}

static void free_deserialization_ae(raft_appendentries_req_t* msg) {
    raft_entry_release_list(msg->entries, msg->n_entries);
    raft_free(msg);
}

static int raft_send_appendentries (
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node,
        raft_appendentries_req_t* msg
)
{
    string data = pack_msg(serialization_ae(msg), MSG_AE);
    return net->send_to(raft_node_get_id(node), data) == (ssize_t)data.size() ? 0 : -1;
}

static int raft_send_snapshot (
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node,
        raft_snapshot_req_t* msg
)
{
    assert(false);
    return 0;
}

static int raft_send_timeoutnow (
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node
)
{
    assert(false);
    return 0;
}

static int raft_load_snapshot
(
        raft_server_t* raft,
        void *user_data,
        raft_term_t snapshot_term,
        raft_index_t snapshot_index
)
{
    assert(false);
    return 0;
}

static int raft_get_snapshot_chunk
(
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node,
        raft_size_t offset,
        raft_snapshot_chunk_t* chunk
)
{
    assert(false);
    return 0;
}

//    /** Callback to retrieve monotonic timestamp in microseconds */
//    raft_timestamp_f timestamp;

static int raft_store_snapshot_chunk
(
        raft_server_t* raft,
        void *user_data,
        raft_index_t snapshot_index,
        raft_size_t offset,
        raft_snapshot_chunk_t* chunk
)
{
    assert(false);
    return 0;
}

static int raft_clear_snapshot
(
        raft_server_t* raft,
        void *user_data
)
{
    assert(false);
    return 0;
}

static int raft_applylog
(
        raft_server_t* raft,
        void *user_data,
        raft_entry_t *entry,
        raft_index_t entry_idx
)
{
    state_machine += string(" ") + entry->data;
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

static int raft_node_has_sufficient_logs (
        raft_server_t* raft,
        void *user_data,
        raft_node_t* node
)
{
    assert(false);
    return 0;
}

static raft_time_t raft_timestamp (
        raft_server_t *raft,
        void *user_data
)
{
    struct timeval curr;
    if (gettimeofday(&curr, NULL) == -1)
        throw_syserror("gettimeofday");
    return curr.tv_sec * 1000000 + curr.tv_usec;
}

static void print_raft_log(
        raft_server_t* raft,
        void *user_data,
        const char *buf
)
{
    cerr_detail << buf << endl;
}

raft_cbs_t raft_cbs = {
        .send_requestvote = raft_send_requestvote,
        .send_appendentries = raft_send_appendentries,
        .send_snapshot = raft_send_snapshot,
        .send_timeoutnow = raft_send_timeoutnow,
        .load_snapshot = raft_load_snapshot,
        .get_snapshot_chunk = raft_get_snapshot_chunk,
        .store_snapshot_chunk = raft_store_snapshot_chunk,
        .clear_snapshot = raft_clear_snapshot,
        .applylog = raft_applylog,
        .persist_metadata = raft_persist_metadata,
        .get_node_id = raft_get_node_id,
        .node_has_sufficient_logs = raft_node_has_sufficient_logs,
        .timestamp = raft_timestamp,
        // optional
        .notify_membership_event = nullptr,
        .notify_state_event = nullptr,
        .notify_transfer_event = nullptr,
        .log = print_raft_log,
        .backpressure = nullptr,
        .get_entries_to_send = nullptr
};

bool RaftInit() {
    raft_server_t *me = raft_new();
    if (!me)
        return false;
    if (FLAGS_detail)
        raft_config(me, 1, RAFT_CONFIG_LOG_ENABLED, 1);
    cerr_verbose << "Raft init, self id: " << config.get_self_node().getid() << endl;
    raft_set_callbacks(me, &raft_cbs, nullptr);
    cerr_verbose << "Raft set callbacks" << endl;
    for (auto &i: config.get_all_nodes()) {
        Node &n = const_cast<Node&>(i);  // set data is not const, but will not affect sorting order
        cerr << "Raft add node, id: " << n.getid() << endl;
        n.set_data(raft_add_node(me, nullptr, n.getid(),  n.getid() == config.get_self_node().getid()));
    }
    config.set_raft_server(me);
    return true;
}

static int raft_send_appendentries_resp(const Node &node, const raft_appendentries_resp_t &msg) {
    string data;
    data.resize(sizeof(msg));
    *(raft_appendentries_resp_t*)&data.front() = msg;
    data = pack_msg(data, MSG_AER);
    return net->send_to(node, data) == (ssize_t)data.size() ? 0 : -1;
}

static int raft_send_requestvote_resp(const Node &node, const raft_requestvote_resp_t &msg) {
    string data;
    data.resize(sizeof(msg));
    *(raft_requestvote_resp_t*)&data.front() = msg;
    data = pack_msg(data, MSG_RVR);
    return net->send_to(node, data) == (ssize_t)data.size() ? 0 : -1;
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
        default:
            assert(false);
    }
    return true;
}

bool RaftPeriodic(raft_time_t msec = -1) {
    if (msec > 0) {
        return raft_periodic_internal((raft_server_t*)config.get_raft_server(), msec) == 0;
    } else {
        return raft_periodic((raft_server_t *) config.get_raft_server()) == 0;
    }
}

bool RaftClientOperation(string data) {
    auto *me = static_cast<raft_server_t *>(config.get_raft_server());
    raft_entry_resp_t resp;
    raft_entry_t  *ety = raft_entry_new(DATA_LEN);
    if (data.size() > DATA_LEN - 1)
        data.resize(DATA_LEN - 1);
    mempcpy(ety->data, data.c_str(), data.size());
    if (raft_recv_entry(me, ety, &resp) == 0) {
        cerr_verbose << "RaftClientOperation success, idx: " << resp.idx << " term: " << resp.term << endl;
        return true;
    } else {
        cerr_warning << "RaftClientOperation failed" << endl;
        return false;
    }
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
    }
    else {
        return false;
    }
    return false;
}

string RaftGet(const string &variable) {
    auto *me = static_cast<raft_server_t *>(config.get_raft_server());
    if (variable == "commit_idx") {
        return to_string(me->commit_idx);
    } else if (variable == "current_term") {
        return to_string(me->current_term);
    } else if (variable == "log") {
        // [(2, 'Nil'), (2, 'v1')]
        auto *log = static_cast<raft_log_t *>(me->log);
        string res = "[";
        raft_index_t base = raft_log_get_base(log);
//        cerr << "RAFT LOG COUNT: " << raft_log_count(log) << endl;
        for (int i = 1; i <= raft_log_count(log); i++) {  // starts from 1!
            raft_entry_t *ety = raft_log_get_at_idx(log, i + base);
            if (ety) {
                if (i != 1)
                    res += ", ";
                res += "(" + to_string(ety->term) + ", ";
                if (ety->type == RAFT_LOGTYPE_NO_OP)
                    res += "'Nil')";
                else if (ety->type == RAFT_LOGTYPE_NORMAL)
                    res += "'" + string(ety->data) + "')";
                else
                    res += "'?UNKNOWN?')";
            }
        }
        res += "]";
        return res;
    } else if (variable == "state") {
        return to_string(me->state);
    } else if (variable == "next_idx" || variable == "match_idx") {
        // {'n2': 2, 'n3': 2}
        vector<string> tokens;
        bool is_next_idx = variable == "next_idx";
        for (int i = 0; i < me->num_nodes; i++) {
            raft_node_t *n = me->nodes[i];
            if (raft_node_get_id(n) == raft_node_get_id(me->node))
                continue;
            Node node(raft_node_get_id(n));
            if (!config.get_node(node)) {
                cerr_warning << "RaftGet cannot find node: " << node.to_string() << endl;
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

// not implemented!
//void RaftAutoRun() {
//    if (!RaftInit()) {
//        cerr_warning << "cannot init" << endl;
//        abort();
//    }
//
//}