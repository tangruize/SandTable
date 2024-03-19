//
// Created by tangruize on 22-5-17.
//

#ifndef TPROXY_TCPNETWORK_H
#define TPROXY_TCPNETWORK_H

#include "common.h"
#include "TcpSocket.h"
#include "Command.h"
#include "Msg.h"
#include "RemoteControl.h"
#include <ctime>
#include <set>
#include <list>
#include <thread>
#include <memory>

//#include <readerwriterqueue.h>
#include <concurrentqueue/blockingconcurrentqueue.h>
using namespace moodycamel;

struct ChannelMsgs {
    BlockingConcurrentQueue<Msg> msgs;
//    BlockingReaderWriterQueue<Msg> msgs;
    bool deliver_next_msg;
    Msg *wait_merge = NULL;
    ~ChannelMsgs() {
        if (wait_merge != NULL) {
            delete wait_merge;
            wait_merge = NULL;
        }
    }
};

//typedef pair<struct sockaddr_in, struct sockaddr_in> channel_t;
struct channel_t {
    struct sockaddr_in first;
    struct sockaddr_in second;
    bool half_duplex_reverse_direction;  // not to choose this channel to receive in half duplex mode
    friend std::ostream & operator<<(std::ostream &os, const channel_t& channel);
    bool ok() const {
        return first.sin_port != (in_port_t)-1 && second.sin_port != (in_port_t)-1;
    }
};

struct channel_status_t {
    channel_t channel;
    shared_ptr<int> self_fd, fd;  // use shared pointer to invalidate buffered msgs whose connections are closed
    bool disconnected;
};

struct cmp_channel {
    cmp_addr_less less;
    cmp_addr_no_port_less less_no_port;
    cmp_addr_no_port_equal equal_no_port;
    bool operator()(const channel_t& a, const channel_t& b) const {
        if (a.half_duplex_reverse_direction == b.half_duplex_reverse_direction) {
            if (a.half_duplex_reverse_direction) {  // accept() connection: a.second port is ignored
                if (equal_no_port(a.second, b.second))
                    return less(a.first, b.first);
                return less_no_port(a.second, b.second);
            } else {  // connect() connection: a.first port is ignored
                if (equal_no_port(a.first, b.first))
                    return less(a.second, b.second);
                return less_no_port(a.first, b.first);
            }
        } else {
            return a.half_duplex_reverse_direction < b.half_duplex_reverse_direction;
        }
    }
};

class TcpNetwork {
private:
    TcpSocket *tcp;
    map<int, channel_status_t> fd_to_channel_status;
    map<channel_t, struct ChannelMsgs, cmp_channel> network;
    map<struct sockaddr_in, int, cmp_addr_less> client_to_fd;
    map<int, struct sockaddr_in> fd_to_client;
    set<int> unintercepted_fd;
    int epoll_fd;
    bool is_direct;
    const int max_events = 10;
    const struct timeval recv_timeout = { .tv_sec = 3, .tv_usec = 0};
    const int64_t deliver_timeout = recv_timeout.tv_sec * 1000000 + recv_timeout.tv_usec;  // reuse recv timeout
    const int syn_retries = 1;  // connection syn retry times. 1: ~3s timeout, 2: ~7s timeout, 0: ~127s (unintuitive)
    int server_count = 0;
    string net_status_cache;
    bool is_half_duplex;
    list<pair<AcceptData, channel_status_t>> pending_connections;
    vector<Msg> messages_array; // backward compatibility, for random access (allow_msg_unordered)
private:
    void set_recv_timeout(int fd);
    void set_conn_retries(int fd);
    int connect_peer(const AcceptData &acc);
    void add_fd_to_channel(int src_fd, int dst_fd, const AcceptData& acc);
    pair<int, int> do_accept_connect();
    void add_monitor_fd(int fd) const;
    void del_monitor_fd(int fd) const;
    void do_receive(int fd);
    void enqueue_msg(const channel_status_t &cf, Msg &m);
    bool deliver_msg(const channel_t &channel, Msg *m = nullptr, bool try_deliver = false);
    void do_close(map<int, channel_status_t>::iterator it);
    void close_connection(int fd, bool tag_disconnected=false, bool close_peer=true, bool reopen=false);
    bool packet_validation(const MsgHeader &header, unsigned size) const;
    void set_unintercepted(int fd, const channel_t &channel);
    void transfer_unintercepted(int out_fd, int in_fd);
    void clear_msgs(const channel_t &channel);
    static bool check_connection_is_active(int fd);
    string convert_cmd_check_has_recv_queue(const string &node, const string &c);
    void enqueue_messages_array(const Msg &msg);
public:
    static string channel_to_string(const channel_t &c);
    void partition(const string &node, bool clear_msg=false, bool is_recover=false);
    void recover(const string &node);
    void recover_no_disconnect(const string &node);
    bool send_cmd(const string &node, const string &cmd, int lineno);
    void init(int n_servers, int wait_ms);
    void wait_init(int n_servers, bool double_connection, int wait_ms);
    void wait_recover();
    bool deliver(const string &from, const string &to, bool all, unsigned seq=0);
    bool deliver_unordered(const string &from, const string &to, unsigned seq); // backward compatibility
    void print_status();
    string get_status_cache();
    void deliver_all(int least_count=0);
    void connect_pending();
    void print_connection_buffer(int fd, bool consume=false);
    void close_client(const string &node);
    void pre_close_client(const string &node);
    bool check_client_online(const string &node);
    bool send_cmd_all(const string &prefix, const string &cmd, int lineno);
    void clear_channel_msgs(const string &from, const string &to);
    int get_net_len();
public:
    explicit TcpNetwork(TcpSocket *tcp_socket, bool half_duplex=false);
    void run_epoll();
    std::thread run_epoll_background() { return std::thread( [this] { this->run_epoll(); } ); }
};

extern TcpNetwork *net;

#endif //TPROXY_TCPNETWORK_H
