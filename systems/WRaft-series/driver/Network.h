//
// Created by tangruize on 2/13/23.
//

#ifndef REDISTMET_NETWORK_H
#define REDISTMET_NETWORK_H

#include "common.h"
#include "Config.h"

class Network {
protected:
    map<Node, int> peers;  // node (for connectionless socket) -> file descriptor (for connection-based socket)
    Node self;
    volatile int sockfd = -1;
    int evfd = -1;  // auto recv, not implemented!
    string recvbuffer;
    [[nodiscard]] map<Node, int>::iterator find_node(const Node &e);
public:
    Network();
    int load_config();
    bool add_node(const Node &peer);
    virtual bool connect(const Node &n) { return true; }  // do nothing for connectionless socket
    virtual void connect_all() {}  // do nothing for connectionless socket
    virtual bool is_all_connected() { return true; }  // do nothing for connectionless socket
    virtual ssize_t send_to(const Node &peer, const string &data) = 0;
    virtual ssize_t recv_from(const Node &peer, string &data) = 0;
    ssize_t recv_from(const Node &peer) { return recv_from(peer, recvbuffer); }
    void shut_down();
    ~Network() { shut_down(); }
    static int set_nonblocking(int fd);
    bool repl(const string &cmd);
    string &get_recv_buffer() { return recvbuffer; }
};

extern Network *net;

#endif //REDISTMET_NETWORK_H
