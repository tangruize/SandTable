//
// Created by tangruize on 2/14/23.
//

#ifndef REDISTMET_CONFIG_H
#define REDISTMET_CONFIG_H

#include <set>
#include <string>
#include "Node.h"
//#include "deps/raft/include/raft.h"

using namespace std;

const int DEFAULT_PORT = 9000;

class Config {
    typedef map<struct sockaddr_in, struct sockaddr_in, cmp_addr_less> conv_map_t;
    conv_map_t cidr_map;
    conv_map_t rev_cidr_map;
    set<Node> nodes;
    string self_name;
    Node self_node;
    void *raft_server;
    set<Node>::iterator find_node(const Node &e) const;
    bool loading = false;
    struct sockaddr_in get_converted_addr(const struct sockaddr_in &to_conv, const conv_map_t &b) const;
public:
    Config();
    Config(const string &filename);
    void load(const string &filename);
    bool read(const string &line, int line_no=-1);
    bool getinfo(const string &cmd);
    bool get_node(Node &n) const;
    bool get_addr(const string &name, struct sockaddr_in &addr) const;
    bool get_name(const struct sockaddr_in &addr, string &name) const;
    bool set_self_node(const string& name = "");
    bool get_self_node(Node &n);
    Node &get_self_node();
    [[nodiscard]] set<Node> &get_all_nodes();
    void set_raft_server(void *s) { raft_server = s; }
    [[nodiscard]] void *get_raft_server() const { return raft_server; }
};

extern Config config;

#endif //REDISTMET_CONFIG_H
