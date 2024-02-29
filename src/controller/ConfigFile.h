//
// Created by tangruize on 22-5-10.
//

#ifndef TPROXY_CONFIGFILE_H
#define TPROXY_CONFIGFILE_H

#include <map>
#include <vector>
#include <unordered_map>
#include <set>
#include <string>
#include <arpa/inet.h>

using namespace std;

// a < b
struct cmp_addr_less {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const {
        if (a.sin_addr.s_addr == b.sin_addr.s_addr)
            return a.sin_port < b.sin_port;
        return a.sin_addr.s_addr < b.sin_addr.s_addr;
    }
};

// a == b
struct cmp_addr_equal {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const {
        return a.sin_addr.s_addr == b.sin_addr.s_addr && a.sin_port == b.sin_port;
    }
};

// a < b (no port)
struct cmp_addr_no_port_less {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const {
        return a.sin_addr.s_addr < b.sin_addr.s_addr;
    }
};

// a == b (no port)
struct cmp_addr_no_port_equal {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const {
        return a.sin_addr.s_addr == b.sin_addr.s_addr;
    }
};

// a.ip + a.port
struct hash_addr {
    // (very unlikely) WARNING: may have collision if sizeof(size_t) == 4
    size_t operator()(const struct sockaddr_in& addr) const {
        return size_t(addr.sin_addr.s_addr) + addr.sin_port;
    }
};

enum strategy_t {STRATEGY_NOT_SET = 0, STRATEGY_DIRECT, STRATEGY_CMD, STRATEGY_FILE};

class ConfigFile {
private:
    typedef map<struct sockaddr_in, struct sockaddr_in, cmp_addr_less> conv_map_t;
    conv_map_t addr_map;  // use map because need to preserve orders
    conv_map_t cidr_map;  // use map because need to iterate over
    conv_map_t rev_addr_map;
    conv_map_t rev_cidr_map;
    unordered_map<struct sockaddr_in, string, hash_addr, cmp_addr_equal> addr_to_node;
    unordered_map<string, struct sockaddr_in> node_to_addr;
    strategy_t strategy = STRATEGY_NOT_SET;
    string cmd_file;
    int port = -1;
    const unordered_map<string, strategy_t> allowed_strategies = {
            {"direct", STRATEGY_DIRECT},
            {"cmd",    STRATEGY_CMD},
            {"file",   STRATEGY_FILE}
    };
//    const strategy_t default_strategy = STRATEGY_DIRECT;
    const strategy_t default_strategy = STRATEGY_NOT_SET;
    static struct sockaddr_in convert_addr(const string &addr, char delim=':');
    struct sockaddr_in get_converted_addr(const struct sockaddr_in &to_conv, const conv_map_t &a, const conv_map_t &c) const;
    set<short> port_to_deliver_first_msg;
public:
    void load(const string &file);
    ConfigFile(const string &file = "") {
        load(file);
    }
    struct sockaddr_in get_masquerade_addr(const struct sockaddr_in &origin) const;
    struct sockaddr_in get_origin_addr(const struct sockaddr_in &masq) const;
    strategy_t get_strategy() const {
        return strategy;
    }
    const string &get_cmd_file() const {
        return cmd_file;
    }
    string get_node_name(const struct sockaddr_in &addr, bool to_string_if_null=false) const;
    string get_node_name_with_addr(const struct sockaddr_in &addr) const;
    struct sockaddr_in get_node_addr(const string &name_port) const;
    struct sockaddr_in router_addr{};
    bool is_router_addr(const struct sockaddr_in &addr);
    void set_port(int p);
    int get_port() const;
    vector<string> get_nodes() const;
    void init_port_to_deliver_first_msg(const string &s);
    bool check_port_to_deliver_first_msg(short p);
};

#endif //TPROXY_CONFIGFILE_H
