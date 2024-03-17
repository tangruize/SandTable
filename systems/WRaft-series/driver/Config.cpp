//
// Created by tangruize on 2/14/23.
//

#include <algorithm>
#include "common.h"
#include "Config.h"

bool Config::get_addr(const string &name, sockaddr_in &addr) const {
    auto it = nodes.find(name);
    if (it != nodes.end()) {
        addr = it->addr;
        return true;
    }
    return false;
}

bool Config::get_name(const sockaddr_in &addr, string &name) const {
    Node n(addr);
    if (get_node(n)) {
        name = n.name;
        return true;
    } else {
        return false;
    }
}

bool Config::get_node(Node &n) const {
//    static cmp_addr_equal eq;
//    set<Node>::iterator it;
//    if (n.name.empty()) {
//        auto is_eq = [&n](const Node &i){ return eq(i.addr, n.addr); };
//        it = std::find_if(nodes.begin(), nodes.end(), is_eq);
//    } else {
//        it = nodes.find(n);
//    }
    auto it = find_node(n);
    if (it != nodes.end()) {
        n = *it;
        return true;
    }
    return false;
}

void Config::load(const string &filename) {
    loading = true;
    if (filename.empty()) {
        throw_syserror("Error: filename is empty");
    }
    ifstream f;
    f.exceptions(std::ifstream::failbit | std::ifstream::badbit);  // throw exception if failed to open file for read
    f.open(filename);
    f.exceptions(std::ifstream::badbit);  // disable failbit throwing exceptions (such as EOF)

    string line;
    int line_no = 0;
    cerr_verbose << "Reading config file" << endl;
    while (getline(f, line)) {
        line_no++;
        read(line, line_no);
    }
    f.close();
    set_self_node();
    loading = false;
}

Config::Config(const string &filename) {
    load(filename);
    set_self_node();
}

bool Config::read(const string &line, int line_no) {
    vector<string> tokens = tokenize(line);
    if (tokens.empty() || tokens[0].starts_with('#'))
        return true;

    bool ok = false;
    if (tokens.size() == 3 && tokens[0] == "map-cidr") {
        char delim = '/';
        struct sockaddr_in origin = convert_addr(tokens[1].c_str(), delim);
        struct sockaddr_in masquerade = convert_addr(tokens[2].c_str(), delim);
        if (origin.sin_port && masquerade.sin_port) {
            ok = true;
            cidr_map[origin] = masquerade;
            rev_cidr_map[masquerade] = origin;
            cerr_verbose_cont << "  - " << tokens[0] << ' ' << addr_to_string_delim(origin, delim)
                              << ' ' << addr_to_string_delim(masquerade, delim) << endl;
        }
    }
    else if (tokens.size() == 3 && tokens[0] == "node") {
        struct sockaddr_in addr = get_converted_addr(convert_addr(tokens[2].c_str()), rev_cidr_map);
        if (addr.sin_port == (in_port_t)-1) {
            addr.sin_port = htons(DEFAULT_PORT);
        }
        if (addr.sin_addr.s_addr) {
            ok = true;
            string node = tokens[1];
            nodes.insert(Node(node, addr));
            cerr_verbose << "  - " << tokens[0] << ' ' << node << ' ' << inet_ntoa((addr).sin_addr) << endl;
        }
    } else if (tokens.size() == 2 && tokens[0] == "selfnode") {
        self_name = tokens[1];
        ok = true;
        cerr_verbose << "  - " << tokens[0] << ' ' << self_name << endl;
    } else if (tokens[0] == "get") {
        return getinfo(stringify(tokens, 1));
    }
    if (!ok) {
        if (!loading) {
            cerr_verbose_cont << "  - WARN: invalid cmd";
            if (line_no > 0) {
                cerr_verbose_cont << " at line " << line_no << ": " << line;
            }
            cerr_verbose_cont << endl;
        }
    }
    return ok;
}

bool Config::set_self_node(const string& name) {
    if (name.empty()) {
        if (!FLAGS_name.empty()) {
            self_name = FLAGS_name;
        }
    } else {
        self_name = name;
    }
    if (self_name.empty())
        return false;
    self_node.name = self_name;
    bool ok = get_node(self_node);
    if (!ok) {
        cerr_warning << "Cannot find self node name: " << name << endl;
        self_node.name = "";
    } else {
        cerr_verbose << "Set self node " << self_node.to_string() << endl;
    }
    return ok;
}

Config::Config() {
    set_self_node();
}

bool Config::get_self_node(Node &n) {
    if (!self_node.name.empty()) {
        n = self_node;
        return true;
    } else {
        if (set_self_node()) {
            n = self_node;
            return true;
        } else {
            return false;
        }
    }
//    n.name = self_name;
//    bool ok = get_node(n);
//    if (ok) {
//        self_node = n;
//    }
//    return ok;
}

set<Node> &Config::get_all_nodes() {
    return nodes;
}

Node &Config::get_self_node() {
    if (self_node.name.empty())
        cerr_warning << "self node is not set" << endl;
    return self_node;
}

set<Node>::iterator Config::find_node(const Node &e) const {
    static cmp_addr_equal eq;
    set<Node>::iterator it;
    if (e.name.empty()) {
        auto is_eq = [&e](const Node &i){ return eq(i.addr, e.addr); };
        it = std::find_if(nodes.begin(), nodes.end(), is_eq);
    } else {
        it = nodes.find(e);
    }
    return it;
}

bool Config::getinfo(const string &cmd) {
    auto tokens = tokenize(cmd);
    if (tokens.empty()) {
        return false;
    }
    bool ok;
    if (tokens[0] == "name") {
        Node n(convert_addr(stringify(tokens, 1).c_str()));
        ok = get_node(n);
        if (ok) {
            cout << n.name << endl;
        } else {
            cerr << "failed to find " << n.to_string() << endl;
        }
    } else if (tokens[0] == "addr") {
        Node n(stringify(tokens, 1));
        ok = get_node(n);
        if (ok) {
            cout << addr_to_string(n.addr) << endl;
        }
    } else if (tokens[0] == "selfnode") {
        Node n;
        ok = get_self_node(n);
        if (ok) {
//            cout << n.name << ' ' << addr_to_string(n.addr) << endl;
            cout << n.to_string() << endl;
        }
    }
    return ok;
}

static inline in_addr_t addr_mask(const sockaddr_in &addr, unsigned mask) {
    return ntohl(addr.sin_addr.s_addr) & mask;
}

struct sockaddr_in Config::get_converted_addr(const sockaddr_in &to_conv, const Config::conv_map_t &b) const {
    for (auto &i: b) {
        unsigned mask = unsigned(-1) << (32 - i.first.sin_port);
        if (addr_mask(i.first, mask) == addr_mask(to_conv, mask)) {
            mask = unsigned(-1) << (32 - i.second.sin_port);
            sockaddr_in ret = to_conv;
            ret.sin_addr.s_addr = htonl(addr_mask(i.second, mask) | addr_mask(to_conv, ~mask));
            return ret;
        }
    }
    return to_conv;
}

Config config;
