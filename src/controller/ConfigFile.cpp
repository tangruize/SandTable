//
// Created by tangruize on 22-5-10.
//

#include "ConfigFile.h"
#include "common.h"
#include <set>
#include <algorithm>

//DECLARE_bool(deliver_first_msg);
//DECLARE_bool(multi_ports);
//DECLARE_bool(half_duplex_connection);
DECLARE_bool(verbose);
DECLARE_bool(detail);
DECLARE_int32(port);
DECLARE_string(tmpdir);
DECLARE_int32(sshno);
DECLARE_bool(deliver_first_msg);
DECLARE_bool(no_exit);
DECLARE_int32(max_loop_times);
DECLARE_bool(no_abrt);
DECLARE_bool(half_duplex_connection);
DECLARE_bool(delay_connect);
DECLARE_int32(block_connect_timeout);
DECLARE_int32(merge_small_msg);
DECLARE_bool(dump_msg);
DECLARE_bool(no_exec_ack);
DECLARE_double(add_ssh_timeout);
DECLARE_bool(multi_ports);
DECLARE_string(deliver_first_msg_ports);
DECLARE_bool(abort_failed_init);
DECLARE_bool(state_no_fail_empty);
DECLARE_bool(partition_keep_msgs);
DECLARE_bool(allow_msg_unordered);
DECLARE_bool(udp);

void ConfigFile::load(const string &file) {
    if (file.empty())
        return;
    cerr_verbose << "Read config file \"" << file << "\"" << endl;
    ifstream f;
    f.exceptions(std::ifstream::failbit | std::ifstream::badbit);  // throw exception if failed to open file for read
    f.open(file);
    f.exceptions(std::ifstream::badbit);  // disable failbit throwing exceptions (such as EOF)
    string line, token;
    set<string> ignore_cmd = {"log", "collector"};
    int line_no = 0;
    while (getline(f, line)) {
        line_no++;
        vector<string> tokens;
        istringstream ss(line);
        while (getline(ss, token, ' ')) {
            if (token.empty())
                continue;
            if (token[0] == '#')
                break;
            tokens.push_back(token);
        }
        if (tokens.empty())
            continue;
        if (ignore_cmd.count(tokens[0]))
            continue;

        bool ok = false;
        if (tokens.size() == 3 && (tokens[0] == "map-addr" || tokens[0] == "map-cidr")) {
            char delim = ((tokens[0] == "map-addr") ? ':' : '/');
            struct sockaddr_in origin = convert_addr(tokens[1], delim);
            struct sockaddr_in masquerade = convert_addr(tokens[2], delim);
            if (origin.sin_port && masquerade.sin_port) {
                ok = true;
                auto &which = ((tokens[0] == "map-addr") ? addr_map : cidr_map);
                auto &rev = ((tokens[0] == "map-addr") ? rev_addr_map : rev_cidr_map);
                which[origin] = masquerade;
                rev[masquerade] = origin;
                cerr_verbose_cont << "  - " << tokens[0] << ' ' << addr_to_string_delim(origin, delim)
                                  << ' ' << addr_to_string_delim(masquerade, delim) << endl;
            }
        } else if (tokens.size() == 3 && tokens[0] == "node") {
            bool hasport = tokens[2].find(':') != std::string::npos;
            struct sockaddr_in addr = convert_addr(tokens[2] + (hasport ? "" : ":0"), ':');
            addr.sin_port = 0;
            if (addr.sin_addr.s_addr) {
                ok = true;
                string node = tokens[1];
                addr_to_node[addr] = node;
                node_to_addr[node] = addr;
                cerr_verbose_cont << "  - " << tokens[0] << ' ' << node << ' ' << inet_ntoa((addr).sin_addr) << endl;
            }
        } else if (tokens.size() >= 2 && tokens[0] == "strategy") {
            if (strategy != STRATEGY_NOT_SET) {
                cerr_verbose_cont << "  - WARN: strategy should not appear twice at line " << line_no << ": " << line << endl;
                continue;
            }
            auto it = allowed_strategies.find(tokens[1]);
            if (it != allowed_strategies.end()) {
                if (tokens.size() > 2 && it->second != STRATEGY_FILE)
                    ok = false;
                else {
                    ok = true;
                    strategy = it->second;
                    if (strategy == STRATEGY_FILE) {
                        cmd_file = std::move(tokens[2]);
                    }
                    cerr_verbose_cont << "  - " << tokens[0] << ' ' << tokens[1] << (cmd_file.empty() ? "" : " " + cmd_file) << endl;
                }
            }
        } else if (tokens.size() >= 2 && tokens[0] == "router") {
            struct sockaddr_in router = convert_addr(tokens[1], ':');
            if (router.sin_port) {
                if (port == -1)  // cmd line has higher priority than config file
                    set_port(ntohs(router.sin_port));
                router_addr = router;
                ok = true;
                router.sin_port = 0;
                addr_to_node[router] = "router";
                node_to_addr["router"] = router;
                cerr_verbose_cont << "  - " << tokens[0] << ' ' << addr_to_string(router) << endl;
            }
        } else if (tokens.size() >= 2 && tokens[0] == "option") {
            if (tokens[1] == "verbose") {
                FLAGS_verbose = true;
                ok = true;
            } else if (tokens[1] == "detail") {
                FLAGS_verbose = true;
                FLAGS_detail = true;
                ok = true;
            } else if (tokens[1] == "port") {
                if (port == -1) {
                    set_port(stoi(tokens[2]));
                } else {
                    continue;
                }
                ok = true;
            } else if (tokens[1] == "tmpdir") {
                if (FLAGS_tmpdir.empty()) {  // do not override cmd line option
                    string env_name, path_to_set;
                    if (tokens.size() <= 2) {
                        env_name = "TMPDIR";
                    } else {
                        if (tokens[2][0] == '$') {
                            env_name = tokens[2].substr(1);
                        } else {
                            path_to_set = tokens[2];
                        }
                    }
                    if (!path_to_set.empty()) {
                        FLAGS_tmpdir = path_to_set;
                        ok = true;
                    } else if (!env_name.empty()) {
                        const char *value = getenv(env_name.c_str());
                        if (value) {
                            FLAGS_tmpdir = value;
                            ok = true;
                        } else {
                            cerr_warning << "Cannot find env \"" << env_name << "\", note that env list is cleared when process is privileged." << endl;
                        }
                    }
                    cerr_verbose_cont << "  - option tmpdir " << FLAGS_tmpdir << endl;
                    continue;
                } else {
                    continue;
                }
            } else if (tokens[1] == "sshno") {
                if (FLAGS_sshno == -1) {
                    continue;
                }
                FLAGS_sshno = stoi(tokens[2]);
                ok = true;
            } else if (tokens[1] == "deliver_first_msg") {
                FLAGS_deliver_first_msg = true;
                ok = true;
            } else if (tokens[1] == "no_exit") {
                FLAGS_no_exit = true;
                ok = true;
            } else if (tokens[1] == "max_loop_times") {
                FLAGS_max_loop_times = stoi(tokens[2]);
                ok = true;
            } else if (tokens[1] == "no_abrt") {
                FLAGS_no_abrt = true;
                ok = true;
            } else if (tokens[1] == "half_duplex_connection") {
                FLAGS_half_duplex_connection = true;
                ok = true;
            } else if (tokens[1] == "delay_connect") {
                FLAGS_delay_connect = true;
                ok = true;
            } else if (tokens[1] == "block_connect_timeout") {
                if (FLAGS_block_connect_timeout != -1) {
                    continue;
                }
                FLAGS_block_connect_timeout = stoi(tokens[2]);
                ok = true;
            } else if (tokens[1] == "merge_small_msg") {
                if (FLAGS_merge_small_msg != -1) {
                    continue;
                }
                FLAGS_merge_small_msg = stoi(tokens[2]);
                ok = true;
            } else if (tokens[1] == "dump_msg") {
                FLAGS_dump_msg = true;
                ok = true;
            } else if (tokens[1] == "no_exec_ack") {
                FLAGS_no_exec_ack = true;
                ok = true;
            } else if (tokens[1] == "add_ssh_timeout") {
                if (FLAGS_add_ssh_timeout != -1)
                    continue;
                FLAGS_add_ssh_timeout = stoi(tokens[2]);
                ok = true;
            } else if (tokens[1] == "multi_ports") {
                FLAGS_half_duplex_connection = true;
                FLAGS_multi_ports = true;
                ok = true;
            } else if (tokens[1] == "deliver_first_msg_ports") {
                if (!FLAGS_deliver_first_msg_ports.empty()) {
                    continue;
                }
                init_port_to_deliver_first_msg(tokens[2]);
                ok = true;
            } else if (tokens[1] == "abort_failed_init") {
                FLAGS_abort_failed_init = true;
                ok = true;
            } else if (tokens[1] == "state_no_fail_empty") {
                FLAGS_state_no_fail_empty = true;
                ok = true;
            } else if (tokens[1] == "state_no_clear") {
                // nothing to do here
                ok = true;
            } else if (tokens[1] == "partition_keep_msgs") {
                FLAGS_partition_keep_msgs = true;
                ok = true;
            } else if (tokens[1] == "allow_msg_unordered") {
                FLAGS_allow_msg_unordered = true;
                ok = true;
            } else if (tokens[1] == "udp") {
                FLAGS_udp = true;
                ok = true;
            }
            if (ok) {
                cerr_verbose_cont << "  - " << line << endl;
            }
        }
        if (!ok) {
            cerr_verbose_cont << "  - WARN: invalid cmd at line " << line_no << ": " << line << endl;
        }
    }
    f.close();
    if (strategy == STRATEGY_NOT_SET) {
        strategy = default_strategy;
        cerr_verbose << "Strategy not set, use simple redirect" << endl;
    }
}

struct sockaddr_in ConfigFile::convert_addr(const string &addr, char delim) {
    struct sockaddr_in res{};
    stringstream ss(addr);
    string ip, port;
    getline(ss, ip, delim);
    getline(ss, port, delim);
    res.sin_family = AF_INET;
    inet_aton(ip.c_str(), &res.sin_addr);
    if (delim == ':')
        res.sin_port = htons(stoi(port));
    else if (delim == '/')
        res.sin_port = stoi(port);
    return res;
}

static inline in_addr_t addr_mask(const sockaddr_in &addr, unsigned mask) {
    return ntohl(addr.sin_addr.s_addr) & mask;
}

struct sockaddr_in ConfigFile::get_masquerade_addr(const sockaddr_in &origin) const {
    return get_converted_addr(origin, addr_map, cidr_map);
}

string ConfigFile::get_node_name(const struct sockaddr_in &addr, bool to_string_if_null) const {
    struct sockaddr_in a = addr;
    a.sin_port = 0;
    auto it = addr_to_node.find(a);
    if (it != addr_to_node.end())
        return it->second;
    if (to_string_if_null)
        return addr_to_string(addr);
    return ""; // failed to look up
}

struct sockaddr_in ConfigFile::get_node_addr(const string &name_port) const {
    auto pos = name_port.find(':');
    string name, addr_port;
    short addr_port_int = 0;
    if (pos != string::npos) {
        name = name_port.substr(0, pos);
        addr_port = name_port.substr(pos+1);
        try {
            addr_port_int = (short)htons(std::stoi(addr_port));
        } catch (const std::exception& e) {
            cerr_warning << "Port in \"" << name_port << "\" is illegal" << endl;
            addr_port_int = 0;
        }
    } else {
        name = name_port;
    }
    auto it = node_to_addr.find(name);
    struct sockaddr_in ret{};
    if (it != node_to_addr.end()) {
        ret = it->second;
        ret.sin_port = addr_port_int;
        return ret;
    }
    if (inet_aton(name.c_str(), &ret.sin_addr)) {
        ret.sin_port = addr_port_int;
        return ret;
    }
    // failed to look up
    ret.sin_port = (in_port_t)-1;
    return ret;
}

string ConfigFile::get_node_name_with_addr(const sockaddr_in &addr) const {
    string node_name = get_node_name(addr);
    if (node_name.empty())
        node_name = addr_to_string(addr);
    else
        node_name += " (" + addr_to_string(addr) + ")";
    return node_name;
}

bool ConfigFile::is_router_addr(const struct sockaddr_in &addr) {
    cmp_addr_equal cmp;
    return cmp(addr, router_addr);
}

struct sockaddr_in ConfigFile::get_converted_addr(const struct sockaddr_in &to_conv, const conv_map_t &a, const conv_map_t &b) const {
    auto it = a.find(to_conv);
    if (it != a.end())
        return it->second;
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

struct sockaddr_in ConfigFile::get_origin_addr(const sockaddr_in &masq) const {
    return get_converted_addr(masq, rev_addr_map, rev_cidr_map);
}

void ConfigFile::set_port(int p) {
    port = p;
}

int ConfigFile::get_port() const {
    return port;
}

vector<string> ConfigFile::get_nodes() const {
    vector<string> result;
    for (auto &k: node_to_addr) {
        if (k.first != "router")
            result.push_back(k.first);
    }
    std::sort(result.begin(), result.end());
    return result;
}

void ConfigFile::init_port_to_deliver_first_msg(const string &s) {
    string token;
    istringstream ss(s);
    while (std::getline(ss, token, ',')) {
        try {
            short value = (short)std::stoi(token);
            port_to_deliver_first_msg.insert(value);
        } catch (const std::exception& e) {
            cerr_warning << "init_port_to_deliver_first_msg: bad number: " << token << endl;
        }
    }
}

bool ConfigFile::check_port_to_deliver_first_msg(short p) {
    if (FLAGS_deliver_first_msg)
        return true;
    return port_to_deliver_first_msg.contains(p);
}
