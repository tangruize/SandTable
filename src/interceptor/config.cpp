//
// Created by tangruize on 22-5-14.
//

extern "C" {
#include "common.h"
#include "config.h"
#include "router.h"
#include "fcntl.h"
#include "state_collector.h"
#include "mysyscall.h"
}

#include <map>
#include <set>
#include <vector>
#include <string>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <cstring>
#include <thread>

#include <unistd.h>
#include <sys/socket.h>

using namespace std;

// comparison func of struct sockaddr_in for map/set
struct cmp_addr {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const {
        if (a.sin_addr.s_addr == b.sin_addr.s_addr)
            return a.sin_port < b.sin_port;
        return a.sin_addr.s_addr < b.sin_addr.s_addr;
    }
};
struct cmp_addr_no_port {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const {
        return a.sin_addr.s_addr < b.sin_addr.s_addr;
    }
};

struct addr_info {
    struct sockaddr_in addr;
    bool passive;  // connection is established by accept/accept4
};

struct cmp_addr_info {
    struct cmp_addr cmp_addr_func;
    struct cmp_addr_no_port cmp_addr_no_port_func;
    bool operator()(const struct addr_info& a, const struct addr_info& b) const {
        if (!option_multi_ports) {
            return cmp_addr_no_port_func(a.addr, b.addr);
        }
        else if (a.passive == b.passive) {
            return cmp_addr_func(a.addr, b.addr);
        }
        else {
            return a.passive < b.passive;
        }
    }
};

// fd that addr is concerned
static map<int, struct addr_info> fd_map;
static map<struct addr_info, int, cmp_addr_info> addr_map;
// concerned addrs import from config file
static set<struct sockaddr_in, cmp_addr> concern_addr_set;
static set<unsigned short> subnet_suffix;
static map<string, struct sockaddr_in> node_to_addr;
static map<struct sockaddr_in, struct sockaddr_in, cmp_addr_no_port> addr_conv;


static string merge_tokens_from(const vector<string> &tokens, unsigned start) {
    assert(start < tokens.size());
    string res = tokens[start];
    for (unsigned i = start + 1; i < tokens.size(); ++i) {
        res += " " + tokens[i];
    }
    return res;
}

static string append_node_id(const string &str) {
    if (node_id)
        return str + "." + node_id;
    return str;
}

extern "C" {

const char* node_id = NULL;
int log_stdout_fd = -1;
int log_stderr_fd = -1;
struct collector_popen collector_childinfo;
int option_multi_ports = 0;
int option_state_no_clear = 0;
int option_state_no_fail_empty = 0;
int option_udp = 0;

struct sockaddr_in convert_mapped_ipv6_to_ipv4(const struct sockaddr_in6 *addr) {
    union {
        uint16_t u16[8];
        uint32_t u32[4];
        uint64_t u64[2];
        in6_addr ipv6_addr;
    } u;
    u.ipv6_addr = addr->sin6_addr;
    struct sockaddr_in ret{};
    ret.sin_port = addr->sin6_port;
    if (u.u64[0] == 0 && u.u16[4] == 0 && u.u16[5] == 0xffff) {
        ret.sin_addr.s_addr = u.u32[3];
    }
    return ret;
}

// check addr is concerned, so that we can trace later actions of the fd
int check_addr_is_concerned(const struct sockaddr_in *addr) {
    struct sockaddr_in to_search{}, addr_buf;
    if (addr->sin_family == AF_INET) {
        to_search.sin_addr.s_addr = addr->sin_addr.s_addr;
        to_search.sin_port = addr->sin_port;
    } else if (addr->sin_family == AF_INET6) {
        addr_buf = convert_mapped_ipv6_to_ipv4((const struct sockaddr_in6 *)addr);
        to_search = addr_buf;
        addr = &addr_buf;
    }
    if (concern_addr_set.find(to_search) != concern_addr_set.end())
        return 1;
    for (auto i: subnet_suffix) {
        to_search.sin_port = i;
        unsigned mask = unsigned(-1) << (32 - i);
        to_search.sin_addr.s_addr = htonl(ntohl(addr->sin_addr.s_addr) & mask);
        if (concern_addr_set.find(to_search) != concern_addr_set.end())
            return 1;
    }
    return 0;
}

int check_addr_is_concerned_with_len(const struct sockaddr_in *addr, socklen_t addrlen) {
    if (addrlen >= sizeof(struct sockaddr_in))
        return check_addr_is_concerned(addr);
    return 0;
}

// add fd to concerned fd list
// (Fixed by option multi_ports) bug caution: cmp func in addr_map compares IP only (no port), an existing value might be erased!
void add_concerned_fd(int fd, const struct sockaddr_in *addr, int is_accept) {
    struct sockaddr_in a{};
    if (addr->sin_family == AF_INET)
        a = *addr;
    else
        a = convert_mapped_ipv6_to_ipv4((const sockaddr_in6 *)addr);
    if (option_multi_ports) {
        a.sin_port = addr->sin_port;
    }
    auto ai = (struct addr_info){a, (bool)is_accept};
    auto it = addr_map.find(ai);
    if (it != addr_map.end()) {
        print_info("DEBUG: addr_map {%s: %d} is overwritten to %d\n", ADDR_TO_STR(&a), it->second, fd);
    }
    fd_map[fd] = ai;
    addr_map[ai] = fd;
//    print_info("DEBUG: add_concerned_fd: fd: %d, addr: %s\n", fd, ADDR_TO_STR2(addr));
}

// remove fd (close())
void rm_concerned_fd(int fd) {
    auto it = fd_map.find(fd);
    if (it != fd_map.end()) {
        auto it2 = addr_map.find(it->second);
        if (it2 != addr_map.end() && it2->second == it->first)
            addr_map.erase(it->second);
        fd_map.erase(it);
    }
}

// check fd is concerned to do some actions (send()/sendto())
struct sockaddr_in check_fd_is_concerned_with_addr(int fd) {
    const auto it = fd_map.find(fd);
    if (it != fd_map.end())
        return it->second.addr;
    struct sockaddr_in empty{};
    return empty;
}

int check_fd_is_concerned(int fd) {
    return fd_map.find(fd) != fd_map.end();
}

static void debug_show_addr_map(const struct sockaddr_in &addr) {
    for (auto &i: addr_map) {
        print_info("DEBUG: addr_map: key: %s, is_passive: %d, value: %d\n", ADDR_TO_STR2(&i.first.addr), i.first.passive, i.second);
    }
    print_info("DEBUG: addr to lookup: %s\n", ADDR_TO_STR2(&addr));
}

int get_addr_fd(struct sockaddr_in addr) {
    auto it = addr_map.find({addr, false});
    if (it != addr_map.end()) {
        if (it->second == -1) {
            debug_show_addr_map(addr);
        }
        return it->second;
    }
    debug_show_addr_map(addr);
    return -1;
}

int get_tokens(const char *line, void *ts) {
    vector<string> &tokens = *reinterpret_cast<vector<string> *>(ts);
    string token;
    istringstream ss(line);
    while (getline(ss, token, ' ')) {
        if (token.empty())
            continue;
        if (token[0] == '#')
            break;
        tokens.push_back(token);
    }
    if (tokens.empty())
        return false;
    return true;
}

struct sockaddr_in get_node_addr(const char *node) {
    string n(node);
    struct sockaddr_in addr{};
    addr.sin_port = -1;
    auto it = node_to_addr.find(n);
    if (it != node_to_addr.end()) {
        addr = it->second;
    }
    // assume netmask is 24.
    // caution network endian.
    in_addr_t last_field = ntohl((htonl(addr.sin_addr.s_addr) & 0xff));
    addr.sin_addr.s_addr = ntohl(htonl(addr.sin_addr.s_addr) & 0xffffff00);
    auto it2 = addr_conv.find(addr);
    if (it2 != addr_conv.end()) {
        addr.sin_addr = it2->second.sin_addr;
    }
    else {
        print_info("DEBUG: addr %s\n", ADDR_TO_STR(&addr));
        for (auto &i: addr_conv) {
            print_info("DEBUG: addr_conv %s %s\n", ADDR_TO_STR(&i.first), ADDR_TO_STR2(&i.second));
        }
    }
    addr.sin_addr.s_addr |= last_field;
    return addr;
}

static int init_log_fd(int fd, const string &path) {
    int *log_fd = NULL;
    if (fd == STDOUT_FILENO) {
        log_fd = &log_stdout_fd;
    } else if (fd == STDERR_FILENO) {
        log_fd = &log_stderr_fd;
    } else {
        print_info_no_prompt("  - WARN: invalid fd (%d) to log for \"%s\"\n", fd, path.c_str());
        return false;
    }
    *log_fd = _syscall_(SYS_open, path.c_str(), O_WRONLY | O_APPEND | O_CREAT, 0644);  // O_CLOEXEC?
    if (*log_fd == -1) {
         print_info_no_prompt("  - WARN: failed to open \"%s\": %s\n", path.c_str(), strerror(errno));
         return false;
    }
    return true;
}

static int init_collector(const string &cmdline) {
    pid_t p;
    int pipe_stdin[2], pipe_stdout[2];
    struct collector_popen *childinfo = &collector_childinfo;

    if (_syscall_(SYS_pipe, pipe_stdin) == -1 || _syscall_(SYS_pipe, pipe_stdout) == -1) {
        print_info_no_prompt("  - WARN: failed to init collector pipes: %s", strerror(errno));
        goto failed;
    }

    p = _syscall_(SYS_fork);
    if (p < 0) {
        print_info_no_prompt("  - WARN: failed to fork: %s", strerror(errno));
        goto failed;
    }
    else if(p == 0) { // child
        unsetenv("LD_PRELOAD");  // not to preload for child
        _syscall_(SYS_close, pipe_stdin[1]);
        _syscall_(SYS_dup2, pipe_stdin[0], 0);
        _syscall_(SYS_close, pipe_stdout[0]);
        _syscall_(SYS_dup2, pipe_stdout[1], 1);
        _syscall_(SYS_dup2, MY_STDERR_FILENO, STDERR_FILENO);
        _syscall_(SYS_close, MY_STDERR_FILENO);
        execl("/bin/sh", "sh", "-c", cmdline.c_str(), NULL);
        print_info_no_prompt("  - WARN: failed to execl: %s", strerror(errno));
        _syscall_(SYS_exit, EXIT_FAILURE);
    }
    childinfo->child_pid = p;
    childinfo->to_child = pipe_stdin[1];
    childinfo->from_child = pipe_stdout[0];
    _syscall_(SYS_close, pipe_stdin[0]);
    _syscall_(SYS_close, pipe_stdout[1]);
    std::thread(state_collect_thread).detach();
    return true;
failed:
    _syscall_(SYS_close, pipe_stdin[0]);
    _syscall_(SYS_close, pipe_stdin[1]);
    _syscall_(SYS_close, pipe_stdout[0]);
    _syscall_(SYS_close, pipe_stdout[1]);
    return false;
}

// read config file (get filename from ENV CONFIG_FILE_ENV), store concerned addr
void init_config_file() {
    static bool is_inited = false;  // to avoid initialising twice
    const char *config_file = getenv(CONFIG_FILE_ENV);
    node_id = getenv(NODE_NO_ENV);
    if (is_inited || !config_file || strlen(config_file) == 0)
        return;

    print_info("Read config file \"%s\"\n", config_file);
    is_inited = true;
    ifstream f(config_file);
    if (!f.is_open()) {
        print_info_no_prompt("  - WARN: fail to open file");
        return;
    }

    string line, token;
    int line_no = 0;
    static set<string> ignore_cmd = { "strategy" };
    while (getline(f, line)) {
        line_no++;
        vector<string> tokens;
        if (!get_tokens(line.c_str(), &tokens) || ignore_cmd.count(tokens[0])) {
            continue;
        }

        bool ok = false;
        if (tokens.size() >= 2 && (tokens[0] == "map-addr" || tokens[0] == "map-cidr")) {
            char delim = (tokens[0] == "map-addr") ? ':' : '/';
            struct sockaddr_in origin = convert_addr(tokens[1].c_str(), delim);
            struct sockaddr_in masquerade = convert_addr(tokens[2].c_str(), delim);
            if (origin.sin_port) {
                if (delim == ':') {
                    print_info_no_prompt("  - %s " ADDR_FMT " " ADDR_FMT"\n", tokens[0].c_str(), ADDR_TO_STR(&origin), ADDR_TO_STR2(&masquerade));
                }
                else {
                    print_info_no_prompt("  - %s " CIDR_FMT " " CIDR_FMT"\n", tokens[0].c_str(), CIDR_TO_STR(&origin), CIDR_TO_STR2(&masquerade));
                    subnet_suffix.insert(origin.sin_port);
                }
                addr_conv[masquerade] = origin;
                concern_addr_set.insert(origin);
                ok = true;
            }
        } else if (tokens.size() >= 2 && tokens[0] == "router") {
            if (connect_router(tokens[1].c_str()))
                ok = true;
            else
                ::abort();
        } else if (tokens.size() == 3 && tokens[0] == "node") {
            bool hasport = tokens[2].find(':') != std::string::npos;
            struct sockaddr_in addr = convert_addr((tokens[2] + (hasport ? "" : ":0")).c_str(), ':');
            if (addr.sin_addr.s_addr) {
                ok = true;
                string node = tokens[1];
                addr.sin_port = 0;
                node_to_addr[node] = addr;
                print_info_no_prompt("  - %s %s " ADDR_FMT "\n", tokens[0].c_str(), tokens[1].c_str(), ADDR_TO_STR(&addr));
            }
        } else if (tokens.size() >= 3 && tokens[0] == "log") {
            string outfile = append_node_id(merge_tokens_from(tokens, 2));
            ok = init_log_fd(tokens[1] == "stdout" ? STDOUT_FILENO : STDERR_FILENO, outfile);
            print_info_no_prompt("  - %s %s %s\n", tokens[0].c_str(), tokens[1].c_str(), outfile.c_str());
        } else if (tokens.size() >= 2 && tokens[0] == "collector") {
            string cmd = merge_tokens_from(tokens, 1);
            ok = init_collector(cmd);
            print_info_no_prompt("  - %s %s\n", tokens[0].c_str(), cmd.c_str());
        } else if (tokens.size() >= 2 && tokens[0] == "option") {
            if (tokens[1] == "multi_ports") {
                option_multi_ports = 1;
                ok = true;
            } else if (tokens[1] == "state_no_fail_empty") {
                option_state_no_fail_empty = 1;
                ok = true;
            } else if (tokens[1] == "state_no_clear") {
                option_state_no_clear = 1;
                ok = true;
            } else if (tokens[1] == "udp") {
                option_udp = 1;
                ok = true;
                reg_func_dict[SYS_sendto].state = (STATE_DISABLED | (reg_func_dict[SYS_sendto].state & STATE_LIBRARY));
            }
            else {
                continue;
            }
            print_info_no_prompt("  - %s\n", line.c_str());
        }
        if (!ok)
            print_info_no_prompt("  - WARN: invalid cmd at line %d: %s\n", line_no, line.c_str());
    }
    f.close();
}

// convert ADDR (format: xxx.xxx.xxx.xxx:port) and CIDR (format: xxx.xxx.xxx.xxx/netmask)
struct sockaddr_in convert_addr(const char *addr, char delim) {
    struct sockaddr_in res{};
    stringstream ss(addr);
    string ip, port;
    getline(ss, ip, delim);
    getline(ss, port, delim);
    inet_aton(ip.c_str(), &res.sin_addr);
    if (delim == ':') {
        res.sin_port = htons(stoi(port));
    }
    else {
        res.sin_port = stoi(port);
        unsigned mask = unsigned(-1) << (32 - res.sin_port);
        res.sin_addr.s_addr = htonl(ntohl(res.sin_addr.s_addr) & mask);
    }
    return res;
}

const char *addr_to_str(const struct sockaddr_in *addr, const char *delim, int which) {
    char addr_buf[INET6_ADDRSTRLEN+8] = "NULL";
    in_port_t port;
    if (addr->sin_family == AF_INET6) {
        inet_ntop(AF_INET6, &((const struct sockaddr_in6*)addr)->sin6_addr, addr_buf, INET6_ADDRSTRLEN);
        port = ((const struct sockaddr_in6*)addr)->sin6_port;
    } else {
        inet_ntop(AF_INET, &addr->sin_addr, addr_buf, INET6_ADDRSTRLEN);
        port = addr->sin_port;
    }
    if (delim[0] == ':')
        port = ntohs(port);
    strcat(addr_buf, (delim + to_string(port)).c_str());
    return restrict_str_internal(which, addr_buf);
}

} // extern "C"
