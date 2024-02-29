//
// Created by fedora on 6/5/22.
//


#include <string>
#include <thread>
#include <vector>
#include <map>

using namespace std;

extern "C" {
#include "common.h"
#include "config.h"
#include "router.h"
#include "mysendto.h"
#include "timing.h"
#include "state_collector.h"
#include "mysyscall.h"
#include <unistd.h>
#include <sys/ioctl.h>

static int router_sockfd = -1;
static string ack_data;

static string tokens_to_string(const vector<string> &tokens) {
    string s = tokens[0];
    for (unsigned i = 1; i < tokens.size(); i++)
        s += " " + tokens[i];
    return s;
}

static bool check_warn_args(unsigned required, const vector<string> &tokens) {
    if (tokens.size() < required) {
        print_info_no_prompt("  - WARN: command requires %d args, but given %d\n", required, tokens.size());
        return false;
    }
    return true;
}

static int inc_time_ns(const vector<string> &tokens) {
    if (!check_warn_args(2, tokens))
        return 1;
    long ns = stol(tokens[1]);
    set_time_increment(ns);
    return 0;
}

static int inc_time_us(const vector<string> &tokens) {
    if (!check_warn_args(2, tokens))
        return 1;
    long ns = stol(tokens[1]) * 1000;
    set_time_increment(ns);
    return 0;
}

static int inc_time_ms(const vector<string> &tokens) {
    if (!check_warn_args(2, tokens))
        return 1;
    long ns = stol(tokens[1]) * 1000000;
    set_time_increment(ns);
    return 0;
}

static void ack_cmd(int fd, int status) {
    string status_str;
    if (status == 0) {
        if (!ack_data.empty())
            status_str = std::move(ack_data);
        else
            status_str = "True";
    } else {
        status_str = "False " + to_string(status);
    }
    string send_buf;
    send_buf.resize(4);
    *(uint32_t *)&send_buf.front() = htonl(status_str.length());
    send_buf += status_str;
    ssize_t ret = _syscall_(SYS_write, fd, send_buf.c_str(), send_buf.length());
    if (ret != (ssize_t)send_buf.length()) {
        print_info("WARN: ack controller cmd failed, return value: %ld\n", ret);
    }
}

static int check_has_recv_queue(const vector<string> &tokens) {
    if (!check_warn_args(2, tokens))
        return 1;
    struct sockaddr_in addr{};
    if (tokens[1].find(':') == string::npos) {
        addr = get_node_addr(tokens[1].c_str());
    } else {
        addr = convert_addr(tokens[1].c_str(), ':');
    }
    if (short(addr.sin_port) == -1) {
        print_info("WARN: check recv queue cannot find addr: \"%s\"\n", tokens[1].c_str());
        return 1;
    }
    int fd = get_addr_fd(addr);
    if (fd == -1) {
        print_info("WARN: check recv queue \"%s\": fd is -1\n", ADDR_TO_STR(&addr));
        return 1;
    }
    int count;
    ioctl(fd, FIONREAD, &count);
    print_info("Check recv queue: %d\n", count);
    if (count > 0)
        return 0;
    return 2;
}

static int state_collect(const vector<string> &tokens) {
    UNUSED(tokens);
    bool ok = collect_states();
    if (ok)
        return 0;
    return 1;
}

static int state_get(const vector<string> &tokens) {
    if (!check_warn_args(2, tokens))
        return 1;
    size_t i;
    int status = 2;
    for (i = 1; i < tokens.size(); i++) {
        char *var = get_state(tokens[i].c_str());
        if (i > 1)
            ack_data += '\n';
        if (var) {
            status = 0;
            ack_data += var;
        } else /*if (option_state_no_fail_empty)*/ {
            status = 0;
            ack_data += "(empty)";
        }
        free(var);
    }
    return status;
}

static int print_comments(const vector<string> &tokens) {
//    if (!tokens.empty()) {
//        print_info("%s", tokens[0].c_str());
//    }
//    for (size_t i = 1; i < tokens.size(); i++) {
//        print_info_no_prompt(" %s", tokens[i].c_str());
//    }
//    print_info_no_prompt("\n");
    UNUSED(tokens);
    return 0;
}

static void do_router_cmd() {
    CLOCK_START_RECORD2;
#define CMD_BUFFER_SIZE 1024
    char cmd_buffer[CMD_BUFFER_SIZE];
    bzero(cmd_buffer, CMD_BUFFER_SIZE);
    ssize_t size;
    map<string, int (*)(const vector<string> &)> cmd_map = {
            {"inc_time_ns", inc_time_ns},
            {"inc_time_us", inc_time_us},
            {"inc_time_ms", inc_time_ms},
            {"check_has_recv_queue", check_has_recv_queue},
            {"state_collect", state_collect},
            {"state_get", state_get},
            {"print", print_comments}
    };
    struct hacked_sendto_header *header = (hacked_sendto_header *) (cmd_buffer);
    CLOCK_END_RECORD2;
    
    while ((size = _syscall_(SYS_recvfrom, router_sockfd, cmd_buffer, sizeof(hacked_sendto_header), MSG_WAITALL, 0, 0)) > 0) {
//        print_info("validation: %x\n", ntohl(header->validation));
        CLOCK_START_RECORD;
        assert(ntohl(header->validation) == VALIDATE_STR);
        size = ntohl(header->size);
        if (size >= CMD_BUFFER_SIZE) {
            print_info_stderr("Error: cmd size too large: %d\n", size);
            size = -1;
            errno = EINVAL;
            break;
        }
        size = _syscall_(SYS_recvfrom, router_sockfd, cmd_buffer, size, MSG_WAITALL, 0, 0);
        if (size <= 0) {
            break;
        }
        cmd_buffer[size] = 0;
        vector<string> tokens;
        int32_t lineno = ntohl(*(int32_t *)cmd_buffer);
        if (!get_tokens(cmd_buffer + 4, &tokens)) {
            continue;
        }
        print_info("Router cmd (line %d): %s\n", lineno, tokens_to_string(tokens).c_str());
        auto it = cmd_map.find(tokens[0]);
        int status = 1;
        if (it == cmd_map.end()) {
            print_info_no_prompt("  - WARN: no such command\n");
        } else {
            ack_data.clear();
            status = it->second(tokens);
        }
        ack_cmd(router_sockfd, status);
        CLOCK_END_RECORD;
    }
    if (size == 0) {
        _syscall_(SYS_close, router_sockfd);
        // disable all _syscall_ interceptions to prevent other thread calling destructed global variables (as possible)
        for (int i = 0; i < NR_REG_FUNC_DICT; i++) {
            reg_func_dict[i].state = (STATE_DISABLED | (reg_func_dict[i].state & STATE_LIBRARY));
        }
        print_info("Router socket is closed, exiting ..\n");
        // currently, we set on_exit functions, so we use exit instead of _exit() _syscall_.
        // this can lead to process corruption in race conditions (if an intercepted _syscall_ using destructed global variables)
        //exit(0);
        _exit(0);
    } else {
        print_info("Router socket recv failed: %s\n", strerror(errno));
        _syscall_(SYS_close, router_sockfd);
    }
}

int connect_router(const char *addr) {
    static bool is_connected = false;
    if (is_connected) {
        print_info_no_prompt("    - WARN: router already connected\n");
        return false;
    }
    struct sockaddr_in router = convert_addr(addr, ':');
    if (!router.sin_port) {
        return false;
    }
    router.sin_family = AF_INET;
    print_info_no_prompt("  - router "
    ADDR_FMT
    "\n", ADDR_TO_STR(&router));
    router_sockfd = (int)_syscall_(SYS_socket, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (router_sockfd == -1) {
        print_info_no_prompt("    - WARN: socket: %s\n", strerror(errno));
        return false;
    }
    int retry_times = 3;
    while (_syscall_(SYS_connect, router_sockfd, (struct sockaddr *) &router, sizeof(router)) != 0) {
        sleep(1); // retry
        retry_times--;
        if (!retry_times) {
            print_info_no_prompt("    - WARN: connect: %s\n", strerror(errno));
            return false;
        }
    }
    if (_syscall_(SYS_dup2, router_sockfd, ROUTER_FD) != -1) {
        _syscall_(SYS_close, router_sockfd);
        router_sockfd = ROUTER_FD;
    }
    std::thread(do_router_cmd).detach();
    is_connected = true;
    return true;
}
} // extern "C"