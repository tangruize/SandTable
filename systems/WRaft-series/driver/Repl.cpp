//
// Created by tangruize on 2/14/23.
//

#include "Repl.h"
#include "common.h"
#include "Raft.h"
#include "Config.h"
#include "Network.h"

#include <readline/history.h>
#include <readline/readline.h>
#include <fcntl.h>

void Repl::readline() {
    char *line;
    while ((line = ::readline(prompt)) != nullptr) {
        string line_str(line);
        bool ok = false, invalid = false;
        if (line_str.empty() || line_str.starts_with("#"))
            continue;
        vector<string> tokens = tokenize(line_str);
        if (tokens.empty())
            continue;
        string ack_data;
        if (tokens[0] == "config") {
            ok = config.read(stringify(tokens, 1));
        } else if (tokens[0] == "get") {
            ack_data = RaftGet(stringify(tokens, 1));
            ok = !ack_data.empty();
            if (ok)
                cerr << ack_data << endl;
        } else if (tokens[0] == "raft") {
            ok = RaftRepl(stringify(tokens, 1));
        } else if (tokens[0] == "net") {
            ok = net->repl(stringify(tokens, 1));
        }
        else {
            cerr_warning << "Invalid command" << endl;
            invalid = true;
        }
        if (!invalid) {
            cerr << (ok ? ok_str : fail_str) << endl;
        }
        if (ack_data.empty())
            ack_data = ok ? "True" : "False";
        ack(ack_data);
        free(line);
    }
}

Repl::Repl() {
    if (!isatty(STDIN_FILENO)) {
        prompt = nullptr;
        ok_str = "[OK]";
        fail_str = "[FAIL]";
    }
    check_interceptor_fd();
}

bool Repl::getinfo(const string &cmd) {
    auto tokens = tokenize(cmd);
    if (tokens.empty()) {
        return false;
    }
    bool ok;
    if (tokens[0] == "name") {
        Node n(convert_addr(stringify(tokens, 1).c_str()));
        ok = config.get_node(n);
        if (ok) {
            cout << n.name << endl;
        } else {
            cerr << "failed to find " << n.to_string() << endl;
        }
    } else if (tokens[0] == "addr") {
        Node n(stringify(tokens, 1));
        ok = config.get_node(n);
        if (ok) {
            cout << addr_to_string(n.addr) << endl;
        }
    } else if (tokens[0] == "selfnode") {
        Node n;
        ok = config.get_self_node(n);
        if (ok) {
//            cout << n.name << ' ' << addr_to_string(n.addr) << endl;
            cout << n.to_string() << endl;
        }
    }
    return ok;
}

void Repl::check_interceptor_fd() {
    if (fcntl(interceptor_fd, F_GETFD) == -1 && errno == EBADF) {
        interceptor_fd = -1;
        cerr_verbose << "Repl ack is disabled" << endl;
    } else {
        cerr_verbose << "Repl ack is enabled" << endl;
    }

}

void Repl::ack(const string &data) const {
    if (interceptor_fd == -1)
        return;
    string to_send;
    uint32_t size = data.size();
    to_send.resize(sizeof(uint32_t));
    *(uint32_t*)&to_send.front() = htonl(size);
    to_send += data;
    if (write(interceptor_fd, to_send.c_str(), to_send.size()) != ssize_t(to_send.size())) {
        cerr_warning << "cannot ack cmd with data: " << data << endl;
    }
}
