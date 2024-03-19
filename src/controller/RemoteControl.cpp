//
// Created by tangruize on 10/12/22.
//

#include "RemoteControl.h"
#include "Msg.h"

#include <algorithm>
#include <fcntl.h>
#include <unistd.h>

int RemoteControl::add_node(const string &node) {
    if (router_to_ssh.find(node) != router_to_ssh.end()) {
        return 0;
    }
    if (!tmpdir.empty()) {
        int idx = get_node_idx(node);
        if (idx == -1) {
            // cerr_warning << "RemoteControl::add_node get_node_idx returns -1: " << idx << endl;
            errno = EINVAL;
            return -1;
        }
        string filename = tmpdir + "/ssh." + to_string(idx);
        int fd = open(filename.c_str(), O_WRONLY | O_APPEND | O_NONBLOCK);
        if (fd == -1) {
            // warn_syserror("RemoteControl::add_node");
            return -1;
        } else {
            cerr_detail << "RemoteControl::add_node ssh file (ssh." << idx <<") to " << node << ": " << fd << endl;
            router_to_ssh[node] = fd;
        }
    }
    return 0;
}

int RemoteControl::add_node(const string &node, int interceptor_fd) {
    router_to_interceptor[node] = interceptor_fd;
    int ret = add_node(node);
    if (ret < 0) {
        warn_syserror("RemoteControl::add_node");
    }
    return ret;
}

int RemoteControl::try_add_node(double timeout) {
    if (timeout < 0)
        return 0;
    double orig_timeout = timeout;
    vector<string> nodes = configFile.get_nodes();
    struct timespec curr_time;
    clock_gettime(CLOCK_MONOTONIC, &curr_time);
    double start = (double)curr_time.tv_sec + (double)curr_time.tv_nsec / 1000000000;
    while (timeout > 0) {
        bool suc = false;
        for (auto it = nodes.begin(); it != nodes.end(); it++) {
            if (add_node(*it) == 0) {
                nodes.erase(it);
                suc = true;
                break;
            } else {
                // cerr_warning << "debug: failed: " << *it << endl;
            }
        }
        if (suc)
            continue;
        if (nodes.empty())
            return 0;
        else {
            nanosleep((const struct timespec[]){{0, 10000000L}}, NULL);
            clock_gettime(CLOCK_MONOTONIC, &curr_time);
            double curr = (double)curr_time.tv_sec + (double)curr_time.tv_nsec / 1000000000.0;
            timeout -= (curr - start);
            start = curr;
            // cerr_warning << "debug: node: " << nodes.size() << endl;
            // cerr_warning << "debug: " << timeout << ", " << curr << ", " << start << ", " << curr_time.tv_sec << ", " << curr_time.tv_nsec << endl;
        }
    }
    if (timeout < 0) {
        cerr_warning << "RemoteControl::try_add_node: timeout: " << timeout << ", " << orig_timeout << endl;
    }
    return -1;
}

DECLARE_string(tmpdir);
DECLARE_int32(sshno);
DECLARE_bool(no_exec_ack);

RemoteControl::RemoteControl() {
    if (!FLAGS_tmpdir.empty()) {
        tmpdir = FLAGS_tmpdir;
    } else {
        cerr_warning << "RemoteControl: TMPDIR is not set, ssh connection control is disabled" << endl;
    }
}

RemoteControl::~RemoteControl() {
    for (auto &f: router_to_ssh) {
        close(f.second);
    }
}

int RemoteControl::send_cmd_interceptor(const string &node, const string &cmd, int lineno) {
    auto it = router_to_interceptor.find(node);
    if (it != router_to_interceptor.end()) {
        string to_send;
        to_send.resize(sizeof(struct MsgHeader));
        *(MsgHeader *)(&to_send.front()) = {.validation = htonl(VALIDATION_DATA), .size = (htonl(cmd.size() + 4))};
        string lineno_bytes;
        lineno_bytes.resize(4);
        *(uint32_t *)&lineno_bytes.front() = htonl(lineno);
        to_send += lineno_bytes;
        to_send += cmd;
        int ret = do_send(it->second, to_send);
        if (ret < 0) {
            close(it->second);
            router_to_interceptor.erase(it);
            return -1;
        } else {
            bool ok = recv_ack(node);
            if (ok)
                return 0;
            else
                return 1;
        }
    } else {
        cerr_warning << "RemoteControl::send_cmd_interceptor cannot find node: " << node << endl;
    }
    return 0;
}

int RemoteControl::do_send(int fd, const string &cmd) {
    if (write(fd, cmd.c_str(), cmd.size()) != int(cmd.size())) {
        warn_syserror("RemoteControl::do_send");
        return -1;
    }
    return int(cmd.size());
}

string RemoteControl::convert_special_char(const string &c) {
    const static map<string, string> special_cmd = {
            {"#crash", R"(\x1c)"},  // ctrl + "\"
            {"#quit", R"(\x1c)"},   // ctrl + "\"
            {"#restart", R"(\x1b\x5b\x41)"},     // arrow up
            {"#shell_redo", R"(\x1b\x5b\x41)"},  // arrow up
            {"#interrupt", R"(\x03)"},  // ctrl + c
            {"#suspend", R"(\x1a)"},    // ctrl + z
            {"#continue", "fg"},  // foreground
            {"#eof", R"(\x04)"},  //  ctrl + d
    };
    string cmd = c;
    auto it = special_cmd.find(cmd);
    if (it != special_cmd.end()) {
        cmd = it->second;
    }
    if (!cmd.empty() && cmd[0] == '\\') {
        std::string rawString;
        for (size_t i = 0; i < cmd.length(); i += 4) {
            std::string hexSubstring = cmd.substr(i, 4);
            int intValue;
            sscanf(hexSubstring.c_str(), "\\x%x", &intValue);
            rawString += static_cast<char>(intValue);
        }
        return rawString;
    } else {
        return cmd;
    }
}

bool RemoteControl::send_cmd_ssh(const string &node, const string &cmd) {
    auto it = router_to_ssh.find(node);
    if (it != router_to_ssh.end()) {
        string converted_cmd = convert_special_char(cmd);
        int ret = do_send(it->second, converted_cmd + '\n');
        if (ret != int(converted_cmd.size()) + 1) {
            close(it->second);
            router_to_ssh.erase(it);
            cerr_detail << "RemoteControl::send_cmd_ssh close node: " << node << endl;
            return false;
        } else {
            if (FLAGS_no_exec_ack)
                return true;
            return recv_ack(node);
        }
    } else {
        cerr_warning << "RemoteControl::send_cmd_ssh cannot find node: " << node << endl;
    }
    return true;
}

// test: we need a command that can aysnc execute
bool RemoteControl::send_cmd_ssh_asy(const string &node, const string &cmd) {
    auto it = router_to_ssh.find(node);
    if (it != router_to_ssh.end()) {
        int ret = do_send(it->second, cmd + '\n');
        if (ret != int(cmd.size()) + 1) {
            close(it->second);
            router_to_ssh.erase(it);
            cerr_detail << "RemoteControl::send_cmd_ssh close node: " << node << endl;
            return false;
        } else {
            return true;
        }
    } else {
        cerr_warning << "RemoteControl::send_cmd_ssh cannot find node: " << node << endl;
    }
    return true;
}

bool RemoteControl::recv_ack(const string &node) {
    auto it = router_to_interceptor.find(node);
    if (it != router_to_interceptor.end()) {
        uint32_t length = 0;
        ssize_t ret = read(it->second, &length, sizeof(length));
        if (ret != sizeof(length)) {
            cerr_warning << "RemoteControl::recv_ack cannot recv ack, return value: " << ret << endl;
        }
        else {
            length = ntohl(length);
            if (length > 4096 || length == 0) {
                cerr_warning << "RemoteControl::recv_ack length is illegal: " << length << endl;
            } else {
                string buf;
                buf.resize(length);
                ret = read(it->second, &buf.front(), length);
                if (ret != length) {
                    cerr_warning << "RemoteControl::recv_ack cannot recv whole data, return value: " << ret << endl;
                } else {
                    if (buf.starts_with("False")) {
                        cerr_warning << "Received ack FAILED from node \"" << node << "\": " << buf << endl;
                        return false;
                    }
                    else if (buf == "True") {
                        cerr_detail << "Received ack ok from node \"" << node << "\": " << buf << endl;
                        return true;
                    } else {
                        cerr_detail << "Received data from node \"" << node << "\": " << buf << endl;
                        cache_cmp_data = std::move(buf);
                        return true;
                    }
                }
            }
        }
    } else {
        cerr_warning << "RemoteControl::recv_ack cannot find node: " << node << endl;
        return false;
    }
    return true;
}

int RemoteControl::get_node_idx(const string &node) const {
    auto it = std::find_if(node.begin(), node.end(), [](char c) { return isdigit(c) != 0; });
    if (it != node.end()) {
        return stoi(node.substr(it - node.begin()));
    } else {
        return -1;
    }
}

RemoteControl *remote_control;
