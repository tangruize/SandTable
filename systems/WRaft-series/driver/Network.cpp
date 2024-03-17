//
// Created by tangruize on 2/13/23.
//

#include "Network.h"
#include <fcntl.h>

int Network::load_config() {
    bool ok = config.get_self_node(self);
    if (!ok) {
        cerr_warning << "Self node name is not set" << endl;
    }
    int count = 0;
    for (auto &i: config.get_all_nodes()) {
        count += add_node(i);
    }
    return count;
}

bool Network::add_node(const Node &peer) {
//    auto it = peers.find(peer);
    auto it = find_node(peer);
    if (it != peers.end() || peer.name == self.name) {
        if (it != peers.end() && peer.name == self.name) {
            close(it->second);
            peers.erase(it);
        }
        return false;
    }
    peers[peer] = -1;
    return true;
}

Network::Network() {
    sockfd = -1;
    evfd = -1;
    int n = load_config();
    cerr_verbose << "Load " << n << " peer nodes" << endl;
}

void Network::shut_down() {
    int fd = sockfd;
    sockfd = -1;
    close(fd);
    close(evfd);
}

int Network::set_nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags == -1) {
//        warn_syserror("set_nonblocking fcntl F_GETFL");
        return -1;
    }
    flags |= O_NONBLOCK;
    if (fcntl(fd, F_SETFL, flags) == -1) {
//        warn_syserror("set_nonblocking fcntl F_SETFL");
        return -1;
    }
    return 0;
}

bool Network::repl(const string &cmd) {
    auto tokens = tokenize(cmd);
    if (tokens[0] == "connectall") {
        connect_all();
        return true;
    } else if (tokens[0] == "connect") {
        if (tokens.size() > 1) {
            return connect(tokens[1]);
        } else {
            return false;
        }
    } else if (tokens[0] == "isallconnected") {
        return is_all_connected();
    } else if (tokens[0] == "recv") {
        // to implement epoll!
        return false;
    } else if (tokens[0] == "recvfrom") {
        if (tokens.size() > 1) {
            return recv_from(tokens[1]) > 0;
        } else {
            return false;
        }
    }
    return false;
}

map<Node, int>::iterator Network::find_node(const Node &e) {
    static cmp_addr_equal eq;
    map<Node, int>::iterator it;
    if (e.name.empty()) {
        auto is_eq = [&e](const pair<Node, int> &i){ return eq(i.first.addr, e.addr); };
        it = std::find_if(begin(peers), end(peers), is_eq);
    } else {
        it = peers.find(e);
    }
    return it;
}

Network *net;