//
// Created by tangruize on 2/23/23.
//

#include "TcpNetwork.h"
#include <thread>
#include <sys/epoll.h>

extern "C" {
#include "tlpi/inet_sockets.h"
}

TcpNetwork::TcpNetwork(bool run_accept): Network() {
    if (self.name.empty())
        return;
    addrlen = 0;
    sockfd = inetListen(self.getport().c_str(), 9, &addrlen);
    if (sockfd == -1) {
        throw_syserror("inetListen");
    }
    cerr_verbose << "listening port " << self.getport() << endl;
    if (set_nonblocking(sockfd) == -1) {
        throw_syserror("set_nonblocking");
    }
    if (run_accept) {
        accept_in_background();
//        cerr_verbose << "running accept in background" << endl;
    }
}

bool TcpNetwork::is_connected(int fd) {
    if (fd == -1)
        return false;
    char data;
    ssize_t size = recv(fd, &data, 1, MSG_PEEK | MSG_DONTWAIT);
    if (size == 0 || (size == -1 && errno != EAGAIN))
        return false;
    return true;
}

bool TcpNetwork::connect(const Node &n) {
//    auto it = peers.find(n);
    auto it = find_node(n);
    if (it == peers.end()) {
        cerr_warning << "connect: cannot find peer!" << endl;
        return false;
    }
    int fd = inetConnect(n.gethost().c_str(), n.getport().c_str(), SOCK_STREAM, 1);
    if (fd == -1) {
        warn_syserror("inetConnect");
        return false;
    }
    it->second = fd;
    return true;
}

void TcpNetwork::connect_all() {
    for (auto &i: peers) {
        // detect is still connected
        if (i.second != -1) {
            if (is_connected(i.second)) {
                continue;
            }
            close(i.second);
            i.second = -1;
        }
        // connect peers whose name > self.name. (thus accept connections that peer name < self.name)
        if (i.first.name < self.name)
            continue;
        if (!connect(i.first)) {
            cerr_warning << "failed to connect " << i.first.to_string() << endl;
        } else {
            cerr_verbose << "connected " << i.first.to_string() << endl;
        }
    }
}

int TcpNetwork::accept() {
    if (sockfd == -1) {
        cerr_warning << "sockfd is -1" << endl;
        return 0;
    }
    char claddr[addrlen];
    auto *sa = reinterpret_cast<sockaddr *>(claddr);
    socklen_t alen = addrlen;
    int cfd = ::accept(sockfd, sa, &alen);
    if (cfd == -1) {
        if (errno == EBADF) {
            cerr_verbose << "sockfd is closed" << endl;
            return 0;
        } else if (errno == EAGAIN) {
            return -1;
        } else {
            warn_syserror("accept");
            return -1;
        }
    }
    switch (sa->sa_family) {
        case AF_INET:
            break;
        case AF_INET6:
        default:
            throw_syserror("sa_family not implemented!");
    }
    auto *sin = reinterpret_cast<sockaddr_in*>(sa);
//    auto it = peers.find(*sin);
    auto it = find_node(*sin);
    if (it == peers.end()) {
        char addr_str[IS_ADDR_STR_LEN];
        inetAddressStr(sa, alen, addr_str, IS_ADDR_STR_LEN);
        cerr_warning << "not accepted: cannot find peer " << addr_str << " in config" << endl;
        close(cfd);
        return -1;
    }
    const struct timeval recv_timeout = { .tv_sec = 3, .tv_usec = 0};
    if (setsockopt(cfd, SOL_SOCKET, SO_RCVTIMEO, &recv_timeout, sizeof(recv_timeout)) == -1)
        warn_syserror("accept setsockopt timeout: " + it->first.to_string());
    cerr_verbose << "accept " << it->first.to_string() << endl;
    close(it->second);
    it->second = cfd;
    return cfd;
}

void TcpNetwork::accept_in_background() {
    cerr_verbose << "start accept thread" << endl;
    thread t1([this] { accept_loop(); });
    t1.detach();
}

void TcpNetwork::accept_loop() {
    struct epoll_event ev{};
    struct epoll_event events[1];
    int nfds, epoll_fd = epoll_create1(0);
    if (epoll_fd == -1) {
        throw_syserror("epoll_create");
    }

    ev.events = EPOLLIN | EPOLLET;  // edge triggered
    ev.data.fd = sockfd;
    if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, sockfd, &ev) == -1)
        throw_syserror("epoll_ctl");

    while (true) {
        nfds = epoll_wait(epoll_fd, events, 1, -1);
        if (nfds == -1) {
            if (errno == EINTR) {
                cerr_warning << "epoll_wait is interrupted by signal" << endl;
                continue;
            } else
                throw_syserror("epoll_wait");
        }

        for (int n = 0; n < nfds; ++n) {
            if (events[n].data.fd == sockfd) {
                while (accept() > 0) {  // edge trigger, accept until no request to handle
                    ;
                }
            }
        }
        if (sockfd == -1)
            return;
    }
}

ssize_t TcpNetwork::send_to(const Node &peer, const string &data) {
//    auto it = peers.find(peer);
    auto it = find_node(peer);
    if (it == peers.end() || it->second < 0) {
        cerr_warning << "cannot send to " << peer.to_string() << endl;
        return -1;
    }
    string to_send;
    uint32_t size = htonl(data.size());
    to_send.resize(sizeof(size));
    *(uint32_t *)&to_send.front() = size;
    to_send += data;
    ssize_t ret = write(it->second, to_send.c_str(), to_send.size());
    if (ret != ssize_t(data.size()) + 4) {
        if (ret == -1)
            warn_syserror("send_to");
        else {
            cerr_warning << "partial send: " + to_string(ret) + "/" + to_string(to_send.size());
        }
    }
    return ret;
}

ssize_t TcpNetwork::recv_from(const Node &peer, string &data) {
//    auto it = peers.find(peer);
    auto it = find_node(peer);
    if (it == peers.end() || it->second < 0) {
        cerr_warning << "cannot find node " << peer.to_string() << endl;
        return -1;
    }
    uint32_t size;
    ssize_t ret = recv(it->second, &size, sizeof(size), MSG_DONTWAIT | MSG_PEEK);
    if (ret != 4) {
        if (ret == -1) {
            warn_syserror("TcpNetwork::recv_from");
            close(it->second);
            it->second = -1;
        } else {
            cerr_warning << "recv_from cannot get size" << endl;
        }
        return -1;
    }
    if (recv(it->second, &size, sizeof(size), MSG_DONTWAIT) != 4) {  // discard 4 bytes
        cerr_warning << "recv_from failed to discard 4 bytes" << endl;
        return -1;
    }
    size = ntohl(size);
    if (size > 65535) {
        cerr_warning << "recv_from: size is too big!" << endl;
        abort();
    }
    data.resize(size);
    ret = recv(it->second, &data.front(), size, MSG_WAITALL);
    if (ret == -1) {
        warn_syserror("recv_from");
    }
    return ret;
}

bool TcpNetwork::is_all_connected() {
    return std::ranges::all_of(peers.cbegin(), peers.cend(), [](const pair<Node, int>&i) {
        return i.second != -1 && is_connected(i.second);
    });
}
