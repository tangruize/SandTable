//
// Created by tangruize on 22-5-10.
//

#include "TcpSocket.h"

using namespace std;

TcpSocket::TcpSocket(int port) {
    socket_fd = -1;
    if (port != -1)
        bind_port = port;

    cerr_verbose << "Init socket" << endl;
    socket_fd = ::socket(AF_INET, SOCK_STREAM, 0);
    if (socket_fd == -1)
        throw_syserror("socket");
    if (set_nonblocking(socket_fd) == -1)
        throw_syserror("set_nonblocking");

    const int opt = 1;
    if (setsockopt(socket_fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt)) == -1)
        throw_syserror("setsockopt");
    // (TPROXY) Set IP_TRANSPARENT to get all traffic even if their dest is not me
    cerr_verbose << "Set socket TPROXY options" << endl;
    if (setsockopt(socket_fd, SOL_IP, IP_TRANSPARENT, &opt, sizeof(opt)) == -1)
        throw_syserror("setsockopt");

    struct sockaddr_in bind_addr{};
    bind_addr.sin_family = AF_INET;
    bind_addr.sin_addr.s_addr = htonl(INADDR_ANY);
//    inet_aton("127.0.0.1", &bind_addr.sin_addr);
    bind_addr.sin_port = htons(bind_port);
    cerr_verbose << "Bind ip " << inet_ntoa(bind_addr.sin_addr) << endl;
    if (bind(socket_fd, (struct sockaddr*)&bind_addr, sizeof(bind_addr)) == -1)
        throw_syserror("bind");

    cerr_verbose << "Listen on port " << bind_port << endl;
    if (listen(socket_fd, 10) < 0)
        throw_syserror("listen");
}

AcceptData TcpSocket::accept(int fd) const {
    struct AcceptData ret{};
    ret.socket_fd = fd;

    socklen_t client_len = sizeof(ret.client_addr);
    if (ret.socket_fd < 0) {
        ret.socket_fd = ::accept(socket_fd, (struct sockaddr*)&ret.client_addr, &client_len);
        if (ret.socket_fd == -1) {
            if (errno == EAGAIN)
                return ret;
            throw_syserror("accept");
        }
        cerr_verbose << "Accept TCP client fd: " << ret.socket_fd << " " << configFile.get_node_name_with_addr(ret.client_addr);
    }
    else {
        if (getpeername(ret.socket_fd, (struct sockaddr*)&ret.client_addr, &client_len) == -1)
            throw_syserror("getpeername");
        cerr_verbose << "Get accepted TCP client fd: " << ret.socket_fd << " " << configFile.get_node_name_with_addr(ret.client_addr);
    }

    socklen_t origin_len = sizeof(ret.origin_addr);
    // (TPROXY) Get the original address and port
    if (getsockname(ret.socket_fd, (struct sockaddr*)&ret.origin_addr, &origin_len) == -1) {
//        cerr_warning << "sock fd" << ret.socket_fd << endl;
        throw_syserror("getsockname");
    }
    ret.masque_addr = configFile.get_masquerade_addr(ret.origin_addr);
    ret.origin_client_addr = configFile.get_origin_addr(ret.client_addr);
    cerr_verbose_cont << " -> " << configFile.get_node_name_with_addr(ret.masque_addr);
    if (configFile.is_router_addr(ret.origin_addr)) {
        cerr_verbose_cont << endl;
    } else {
        cerr_verbose_cont << " (origin: " << configFile.get_node_name_with_addr(ret.origin_addr) << ")" << endl;
    }
    return ret;
}
