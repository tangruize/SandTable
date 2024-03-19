//
// Created by weiyuyang on 22-11-10.
//

#include "UdpSocket.h"

using namespace std;

/// @brief prot 被设置了 IP_TRANSPARENT 所以可以随意设置地址
/// @param port 
UdpSokcet::UdpSokcet(int port) {
    socket_fd = -1;
    if (port != -1)
        bind_port = port;

    cerr_verbose << "Init socket" << endl;
    // UDP
    socket_fd = ::socket(AF_INET, SOCK_DGRAM, 0);
    if (socket_fd == -1)
        throw_syserror("socket");
    if (set_nonblocking(socket_fd) == -1)
        throw_syserror("set_nonblocking");

    const int opt = 1;
    if (setsockopt(socket_fd, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt)) == -1)
        throw_syserror("setsockopt");

    if (setsockopt(socket_fd, IPPROTO_IP, IP_PKTINFO, &opt, sizeof(opt)) == -1)
        throw_syserror("setsockopt");
    // (TPROXY) Set IP_TRANSPARENT to get all traffic even if their dest is not me
    cerr_verbose << "Set socket TPROXY options" << endl;
    if (setsockopt(socket_fd, SOL_IP, IP_TRANSPARENT, &opt, sizeof(opt)) == -1)
        throw_syserror("setsockopt");
   
    if ( setsockopt(socket_fd, SOL_IP, IP_ORIGADDRS , &opt, sizeof(opt)) == -1)
        throw_syserror("setsockopt");
    // struct sockaddr_in bind_addr{};
    proxy_addr.sin_family = AF_INET;
    proxy_addr.sin_addr.s_addr = htonl(INADDR_ANY);
//    inet_aton("127.0.0.1", &bind_addr.sin_addr);
    proxy_addr.sin_port = htons(bind_port);
    cerr_verbose << "Bind ip " << inet_ntoa(proxy_addr.sin_addr) << endl;
    if (bind(socket_fd, (struct sockaddr*)&proxy_addr, sizeof(proxy_addr)) == -1)
        throw_syserror("bind");

    cerr_verbose << "UDP - Bind on port " << bind_port << endl;
}
