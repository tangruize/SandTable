//
// Created by weiyuyang on 22-11-1.
//

#ifndef TPROXY_UDPSOCKET_H
#define TPROXY_UDPSOCKET_H


#define LOCAL_PROXY_PORT 3127
#define MAX_MSG 1500
#ifndef IP_TRANSPARENT
#define IP_TRANSPARENT 19
#endif
#ifndef IP_ORIGADDRS
#define IP_ORIGADDRS      20
#endif
#ifndef IP_RECVORIGADDRS
#define IP_RECVORIGADDRS  IP_ORIGADDRS
#endif
#define CTL_BUF_SIZE 64

#include "common.h"
#include "Socket.h"
#include "Msg.h"



class UdpSokcet: Socket {
private:
    int socket_fd = -1;
    int bind_port = 10100;
    struct sockaddr_in proxy_addr;
public:
    UdpSokcet(int port=-1);
    int socket() const override {
        return socket_fd;
    }
    int bindport() const {
        return bind_port;
    }
};

#endif //TPROXY_UDPSOCKET_H
