//
// Created by tangruize on 22-5-10.
//

#ifndef TPROXY_TCPSOCKET_H
#define TPROXY_TCPSOCKET_H

#include "common.h"
#include "Socket.h"

class TcpSocket: Socket {
private:
    int socket_fd = -1;
    int bind_port = 10100;
public:
    TcpSocket(int port=-1);
    int socket() const override {
        return socket_fd;
    }
    AcceptData accept(int client_fd = -1) const;
};

#endif //TPROXY_TCPSOCKET_H
