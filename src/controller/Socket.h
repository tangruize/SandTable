//
// Created by tangruize on 10/8/22.
//

#ifndef TPROXY_SOCKET_H
#define TPROXY_SOCKET_H

#include "common.h"

struct AcceptData {
    int socket_fd;
    struct sockaddr_in client_addr;
    struct sockaddr_in origin_client_addr;
    struct sockaddr_in origin_addr;
    struct sockaddr_in masque_addr;
};

class Socket {
public:
    static int set_nonblocking(int fd);
    virtual int socket() const = 0;
    // virtual AcceptData accept(int client_fd) const = 0;
};


#endif //TPROXY_SOCKET_H
