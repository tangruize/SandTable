//
// Created by tangruize on 10/8/22.
//

#include "Socket.h"
#include <fcntl.h>

int Socket::set_nonblocking(int fd) {
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