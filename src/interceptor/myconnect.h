//
// Created by tangruize on 22-5-14.
//

#ifndef MYSYSCALL_MYCONNECT_H
#define MYSYSCALL_MYCONNECT_H

#ifndef _SYS_SOCKET_H
#define _SYS_SOCKET_H
#endif
#include <bits/socket.h>

int connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen);

#endif //MYSYSCALL_MYCONNECT_H
