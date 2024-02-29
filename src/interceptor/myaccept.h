//
// Created by tangruize on 22-5-14.
//

#ifndef MYSYSCALL_MYACCEPT_H
#define MYSYSCALL_MYACCEPT_H

#ifndef _SYS_SOCKET_H
#define _SYS_SOCKET_H
#endif
#include <bits/socket.h>

int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen);

#endif //MYSYSCALL_MYACCEPT_H
