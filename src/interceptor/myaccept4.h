//
// Created by fedora on 5/26/22.
//

#ifndef MYSYSCALL_MYACCEPT4_H
#define MYSYSCALL_MYACCEPT4_H

#ifndef _SYS_SOCKET_H
#define _SYS_SOCKET_H
#endif
#include <bits/socket.h>

int accept4(int sockfd, struct sockaddr *restrict addr, socklen_t *restrict addrlen, int flags);

#endif //MYSYSCALL_MYACCEPT4_H
