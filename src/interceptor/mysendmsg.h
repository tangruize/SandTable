//
// Created by tangruize on 22-5-16.
//

#ifndef MYSYSCALL_MYSENDMSG_H
#define MYSYSCALL_MYSENDMSG_H

#ifndef _SYS_SOCKET_H
#define _SYS_SOCKET_H
#endif
#include <bits/socket.h>

ssize_t sendmsg(int sockfd, const struct msghdr *msg, int flags);

#endif //MYSYSCALL_MYSENDMSG_H
