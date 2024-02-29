#ifndef MYSYSCALL_MYRECVFROM_H
#define MYSYSCALL_MYRECVFROM_H

//#ifndef _SYS_SOCKET_H
//#define _SYS_SOCKET_H
//#endif
#include <sys/socket.h>   // struct sockaddr, socklen_t

ssize_t recvfrom(int sockfd, void *buf, size_t len, int flags,
                 struct sockaddr *src_addr, socklen_t *addrlen);

#endif //MYSYSCALL_MYRECVFROM_H
