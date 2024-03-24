#ifndef MYSYSCALL_MYRECVMSG_H
#define MYSYSCALL_MYRECVMSG_H

//#ifndef _SYS_SOCKET_H
//#define _SYS_SOCKET_H
//#endif
#include <sys/socket.h> 

ssize_t recvmsg(int sockfd, struct msghdr *msg, int flags);

#endif //MYSYSCALL_MYRECVMSG_H
