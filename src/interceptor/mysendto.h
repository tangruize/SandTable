//
// Created by tangruize on 22-5-13.
//

#ifndef MYSYSCALL_MYSENDTO_H
#define MYSYSCALL_MYSENDTO_H

#ifndef _SYS_SOCKET_H
#define _SYS_SOCKET_H
#endif
#include <bits/socket.h>  // struct sockaddr, socklen_t
#include <time.h>

// if the sendto msg is concerned, send the hacked_sendto_header first before send real contents
struct __attribute__((__packed__)) hacked_sendto_header {
    uint32_t validation;
    uint32_t size;         // msg length
};

#define VALIDATE_STR 0xdeadbeef

// current call send function: write/send/sento
extern __thread unsigned nr_send_syscall;

ssize_t send(int sockfd, const void *buf, size_t len, int flags);
ssize_t sendto(int sockfd, const void *buf, size_t len, int flags, const struct sockaddr *dest_addr, socklen_t addrlen);

#endif //MYSYSCALL_MYSENDTO_H
