//
// Created by tangruize on 22-5-15.
//

#ifndef MYSYSCALL_MYSEND_H
#define MYSYSCALL_MYSEND_H

extern unsigned LIB_send;
ssize_t send(int sockfd, const void *buf, size_t len, int flags);

#endif //MYSYSCALL_MYSEND_H
