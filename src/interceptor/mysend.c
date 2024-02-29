//
// Created by tangruize on 22-5-15.
//

#include "common.h"
#include "mysend.h"
#include "mysendto.h"

MAKE_LIB_TEMPLATE(ssize_t, send, int sockfd, const void *buf, size_t len, int flags) {
    nr_send_syscall = LIB_send;
    return sendto(sockfd, buf, len, flags, NULL, 0);  // send() equals to sendto(dest_addr:NULL, addrlen:0)
}
