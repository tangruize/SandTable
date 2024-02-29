//
// Created by tangruize on 22-5-14.
//

#include "common.h"
#include "myconnect.h"
#include "config.h"

#include <errno.h>

MAKE_SYS_TEMPLATE(int, connect, int sockfd, const struct sockaddr *addr, socklen_t addrlen) {
    if (!begin_intercept(CUR_SYSCALL))
        return real_connect(sockfd, addr, addrlen);
    CLOCK_START_RECORD;
    int concerned = 0;
    // add in advance because connect() can be nonblocking
    if (check_addr_is_concerned_with_len((const struct sockaddr_in*)addr, addrlen)) {
        add_concerned_fd(sockfd, (const struct sockaddr_in*)addr, 0);
        concerned = 1;
    }
    CLOCK_END_RECORD;
    int ret = real_connect(sockfd, addr, addrlen);
    CLOCK_START_RECORD2;
    if (concerned == 1) {
        if (ret != -1 || errno == EINPROGRESS) {
            LOG_INTERCEPTED(CUR_SYSCALL, "concern, return %d, connect(sockfd: %d, addr: " ADDR_FMT ", addrlen: %d)",
                            ret, sockfd, ADDR_TO_STR(addr), addrlen);
        } else {
            rm_concerned_fd(sockfd);
        }
    }
    CLOCK_END_RECORD2;
    return ret;
}
