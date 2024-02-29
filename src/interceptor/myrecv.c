#include "common.h"
#include "config.h"
#include "myrecv.h"

MAKE_LIB_TEMPLATE(ssize_t, recv, int sockfd, void *buf, size_t len, int flags) {
    ssize_t ret = real_recv(sockfd, buf, len, flags);
    CLOCK_START_RECORD;
    struct sockaddr_in check_res = check_fd_is_concerned_with_addr(sockfd);
    if (check_fd_is_concerned(sockfd)) {
        LOG_INTERCEPTED(LIB_recv, "recv from " ADDR_FMT ", return %ld, recv(sockfd: %d, buf: %p, len: %ld, flags: 0x%x",
                        ADDR_TO_STR(&check_res), ret, sockfd, buf, len, flags);
    }
    CLOCK_END_RECORD;
    return ret;
}
