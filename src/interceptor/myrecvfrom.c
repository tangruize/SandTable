#include "common.h"
#include "config.h"
#include "myrecvfrom.h"

MAKE_SYS_TEMPLATE(ssize_t, recvfrom, int sockfd, void *buf, size_t len, int flags,
                  struct sockaddr *src_addr, socklen_t *addrlen)
{
    ssize_t ret = real_recvfrom(sockfd, buf, len, flags, src_addr, addrlen);
    BEGIN_INTERCEPT;
    struct sockaddr_in check_res = check_fd_is_concerned_with_addr(sockfd);
    if (check_fd_is_concerned(sockfd)) {
        LOG_INTERCEPTED(CUR_SYSCALL, "recvfrom from " ADDR_FMT ", return %ld, recvfrom(sockfd: %d, buf: %p, len: %ld, flags: 0x%x, src_addr: %p, addrlen: %p",
                        ADDR_TO_STR(&check_res), ret, sockfd, buf, len, flags, src_addr, addrlen);
    }
    END_INTERCEPT;
}
