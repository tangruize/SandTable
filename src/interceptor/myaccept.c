//
// Created by tangruize on 22-5-14.
//

#include "common.h"
#include "myaccept.h"
#include "config.h"

MAKE_SYS_TEMPLATE(int, accept, int sockfd, struct sockaddr *addr, socklen_t *addrlen) {
    int ret = real_accept(sockfd, addr, addrlen);
    BEGIN_INTERCEPT;
    if (ret != -1 && check_addr_is_concerned_with_len((const struct sockaddr_in*)addr, *addrlen)) {
        // the client addr is concerned, add client fd (return value)
        add_concerned_fd(ret, (const struct sockaddr_in*)addr, 1);
        LOG_INTERCEPTED(CUR_SYSCALL, "concern, return %d, accept(sockfd: %d, addr: " ADDR_FMT ", addrlen: %d)",
                        ret, sockfd, ADDR_TO_STR(addr), *addrlen);
    }
    END_INTERCEPT;
}
