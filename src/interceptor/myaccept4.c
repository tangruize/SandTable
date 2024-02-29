//
// Created by fedora on 5/26/22.
//

#include "common.h"
#include "config.h"
#include "myaccept4.h"

MAKE_SYS_TEMPLATE(int, accept4, int sockfd, struct sockaddr *addr, socklen_t *addrlen, int flags) {
    int ret = real_accept4(sockfd, addr, addrlen, flags);
    BEGIN_INTERCEPT;
    if (ret != -1 && check_addr_is_concerned_with_len((const struct sockaddr_in*)addr, *addrlen)) {
        // the client addr is concerned, add client fd (return value)
        add_concerned_fd(ret, (const struct sockaddr_in*)addr, 1);
        LOG_INTERCEPTED(CUR_SYSCALL, "concern, return %d, accept4(sockfd: %d, addr: " ADDR_FMT ", addrlen: %d, flags: 0x%X)",
                        ret, sockfd, ADDR_TO_STR(addr), *addrlen, flags);
    }
    END_INTERCEPT;
}
