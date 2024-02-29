//
// Created by tangruize on 22-5-14.
//

#include "common.h"
#include "myclose.h"
#include "config.h"

MAKE_SYS_TEMPLATE(int, close, int fd) {
    int ret = real_close(fd);
    BEGIN_INTERCEPT;
    struct sockaddr_in check_res = check_fd_is_concerned_with_addr(fd);
    if (check_res.sin_port != 0) {
        rm_concerned_fd(fd);
        LOG_INTERCEPTED(CUR_SYSCALL, "noconcern " ADDR_FMT ", return %d, close(fd: %d)", ADDR_TO_STR(&check_res), ret, fd);
    }
    END_INTERCEPT;
}
