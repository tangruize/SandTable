#include "common.h"
#include "config.h"
#include "myread.h"

MAKE_SYS_TEMPLATE(ssize_t, read, int fd, void *buf, size_t count) {
    ssize_t ret = real_read(fd, buf, count);
    BEGIN_INTERCEPT;
    struct sockaddr_in check_res = check_fd_is_concerned_with_addr(fd);
    if (check_res.sin_port != 0) {
        LOG_INTERCEPTED(CUR_SYSCALL, "read from " ADDR_FMT ", return %d, read(fd: %d, buf: %p, count: %ld)",
                        ADDR_TO_STR(&check_res), ret, fd, buf, count);
    }
    END_INTERCEPT;
}
