//
// Created by tangruize on 22-5-15.
//

#include "common.h"
#include "config.h"
#include "mywritev.h"
#include "mysendto.h"
#include "mywrite.h"

#define WRITEV_USE_MALLOC  // use malloc to avoid big buffer causing stack overflow

MAKE_SYS_TEMPLATE(ssize_t, writev, int fd, const struct iovec *iov, int iovcnt) {
    CLOCK_START_RECORD;
    if (!check_intercept(CUR_SYSCALL))
        return real_writev(fd, iov, iovcnt);

    if (check_fd_is_concerned(fd) || get_log_fd(fd) > 0) {  // write() equals send(flags:0, dest_addr:NULL, addrlen:0)
        nr_send_syscall = CUR_SYSCALL;
        size_t count = 0;
        for (int i = 0; i < iovcnt; i++) {
            count += iov[i].iov_len;
        }
        #ifdef WRITEV_USE_MALLOC
        char *buf = malloc(count);
        #else
        char buf[count];
        #endif
        count = 0;
        for (int i = 0; i < iovcnt; i++) {
            memcpy(&buf[count], iov[i].iov_base, iov[i].iov_len);
            count += iov[i].iov_len;
        }
        CLOCK_END_RECORD;
        ssize_t ret = write(fd, buf, count);
        #ifdef WRITEV_USE_MALLOC
        free(buf);
        #endif
        nr_send_syscall = 0;
        return ret;
        // return sendto(fd, buf, count, 0, NULL, 0);
    }
    else {
        count_intercepted(CUR_SYSCALL);
        CLOCK_END_RECORD;
        return real_writev(fd, iov, iovcnt);
    }
}
