//
// Created by tangruize on 22-5-15.
//

#include "common.h"
#include "config.h"
#include "mywrite.h"
#include "mysendto.h"
#include "state_collector.h"

MAKE_SYS_TEMPLATE(ssize_t, write, int fd, const void *buf, size_t count) {
    CLOCK_START_RECORD;
    if (!check_intercept(CUR_SYSCALL))
        return real_write(fd, buf, count);

    int log_fd = get_log_fd(fd);
    if (log_fd != -1) {
        write_log(log_fd, buf, count);
        return real_write(fd, buf, count);
    }
    else if (check_fd_is_concerned(fd)) {  // write() equals send(flags:0, dest_addr:NULL, addrlen:0)
        if (!nr_send_syscall)
            nr_send_syscall = CUR_SYSCALL;
        CLOCK_END_RECORD;
        return sendto(fd, buf, count, 0, NULL, 0);
    }
    else {
        count_intercepted(CUR_SYSCALL);
        CLOCK_END_RECORD;
        return real_write(fd, buf, count);
    }
}
