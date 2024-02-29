//
// Created by tangruize on 22-5-13.
//

#include "common.h"
#include "config.h"
#include "mysendto.h"
#include "mysend.h"

#include <stdio.h>

__thread unsigned nr_send_syscall = 0;

static ssize_t hack(int sockfd, size_t len, int flags, const struct sockaddr *dest_addr, socklen_t addrlen);

MAKE_SYS_TEMPLATE(ssize_t, sendto, int sockfd, const void *buf, size_t len, int flags,
                  const struct sockaddr *dest_addr, socklen_t addrlen)
{
    CLOCK_START_RECORD;
    if (!check_intercept(SYS_sendto))
        return real_sendto(sockfd, buf, len, flags, dest_addr, addrlen);

    if (!nr_send_syscall)
        nr_send_syscall = SYS_sendto;

    // hack before send
    struct sockaddr_in check_res = check_fd_is_concerned_with_addr(sockfd);
    ssize_t ret;
    int is_concerned = 0;
    char msg_buf[32];
    if (check_res.sin_port != 0 || check_addr_is_concerned_with_len((const struct sockaddr_in *)dest_addr, addrlen)) {
        is_concerned = 1;
        ret = hack(sockfd, len, flags, dest_addr, addrlen);
        if (ret != sizeof(struct hacked_sendto_header)) { // send error, cancel real send
            print_info("WARN: sendto not send full header: %d\n", ret);
            nr_send_syscall = 0;
            return ret;
        }
        const struct sockaddr_in *addr_ptr = (check_res.sin_port != 0) ? &check_res : (const struct sockaddr_in *)dest_addr;
        snprintf(msg_buf, 32, "hack " ADDR_FMT, ADDR_TO_STR(addr_ptr));
    }
    CLOCK_END_RECORD;

    // do real send (directly use sendto, because write/send can be equal to it)
    ret = real_sendto(sockfd, buf, len, flags, dest_addr, addrlen);

    // print intercept msg
    BEGIN_INTERCEPT_NR(nr_send_syscall);
    if (is_concerned) {
        if (nr_send_syscall == SYS_write || nr_send_syscall == SYS_writev)
            LOG_INTERCEPTED(nr_send_syscall, "%s, return %ld, write(sockfd: %d, buf: \"%s\", count: %d)",
                            msg_buf, ret, sockfd, bstr1(buf, len), len);
        else if (nr_send_syscall == LIB_send)
            LOG_INTERCEPTED(LIB_send, "%s, return %ld, send(sockfd: %d, buf: \"%s\", len: %d, flags: 0x%X)",
                            msg_buf, ret, sockfd, bstr1(buf, len), len, flags);
        else if (nr_send_syscall == SYS_sendto)
            LOG_INTERCEPTED(SYS_sendto, "%s, return %ld, sendto(sockfd: %d, buf: \"%s\", len: %d, flags: 0x%X, dest_addr: " ADDR_FMT ", addrlen: %d)",
                            msg_buf, ret, sockfd, bstr1(buf, len), len, flags, ADDR_TO_STR(dest_addr), addrlen);
    } else {
        LOG_INTERCEPTED(SYS_sendto, "Not concerned! return %ld, sendto(sockfd: %d, buf: \"%s\", len: %d, flags: 0x%X, dest_addr: " ADDR_FMT ", addrlen: %d)",
                        ret, sockfd, bstr1(buf, len), len, flags, ADDR_TO_STR(dest_addr), addrlen);
    }
    nr_send_syscall = 0;
    END_INTERCEPT;
}

// hack: send control info (size, time)
static ssize_t hack(int sockfd, size_t len, int flags, const struct sockaddr *dest_addr, socklen_t addrlen) {
    struct hacked_sendto_header buf = {
            .validation = htonl(VALIDATE_STR),
            .size = htonl(len),
    };
    return real_sendto(sockfd, &buf, sizeof(buf), flags, dest_addr, addrlen);
}
