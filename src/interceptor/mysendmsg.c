//
// Created by tangruize on 22-5-16.
//

#include "common.h"
#include "mysendmsg.h"

MAKE_SYS_TEMPLATE(ssize_t, sendmsg, int sockfd, const struct msghdr *msg, int flags)
{
    ssize_t ret = real_sendmsg(sockfd, msg, flags);
    BEGIN_INTERCEPT;
    LOG_INTERCEPTED(CUR_SYSCALL, "SENDMSG IS CALLED, return %d, sendmsg(sockfd: %d, msg: %p, flags: 0x%x)",
                    ret, sockfd, msg, flags);
    END_INTERCEPT;
}
