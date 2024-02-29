//
// Created by tangruize on 22-5-16.
//

#include "common.h"
#include "mysendmmsg.h"

MAKE_SYS_TEMPLATE(int, sendmmsg, int sockfd, struct mmsghdr *msgvec, unsigned int vlen, int flags)
{
    int ret = real_sendmmsg(sockfd, msgvec, vlen, flags);
    BEGIN_INTERCEPT;
    LOG_INTERCEPTED(CUR_SYSCALL, "SENDMMSG IS CALLED, return %d, sendmmsg(sockfd: %d, mmsghdr: %p, vlen: %d, flags: 0x%x)",
                    ret, sockfd, msgvec, vlen, flags);
    END_INTERCEPT;
}
