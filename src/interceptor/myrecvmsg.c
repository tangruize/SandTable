#include "common.h"
#include "myrecvmsg.h"

MAKE_SYS_TEMPLATE(ssize_t, recvmsg, int sockfd, struct msghdr *msg, int flags)
{
    ssize_t ret = real_recvmsg(sockfd, msg, flags);
    BEGIN_INTERCEPT;
    LOG_INTERCEPTED(CUR_SYSCALL, "RECVMSG IS CALLED, return %d, recvmsg(sockfd: %d, msg: %p, flags: 0x%x)",
                    ret, sockfd, msg, flags);
    END_INTERCEPT;
}
