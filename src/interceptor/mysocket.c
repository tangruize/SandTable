//
// Created by tangruize on 22-5-13.
//

#include "common.h"
#include "mysocket.h"

MAKE_SYS_TEMPLATE(int, socket, int domain, int type, int protocol) {
    int ret = real_socket(domain, type, protocol);
    BEGIN_INTERCEPT;
    LOG_INTERCEPTED(CUR_SYSCALL, "return %d, socket(domain: 0x%X, type: 0x%X, protocol: 0x%X)",
                    ret, domain, type, protocol);
    END_INTERCEPT;
}
