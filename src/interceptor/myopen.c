//
// Created by tangruize on 22-5-13.
//

#include "common.h"
#include "myopen.h"

#ifndef _FCNTL_H
#define	_FCNTL_H
#endif
#include <bits/fcntl.h>  // O_CREAT and O_TMPFILE
#include <stdarg.h>

MAKE_SYS_TEMPLATE(int, open, const char *pathname, int flags, ...) {
    int ret;
    mode_t mode = 0;
    if (flags & (O_CREAT | O_TMPFILE)) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, mode_t);
        ret = real_open(pathname, flags, mode);
        va_end(ap);
    }
    else
        ret = real_open(pathname, flags);
    BEGIN_INTERCEPT;
//    LOG_INTERCEPTED(CUR_SYSCALL, "return %d, open(pathname: \"%s\", flags: 0x%X, mode: %04o)",
//                    ret, rstr1(pathname), flags, mode);
    END_INTERCEPT;
}
