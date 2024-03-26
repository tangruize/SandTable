//
// Created by tangruize on 22-5-14.
//

#include "common.h"
#include "mysyscall.h"
#include "config.h"
#include <stdarg.h>
#include <unistd.h>

typedef long long syscall_arg_t;

syscall_func_t _syscall_;

MAKE_LIB_TEMPLATE(SYSCALL_FUNC_TYPE, syscall, SYSCALL_FUNC_TYPE number, ...) {
    va_list ap;
    syscall_arg_t a, b, c, d, e, f;
    va_start(ap, number);
    a = va_arg(ap, syscall_arg_t);
    b = va_arg(ap, syscall_arg_t);
    c = va_arg(ap, syscall_arg_t);
    d = va_arg(ap, syscall_arg_t);
    e = va_arg(ap, syscall_arg_t);
    f = va_arg(ap, syscall_arg_t);
    va_end(ap);

    if (check_count_intercepted(LIB_syscall)) {
        count_intercepted(number);
        // LOG_INTERCEPTED(LIB_syscall, "concerned counter: syscall(number: %d)", number);
    }
    return real_syscall(number, a, b, c, d, e, f);
}

__attribute__((constructor, unused))static void set_real_syscall() {
#ifdef __unix__
    getpid();  // it cannot be removed
#endif
    _syscall_ = (syscall_func_t) real_syscall;
}
