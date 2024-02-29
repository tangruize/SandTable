//
// Created by tangruize on 22-5-14.
//

#include "common.h"
#include "mysyscall.h"
#include "config.h"
#include <stdarg.h>

typedef long long syscall_arg_t;

syscall_func_t _syscall_;

// long _my_syscall6(long n, long a1, long a2, long a3, long a4, long a5, long a6) {
//     unsigned long ret;
//     register long r10 __asm__("r10") = a4;
//     register long r8 __asm__("r8") = a5;
//     register long r9 __asm__("r9") = a6;
//     __asm__ __volatile__ ("syscall" : "=a"(ret) : "a"(n), "D"(a1), "S"(a2),
//     "d"(a3), "r"(r10), "r"(r8), "r"(r9) : "rcx", "r11", "memory");
//     return ret;
// }

// __attribute__((constructor, unused))static void set_real_syscall() {
//     _syscall_ = (syscall_func_t) _my_syscall6;
// }

// static long futex(uint32_t *uaddr, int futex_op, uint32_t val, const struct timespec *timeout,  uint32_t *uaddr2, uint32_t val3);

MAKE_LIB_TEMPLATE(long, syscall, long number, ...) {
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

        switch (number) {
            case SYS_sendmmsg:
                assert(0); // WHY sendmmsg bypassed?
            case SYS_futex:
                count_concerned(number);
                if (reg_func_dict[number].concerned_count % 1000 == 1) {
                    LOG_INTERCEPTED(LIB_syscall, "concerned counter: syscall(number: %d)", number);
                }
                break;
            default:
                break;
        }
        // if (number == SYS_futex) {
        //     futex((uint32_t *)a, (int)b, (uint32_t)c, (const struct timespec *)d, (uint32_t *)e, (uint32_t)f);
        // }
    }

    return real_syscall(number, a, b, c, d, e, f);
}

__attribute__((constructor, unused))static void set_real_syscall() {
    _syscall_ = (syscall_func_t) real_syscall;
}

// static long futex(uint32_t *uaddr, int futex_op, uint32_t val, const struct timespec *timeout,  uint32_t *uaddr2, uint32_t val3) {
//     return real_syscall(SYS_futex, uaddr, futex_op, val, timeout, uaddr2, val3);
// }
