//
// Created by tangruize on 22-5-13.
//

#ifndef MYSYSCALL_COMMON_H
#define MYSYSCALL_COMMON_H

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <dlfcn.h>
#include <errno.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/syscall.h>

#include "timing.h"

#define UNUSED(x) (void)(x)

// #ifdef __linux__
// #define MY_STDERR_FILENO 1023
// #elif defined(__unix__)
// #define MY_STDERR_FILENO 127 // openbsd max is 128?
// #endif
#define MY_STDERR_FILENO 127

#define STATE_UNUSED    0
#define STATE_ENABLED   1
#define STATE_PTRACE    2
#define STATE_LIBRARY   4
#define STATE_DISABLED  8

struct reg_func_t {
    char name[32];
    uint64_t count;
    uint64_t concerned_count;
    void *real_func;
    void *fake_func;
    int state;
};

#define NR_REG_FUNC_DICT 512
extern struct reg_func_t reg_func_dict[NR_REG_FUNC_DICT];

extern unsigned NR_self_defined_func;

#define PRINT_PREFIX         "[MYSYSCALL] "
//#define PRINT_FIRST_USAGE
//#define PRINT_EVERY_USAGE
//#define PRINT_STATISTICS

// write to stderr directly using syscall number
void print_info_internal(int flags, const char *format, ...);
#define PRINT_NO_PROMPT 1
#define PRINT_STDERR    2
#define print_info(format...) print_info_internal(0, format)
#define print_info_no_prompt(format...) print_info_internal(PRINT_NO_PROMPT, format)
#define print_info_stderr(format...) print_info_internal(PRINT_STDERR, format)

// register an intercepted function to log usages
void register_intercepted(unsigned nr_syscall, const char *name, void *func, void **real);

// unregister an intercepted function
static inline void unregister_intercepted(unsigned nr_syscall) {
    reg_func_dict[nr_syscall].state = (reg_func_dict[nr_syscall].state & ~STATE_ENABLED) | STATE_DISABLED;
}

// log usages of the intercepted syscall
#if defined(PRINT_FIRST_USAGE) || defined(PRINT_EVERY_USAGE)
void log_intercepted(unsigned nr_syscall, const char *format, ...);
#define LOG_INTERCEPTED(nr_syscall, format...)  log_intercepted(nr_syscall, format)
#else
void log_intercepted(unsigned nr_syscall);
#define LOG_INTERCEPTED(nr_syscall, ...)  log_intercepted(nr_syscall)
#endif

// restrict string argument length for logging
const char *restrict_str_internal(unsigned which, const char *buf);
#define rstr1(buf) restrict_str_internal(0, buf)
#define rstr2(buf) restrict_str_internal(1, buf)
#define rstr3(buf) restrict_str_internal(2, buf)
#define rstr4(buf) restrict_str_internal(3, buf)

// restrict length and convert binary data to \x00~\xFF
const char *binary_str_internal(unsigned which, const void *buf, size_t size);
#define bstr1(buf, sz) binary_str_internal(0, buf, sz)
#define bstr2(buf, sz) binary_str_internal(1, buf, sz)
#define bstr3(buf, sz) binary_str_internal(2, buf, sz)
#define bstr4(buf, sz) binary_str_internal(3, buf, sz)

// save errno
extern __thread int saved_errno;

// check if we can start intercept
static inline int check_intercept(unsigned nr_syscall) {
    return reg_func_dict[nr_syscall].state & STATE_ENABLED;
}

// count the intercepted syscall that we do not concern
static inline void count_intercepted(unsigned nr_syscall) {
    reg_func_dict[nr_syscall].count++;
}

// count the intercepted syscall that we concern
static inline void count_concerned(unsigned nr_syscall) {
    reg_func_dict[nr_syscall].concerned_count++;
}

static inline int check_count_intercepted(unsigned nr_syscall) {
    if (check_intercept(nr_syscall)) {
        count_intercepted(nr_syscall);
        return 1;
    }
    return 0;
}

// call it before intercept to check if we can intercept, and then save errno
static inline int begin_intercept(unsigned nr_syscall) {
    if (!check_intercept(nr_syscall))
        return 0;
    saved_errno = errno;
    count_intercepted(nr_syscall);
    return 1;
}
#define BEGIN_INTERCEPT CLOCK_START_RECORD2; if (!begin_intercept(CUR_SYSCALL)) return ret
#define BEGIN_INTERCEPT_NR(nr_syscall) CLOCK_START_RECORD2; if (!begin_intercept(nr_syscall)) return ret

// call it before return to restore errno
static inline void end_intercept() {
    errno = saved_errno;
}
#define END_INTERCEPT do { end_intercept(); CLOCK_END_RECORD2; return ret; } while (0)

extern int is_inited;

#define STR(x) #x
#define CAT(a, b) a ## b
#define CAT3(a, b, c) a ## b ## c

#define MAKE_SYS_TEMPLATE(type, name, args...)        \
static const unsigned CUR_SYSCALL = CAT(SYS_, name);  \
static type (*CAT(real_, name))(args) = NULL;         \
type name(args);                                      \
__attribute__((constructor, unused))                  \
static void CAT(reg_, name)() {                       \
    CLOCK_START_RECORD                                \
    register_intercepted(CUR_SYSCALL, STR(name), name, (void **)&(CAT(real_, name))); \
    CLOCK_END_RECORD                                  \
}                                                     \
type name(args)

#define MAKE_LIB_TEMPLATE(type, name, args...)        \
unsigned CAT(LIB_, name);                             \
static type (*CAT(real_, name))(args) = NULL;         \
type name(args);                                      \
__attribute__((constructor, unused))                  \
static void CAT(reg_, name)() {                       \
    CLOCK_START_RECORD                                \
    CAT(LIB_, name) = NR_self_defined_func--;         \
    register_intercepted(CAT(LIB_, name), STR(name), name, (void **)&(CAT(real_, name))); \
    CLOCK_END_RECORD                                  \
}                                                     \
type name(args)

#define MAKE_COUNTER_TEMPLATE(prefix, type, name, args...) \
CAT3(MAKE_, prefix, _TEMPLATE)(type, name, args) {         \
    check_count_intercepted(CAT3(prefix, _, name));

#define CALL(name, args...) return CAT(real_, name)(args); }

#endif //MYSYSCALL_COMMON_H
