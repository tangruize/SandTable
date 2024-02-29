//
// Created by tangruize on 22-5-13.
//

#include "common.h"
#include "config.h"
#include "mysyscall.h"
#include "mytime.h"

#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <sys/uio.h>

struct reg_func_t reg_func_dict[NR_REG_FUNC_DICT];
// the last one is used for summary info
unsigned NR_self_defined_func = NR_REG_FUNC_DICT - 2;

#define MAX_MSG_LEN      256
#define MAX_STR_LEN      64  // can contain IPv6
#define NR_STR_BUF       4

int is_inited = 0;

// in case the program close stderr (usually in destructors)
__attribute__((constructor, unused))  // unused is no use, just to make clion happy
static void init_common() {
    if (_syscall_ == NULL) {
        fprintf(stderr, "ERROR: _syscall_ symbol is null!\n");
        return;
    }
    CLOCK_START_RECORD;
    const char *program_path = getenv("PROGRAM_PATH");

#ifdef __linux__
#elif defined(__unix__)
    const char *program_invocation_name = getprogname();
#endif

    if (program_path && strcmp(program_invocation_name, program_path) != 0) {
        is_inited = 1;
        print_info_stderr("program_invocation_name is \"%s\", PROGRAM_PATH is \"%s\"\n", program_invocation_name, program_path);
        for (int i = 0; i < NR_REG_FUNC_DICT; i++) {
            reg_func_dict[i].state = (STATE_DISABLED | (reg_func_dict[i].state & STATE_LIBRARY));
        }
    }
    if (is_inited)
        return;
    is_inited = 1;
    if (MY_STDERR_FILENO != 2) {
        if (_syscall_(SYS_dup2, STDERR_FILENO, MY_STDERR_FILENO) == -1) {
            print_info_stderr("ERROR: dup2 failed: %s\n", strerror(errno));
        }
    }
    print_info("Program %s\n", program_invocation_name);
    init_config_file();
    strcpy(reg_func_dict[NR_REG_FUNC_DICT-1].name, "FUNCS");
    print_info("Init completed\n");
    CLOCK_END_RECORD;
}

// write vector to stderr directly using syscall number (in case writev is intercepted)
static void print_info_va(int flags, const char *format, va_list ap) {
    char msg[MAX_MSG_LEN];
    size_t size = vsnprintf(msg, sizeof(msg), format, ap);
    int fd = MY_STDERR_FILENO;
    if (flags & PRINT_STDERR)  // in case open_my_stderr() has not been called in constructors
        fd = STDERR_FILENO;
    struct iovec write_iov[] = {
            {"\033[1;31m" PRINT_PREFIX "\033[0m", 7+(sizeof(PRINT_PREFIX)-1)+4},  // bold red
            {msg, size}
    };
    if (flags & PRINT_NO_PROMPT)
        write_iov[0].iov_len = 0;
    else {
        static int is_tty = -1;
        if (is_tty == -1)
            is_tty = isatty(STDERR_FILENO);
        if (is_tty != 1) {
            write_iov[0].iov_base = (uint8_t *)(write_iov[0].iov_base) + 7;
            write_iov[0].iov_len = write_iov[0].iov_len - 7 - 4;
        }
    }
    if (_syscall_ != NULL) {
        _syscall_(SYS_writev, fd, write_iov, sizeof(write_iov)/sizeof(write_iov[0]));
    }
}

void print_info_internal(int flags, const char *format, ...) {
    va_list ap;
    va_start(ap, format);
    print_info_va(flags, format, ap);
    va_end(ap);
}

static size_t max_func_name_len = 0;

// register an intercepted function to log usages
void register_intercepted(unsigned nr_syscall, const char *name, void *func, void **real) {
    assert(nr_syscall < NR_REG_FUNC_DICT);
    void *default_func = dlsym(RTLD_DEFAULT, name);
    if (default_func != func) {
        *real = default_func;
        reg_func_dict[nr_syscall].real_func = *real;
        reg_func_dict[nr_syscall].fake_func = func;
        reg_func_dict[nr_syscall].state = STATE_DISABLED;
        print_info_stderr("Discharge (real %p) \"%s\"\n", *real, name);
    }
    else {
        *real = dlsym(RTLD_NEXT, name);
        reg_func_dict[nr_syscall].real_func = *real;
        reg_func_dict[nr_syscall].fake_func = func;
        reg_func_dict[nr_syscall].state = STATE_ENABLED;
        reg_func_dict[NR_REG_FUNC_DICT-1].concerned_count++;
        if (strlen(name) > max_func_name_len)
            max_func_name_len = strlen(name);
        print_info_stderr("Intercept (real %p -> fake %p) \"%s\"\n", *real, func, name);
    }
    strncpy(reg_func_dict[nr_syscall].name, name, sizeof(reg_func_dict[nr_syscall].name) - 1);
    if (nr_syscall == NR_self_defined_func + 1)
        reg_func_dict[nr_syscall].state |= STATE_LIBRARY;
    reg_func_dict[NR_REG_FUNC_DICT-1].count++;  // summary
}

// log usages of the intercepted syscall
#if defined(PRINT_FIRST_USAGE) || defined(PRINT_EVERY_USAGE)
void log_intercepted(unsigned nr_syscall, const char *format, ...)
#else
void log_intercepted(unsigned nr_syscall)
#endif
{
    if (!check_intercept(nr_syscall))
        return;
    count_concerned(nr_syscall);
//    reg_func_dict[nr_syscall].concerned_count++;
#if defined(PRINT_FIRST_USAGE) && !defined(PRINT_EVERY_USAGE)
    if (reg_func_dict[nr_syscall].count == 1)
#endif
#if defined(PRINT_FIRST_USAGE) || defined(PRINT_EVERY_USAGE)
    {
#if defined(NO_PRINT_TIME_SYSCALLS)
#ifdef __linux__
        if (nr_syscall == SYS_time)
            return;
#elif defined(__unix__)
        if (nr_syscall == LIB_time)
            return;
#endif
        if (nr_syscall == SYS_clock_gettime || nr_syscall == SYS_gettimeofday)
            return;
#endif
        va_list ap;
        va_start(ap, format);
        if (!format)
            format = reg_func_dict[nr_syscall].name;
        char format_buf[MAX_MSG_LEN];
        snprintf(format_buf, sizeof(format_buf), "Call %ld/%ld, %s\n",
                 (long)reg_func_dict[nr_syscall].concerned_count, (long)reg_func_dict[nr_syscall].count, format);
        print_info_va(0, format_buf, ap);
        va_end(ap);
    }
#endif
}

// restrict string argument length for logging
const char *restrict_str_internal(unsigned which __attribute__((unused)), const char *buf) {
#if defined(PRINT_FIRST_USAGE) || defined(PRINT_EVERY_USAGE)
    assert(which < NR_STR_BUF);
    static __thread char str_buf[NR_STR_BUF][MAX_STR_LEN+1] = { 0 };
    strncpy(str_buf[which], buf, MAX_STR_LEN);
    return str_buf[which];
#else
    return buf;
#endif
}

// restrict length and convert binary data to \x00~\xFF
const char *binary_str_internal(unsigned which __attribute__((unused)), const void *buf, size_t size __attribute__((unused))) {
#if defined(PRINT_FIRST_USAGE) || defined(PRINT_EVERY_USAGE)
    assert(which < NR_STR_BUF);
    static __thread char str_buf[NR_STR_BUF][MAX_STR_LEN+1] = { 0 };
    str_buf[which][0] = 0;
    size = (size < MAX_STR_LEN / 4) ? size : (MAX_STR_LEN / 4);
    for (size_t i = 0; i < size; i++)
        snprintf(&(str_buf[which][i*4]), 5, "\\x%02X", ((const char *)buf)[i]);
    return str_buf[which];
#else
    return buf;
#endif
}

// show statistics when unloading
__attribute__((destructor, unused))
//static  // clion says the for loop is endless if static
void print_statistics() {
#ifdef PRINT_STATISTICS
    print_info("STATISTICS\n");
    print_info_no_prompt("    %*s  %-*s %s\n", max_func_name_len, "NAME", 10, "CONCERNED", "TOTAL");
    for (int i = 0; i < NR_REG_FUNC_DICT; i++) {
        if (reg_func_dict[i].count || (reg_func_dict[i].state & STATE_ENABLED)) {
            if (reg_func_dict[i].name[0]) {
                print_info_no_prompt("  - %*s  %-*d %d\n", max_func_name_len, reg_func_dict[i].name,
                                     10, reg_func_dict[i].concerned_count, reg_func_dict[i].count);
            } else {
                print_info_no_prompt("  - %*d  %-*d %d\n", max_func_name_len, i,
                                     10, reg_func_dict[i].concerned_count, reg_func_dict[i].count);
            }
        }
    }
#endif
}

__thread int saved_errno;

// // show usage msg
// void __attribute__((unused)) my_entry() {
// #define USAGE_MSG "Usage: env LD_PRELOAD=/path/to/libmysyscall.so [" CONFIG_FILE_ENV "=CONFIG_FILE] COMMAND [ARGS]\n"
//     _syscall_(SYS_write, STDERR_FILENO, USAGE_MSG, sizeof(USAGE_MSG)-1);
//     _syscall_(SYS_exit, 1);
// }

// #ifndef LD_LOADER
// #define LD_LOADER "/lib64/ld-linux-x86-64.so.2"
// #endif
// const char ld_loader[] __attribute__((section(".interp"), unused)) = LD_LOADER;
