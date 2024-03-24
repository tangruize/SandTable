//
// Created by fedora on 5/27/22.
//

#include "common.h"
#include "myclock_gettime.h"
#include "timing.h"

#include <time.h>
#include <unistd.h>

//MAKE_COUNTER_TEMPLATE(SYS, int, clock_gettime, clockid_t clockid, struct timespec *tp) {
//    CALL(clock_gettime, clockid, tp);
//}

MAKE_SYS_TEMPLATE(int, clock_gettime, clockid_t clockid, struct timespec *tp) {
    CLOCK_START_RECORD;
    if (!check_count_intercepted(CUR_SYSCALL))
        return real_clock_gettime(clockid, tp);
    struct timespec ret;
    ret = increase_time(NULL);
    switch (clockid) {
        case CLOCK_REALTIME:
#ifdef __linux__
        case CLOCK_REALTIME_COARSE:
#endif
            *tp = get_real_time_after(&ret);
            break;
        case CLOCK_MONOTONIC:
        case CLOCK_BOOTTIME:
#ifdef __linux__
        case CLOCK_MONOTONIC_COARSE:
        case CLOCK_MONOTONIC_RAW:
#endif
            tp->tv_sec = ret.tv_sec;
            tp->tv_nsec = ret.tv_nsec;
            break;
        default: {
            int real_ret = real_clock_gettime(clockid, tp);
            print_info("WARN: clock_gettime not implemented clockid: 0x%x, queried real clock_gettime returns %d {sec: %ld, nsec: %ld}\n",
                       clockid, real_ret, tp->tv_sec, tp->tv_nsec);
//            return real_ret;
            assert(0);
            print_info("WARN: exit now\n");
            _exit(1);
        }
    }
//    count_concerned(CUR_SYSCALL);
    LOG_INTERCEPTED(CUR_SYSCALL, "clock_gettime(clockid: %ld, timespec: {tv_sec: %ld, tv_nsec: %ld})", clockid, tp->tv_sec, tp->tv_nsec);
    CLOCK_END_RECORD;
    return 0;
}

__attribute__((constructor, unused))
static void init_start_time() {
    real_clock_gettime(CLOCK_MONOTONIC, &system_startup_monotonic);
}