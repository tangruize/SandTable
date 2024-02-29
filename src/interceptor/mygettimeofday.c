//
// Created by fedora on 5/30/22.
//

#include "common.h"
#include "mygettimeofday.h"
#include "timing.h"

//MAKE_COUNTER_TEMPLATE(SYS, int, gettimeofday, struct timeval *__restrict tv, void *__restrict tz) { CALL(gettimeofday, tv, tz); }

MAKE_SYS_TEMPLATE(int, gettimeofday, struct timeval *tv, GETTIMEOFDAY_TYPE tz) {
    CLOCK_START_RECORD;
    if (!check_count_intercepted(CUR_SYSCALL))
        return real_gettimeofday(tv, tz);
    if (tz) {
        real_gettimeofday(tv, tz);
    }
    struct timespec mono = increase_time(NULL);
    struct timespec rt = get_real_time_after(&mono);
    tv->tv_sec = rt.tv_sec;
    tv->tv_usec = rt.tv_nsec / US_TO_NS;
//    count_concerned(CUR_SYSCALL);
    LOG_INTERCEPTED(CUR_SYSCALL, "gettimeofday(timeval: {tv_sec: %ld, tv_usec: %ld}, tz: %p)", tv->tv_sec, tv->tv_usec, tz);
    CLOCK_END_RECORD;
    return 0;
}