//
// Created by fedora on 6/6/22.
//

#include "common.h"
#include "mytime.h"
#include "timing.h"

#ifdef __linux__
#define TIME_NR_NAME CUR_SYSCALL
#define TEMPLATE MAKE_SYS_TEMPLATE
#elif defined(__unix__)
#define TIME_NR_NAME LIB_time
#define TEMPLATE MAKE_LIB_TEMPLATE
#endif

TEMPLATE(time_t, time, time_t *tloc) {
    CLOCK_START_RECORD;
    if (!check_count_intercepted(TIME_NR_NAME))
        return real_time(tloc);
    struct timespec mono = increase_time(NULL);
    struct timespec real_current_time = get_real_time_after(&mono);
    time_t ret = real_current_time.tv_sec;
    if (tloc) {
        if (real_time(tloc) == -1)
            return -1;
        *tloc = ret;
    }
//    count_concerned(TIME_NR_NAME);
    LOG_INTERCEPTED(TIME_NR_NAME, "ret %ld, time(tloc: %p)", ret, tloc);
    CLOCK_END_RECORD;
    return ret;
}
