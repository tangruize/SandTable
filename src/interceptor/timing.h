//
// Created by fedora on 5/31/22.
//

#ifndef MYSYSCALL_TIMING_H
#define MYSYSCALL_TIMING_H

#include <time.h>
#include <pthread.h>

#define S_TO_NS  1000000000
#define US_TO_NS 1000

extern int resolution_increment;
extern struct timespec resolution;
extern struct timespec startup_realtime;
extern struct timespec prev_monotonic;
extern volatile struct timespec curr_monotonic;
extern struct timespec system_startup_monotonic;

extern clock_t first_clock, overhead_clock;
extern pthread_mutex_t clock_mutex;

struct timespec set_time_increment(long tv_nsec);
struct timespec increase_time(struct timespec *increment);
struct timespec get_real_time_after(struct timespec *mono);

#define CLOCK_START_RECORD clock_t start_clock = clock(); \
    if (first_clock == 0) first_clock = start_clock;

#define CLOCK_END_RECORD pthread_mutex_lock(&clock_mutex); \
    clock_t clocks = clock() - start_clock; \
    overhead_clock += clocks; \
    pthread_mutex_unlock(&clock_mutex);

#define CLOCK_START_RECORD2 clock_t start_clock2 = clock();
#define CLOCK_END_RECORD2 pthread_mutex_lock(&clock_mutex); \
    clock_t clocks2 = clock() - start_clock2; \
    overhead_clock += clocks2; \
    pthread_mutex_unlock(&clock_mutex);


#endif //MYSYSCALL_TIMING_H
