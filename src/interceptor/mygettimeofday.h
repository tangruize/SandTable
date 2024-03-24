//
// Created by fedora on 5/30/22.
//

#ifndef MYSYSCALL_MYGETTIMEOFDAY_H
#define MYSYSCALL_MYGETTIMEOFDAY_H

#include <sys/time.h>

#ifdef __linux__
#define GETTIMEOFDAY_TYPE void *
#elif defined(__unix__)
#define GETTIMEOFDAY_TYPE struct timezone *
#endif

int gettimeofday(struct timeval *tv, GETTIMEOFDAY_TYPE tz);

#endif //MYSYSCALL_MYGETTIMEOFDAY_H
