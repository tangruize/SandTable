//
// Created by fedora on 6/6/22.
//

#ifndef MYSYSCALL_MYTIME_H
#define MYSYSCALL_MYTIME_H

#include <time.h>

time_t time(time_t *tloc);

#ifdef __linux__
#elif defined(__unix__)
extern unsigned LIB_time;
#endif

#endif //MYSYSCALL_MYTIME_H
