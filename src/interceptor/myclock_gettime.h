//
// Created by fedora on 5/27/22.
//

#ifndef MYSYSCALL_MYCLOCK_GETTIME_H
#define MYSYSCALL_MYCLOCK_GETTIME_H

int clock_gettime(clockid_t clockid, struct timespec *tp);

#endif //MYSYSCALL_MYCLOCK_GETTIME_H
