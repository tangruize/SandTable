//
// Created by fedora on 6/6/22.
//

#ifndef MYSYSCALL_MYCLOCK_GETRES_H
#define MYSYSCALL_MYCLOCK_GETRES_H

#include <bits/types/clockid_t.h>
#include <bits/types/struct_timespec.h>

int clock_getres(clockid_t clockid, struct timespec *res);

#endif //MYSYSCALL_MYCLOCK_GETRES_H
