//
// Created by tangruize on 22-5-17.
//

#ifndef MYSYSCALL_MYOPENAT_H
#define MYSYSCALL_MYOPENAT_H

#include <sys/types.h>

int openat(int dirfd, const char *pathname, int flags, mode_t mode);

#endif //MYSYSCALL_MYOPENAT_H
