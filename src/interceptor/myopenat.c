//
// Created by tangruize on 22-5-17.
//

#include "common.h"
#include "myopenat.h"

MAKE_COUNTER_TEMPLATE(SYS, int, openat, int dirfd, const char *pathname, int flags, mode_t mode)
{ CALL(openat, dirfd, pathname, flags, mode); }