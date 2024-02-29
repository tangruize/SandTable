//
// Created by tangruize on 22-5-17.
//

#include "common.h"
#include "mysendfile.h"

MAKE_COUNTER_TEMPLATE(SYS, ssize_t, sendfile, int out_fd, int in_fd, off_t *offset, size_t count)
{ CALL(sendfile, out_fd, in_fd, offset, count); }
