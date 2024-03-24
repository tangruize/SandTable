//
// Created by tangruize on 22-5-17.
//

#include "common.h"
#include "mysendfile.h"

#ifdef __linux__
MAKE_COUNTER_TEMPLATE(SYS, ssize_t, sendfile, int out_fd, int in_fd, off_t *offset, size_t count)
{ CALL(sendfile, out_fd, in_fd, offset, count); }
#elif defined(__unix__)
ssize_t sendfile(int out_fd, int in_fd, off_t *offset, size_t count) {
    UNUSED(out_fd);
    UNUSED(in_fd);
    UNUSED(offset);
    UNUSED(count);
    return -1;
}
#endif

