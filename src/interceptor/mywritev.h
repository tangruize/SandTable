//
// Created by tangruize on 22-5-15.
//

#ifndef MYSYSCALL_MYWRITEV_H
#define MYSYSCALL_MYWRITEV_H

#include <sys/uio.h>

ssize_t writev(int fd, const struct iovec *iov, int iovcnt);

#endif //MYSYSCALL_MYWRITEV_H
