//
// Created by tangruize on 22-5-17.
//

#ifndef MYSYSCALL_MYSENDFILE_H
#define MYSYSCALL_MYSENDFILE_H

ssize_t sendfile(int out_fd, int in_fd, off_t *offset, size_t count);

#endif //MYSYSCALL_MYSENDFILE_H
