//
// Created by tangruize on 22-5-14.
//

#ifndef MYSYSCALL_MYCLOSE_H
#define MYSYSCALL_MYCLOSE_H

typedef long (*syscall_func_t)(long number, ...);
extern syscall_func_t _syscall_;

// long _my_syscall6(long n, long a1, long a2, long a3, long a4, long a5, long a6);
long syscall(long number, ...) __THROW;

#endif //MYSYSCALL_MYCLOSE_H
