//
// Created by tangruize on 22-5-14.
//

#ifndef MYSYSCALL_MYSYSCALL_H
#define MYSYSCALL_MYSYSCALL_H

#ifdef __linux__
#define SYSCALL_FUNC_TYPE long
#define SYSCALL_FUNC_THROW __THROW
#elif defined(__unix__)
#define SYSCALL_FUNC_TYPE int
#define SYSCALL_FUNC_THROW
#endif

typedef SYSCALL_FUNC_TYPE (*syscall_func_t)(SYSCALL_FUNC_TYPE number, ...);
//int _my_syscall6(int n, long a1, long a2, long a3, long a4, long a5, long a6);
SYSCALL_FUNC_TYPE syscall(SYSCALL_FUNC_TYPE number, ...) SYSCALL_FUNC_THROW;

extern syscall_func_t _syscall_;

#endif //MYSYSCALL_MYSYSCALL_H
