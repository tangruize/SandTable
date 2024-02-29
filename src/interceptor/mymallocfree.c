//
// Created by tangruize on 22-5-16.
//

#include "common.h"

// examples to count dynamic memory operations

// fake buffer for dlsym() while constructing
#define MALLOC_SIZE 81920  // may be a suitable size for init (dlsym() uses malloc), smaller causes SIGSEGV
static uint8_t malloc_buffer[MALLOC_SIZE];
static uint8_t *malloc_ptr = malloc_buffer;

MAKE_LIB_TEMPLATE(void, free, void *ptr) {
    if ((ptr >= (void *)malloc_buffer && ptr < (void *)&(malloc_buffer[MALLOC_SIZE])))
        return;
//    if (!is_inited)
//        return;
    check_count_intercepted(LIB_free);
    return real_free(ptr);
}

MAKE_LIB_TEMPLATE(void *, malloc, size_t size) {
    if (!is_inited) {
        uint8_t *ptr = malloc_ptr;
        malloc_ptr += (size & (~0xf)) + 0x10;
        return ptr;
    }
    check_count_intercepted(LIB_malloc);
    return real_malloc(size);
}

MAKE_LIB_TEMPLATE(void *, calloc, size_t nmemb, size_t size) {
    if (!is_inited) {
        uint8_t *ptr = malloc_ptr;
        malloc_ptr += ((nmemb * size) & (~0xf)) + 0x10;  // aligned to 16 boundary
        return ptr;
    }
    check_count_intercepted(LIB_calloc);
    return real_calloc(nmemb, size);
}

MAKE_COUNTER_TEMPLATE(LIB, void *, realloc, void *ptr, size_t size) { CALL(realloc, ptr, size); }
// reallocarray is a GNU extenstion and is rarely used
//MAKE_COUNTER_TEMPLATE(LIB_, void *, reallocarray, void *ptr, size_t nmemb, size_t size) { CALL(reallocarray, ptr, nmemb, size); }
