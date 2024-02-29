cmake_minimum_required(VERSION 3.16)
project(tlpi)

set(CMAKE_C_STANDARD 99)
add_compile_options(-Wall -Wextra -Werror)

add_library(tlpi inet_sockets.c inet_sockets.h tlpi_hdr.h)
