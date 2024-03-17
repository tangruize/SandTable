cmake_minimum_required(VERSION 3.16)
project(raftdriver)

set(CMAKE_CXX_STANDARD 20)
add_compile_options(-Wall -Wextra -Werror -Wno-unused-parameter -Wno-unused-function)

add_subdirectory(deps/WRaft EXCLUDE_FROM_ALL)
add_subdirectory(deps/RedisRaft EXCLUDE_FROM_ALL)
add_subdirectory(deps/DaosRaft EXCLUDE_FROM_ALL)
add_subdirectory(tlpi EXCLUDE_FROM_ALL)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/cmake/")

find_package(gflags REQUIRED)
find_package(Readline REQUIRED)

set(DRIVER_SOURCES main.cpp Network.cpp Network.h Config.cpp Config.h Repl.cpp Repl.h Raft.h common.h common.cpp Node.cpp Node.h TcpNetwork.cpp TcpNetwork.h)

macro(define_driver name)
    add_executable(${name}Driver deps/${name}.cpp ${DRIVER_SOURCES})
    target_link_libraries(${name}Driver ${name} readline gflags tlpi)
endmacro()

define_driver(WRaft)
define_driver(RedisRaft)
define_driver(DaosRaft)
