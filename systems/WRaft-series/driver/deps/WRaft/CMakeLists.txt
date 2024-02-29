# Library build :
#         mkdir build && cd build && cmake ..
#         make

cmake_minimum_required(VERSION 3.7.2)

project(WRaft C)

# ----------------------- Build Settings Start ------------------------------- #
set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)
# ------------------------ Build Settings End -------------------------------- #

# ----------------------------- C Tests Start -------------------------------- #

set(RAFT_SOURCE_FILES
        src/raft_log.c
        src/raft_server.c
        src/raft_node.c
        src/raft_server_properties.c)

add_library(WRaft STATIC ${RAFT_SOURCE_FILES})
target_compile_options(WRaft PRIVATE -g -Wall -Wextra)
target_include_directories(WRaft PRIVATE include)

add_library(WRaft_shared SHARED ${RAFT_SOURCE_FILES})
target_include_directories(WRaft_shared PRIVATE include)
set_property(TARGET WRaft_shared PROPERTY POSITION_INDEPENDENT_CODE ON)
target_compile_options(WRaft_shared PRIVATE -g -Wall -Wextra)
# ------------------------------ C Tests End --------------------------------- #

