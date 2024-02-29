# Library build :
#         mkdir build && cd build && cmake ..
#         make

cmake_minimum_required(VERSION 3.7.2)

project(DaosRaft C)

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

add_library(DaosRaft STATIC ${RAFT_SOURCE_FILES})
target_compile_options(DaosRaft PRIVATE -g -Wall -Wextra)
target_include_directories(DaosRaft PRIVATE include)

add_library(DaosRaft_shared SHARED ${RAFT_SOURCE_FILES})
target_include_directories(DaosRaft_shared PRIVATE include)
set_property(TARGET DaosRaft_shared PROPERTY POSITION_INDEPENDENT_CODE ON)
target_compile_options(DaosRaft_shared PRIVATE -g -Wall -Wextra)
# ------------------------------ C Tests End --------------------------------- #

