cmake_minimum_required(VERSION 3.16)
project(controller CXX)

set(CMAKE_CXX_STANDARD 20)

add_compile_options(-Wall -Wextra -Werror -Wno-cast-function-type)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/cmake/")

find_package(gflags REQUIRED)
find_package(Readline REQUIRED)
find_package(ConcurrentQueue REQUIRED)

add_executable(controller main.cpp TcpSocket.cpp TcpSocket.h common.h ConfigFile.cpp ConfigFile.h
        TcpNetwork.cpp TcpNetwork.h Command.cpp Command.h Repl.cpp Repl.h
        Socket.cpp Socket.h RemoteControl.cpp RemoteControl.h Msg.cpp Msg.h
        UdpNetwork.h UdpNetwork.cpp UdpSocket.cpp UdpSocket.h)
target_link_libraries(controller PUBLIC
        gflags
        readline
        pthread
)
