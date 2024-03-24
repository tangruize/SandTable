cmake_minimum_required(VERSION 3.16)
project(interceptor C CXX)

set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 14)

add_compile_definitions(PRINT_EVERY_USAGE)
add_compile_definitions(PRINT_STATISTICS)
add_compile_definitions(NO_PRINT_TIME_SYSCALLS)
#add_compile_definitions(TIMING_USE_REAL)  // use real wall time as real time
add_compile_options(-O)  # optimize, such as inline
add_compile_options(-Wall -Wextra -Werror)  # no -Wpedantic, it does not permit named variadic macros

# config files
set(VERSION_FILE ${CMAKE_CURRENT_SOURCE_DIR}/version.map)
set(CONFIG_FILE ${CMAKE_CURRENT_SOURCE_DIR}/config.txt)

# target files
set(LIB_NAME interceptor)
set(RUN_SCRIPT ${CMAKE_CURRENT_BINARY_DIR}/run.sh)

# file order affects the init order (setting priorities of constructors may be better?)
add_library(${LIB_NAME} SHARED mysyscall.c mysyscall.h myclock_gettime.c myclock_gettime.h mymallocfree.c myopen.c myopen.h myclose.c myclose.h mysocket.c mysocket.h
        myaccept.c myaccept.h myconnect.c myconnect.h mysendto.c mysendto.h mysend.c mysend.h mywrite.c mywrite.h
        mysendmsg.c mysendmsg.h mysendfile.c mysendfile.h myopenat.c myopenat.h myaccept4.c myaccept4.h
        myrandom.c myrandom.h mygettimeofday.c mygettimeofday.h mytime.c mytime.h
        myclock_getres.c myclock_getres.h mysendmmsg.c mysendmmsg.h mywritev.c mywritev.h myrecv.c myrecv.h myrecvfrom.c myrecvfrom.h myrecvmsg.c myrecvmsg.h myread.c myread.h)
# common.c must after config.c, and common.c should be the last one to init
set_property(TARGET ${LIB_NAME} APPEND PROPERTY SOURCES timing.c timing.h state_collector.cpp state_collector.h router.cpp router.h config.cpp config.h common.c common.h)
# use version map to expose symbols
set_target_properties(${LIB_NAME} PROPERTIES LINK_DEPENDS "${VERSION_FILE}")
# --version-script: define global symbols to export
target_link_libraries(${LIB_NAME} "-Wl,--version-script,${VERSION_FILE}")
# generate a run script
add_custom_command(OUTPUT "${RUN_SCRIPT}"
        COMMAND sed -e 's,\$\${LIBRARY},${CMAKE_CURRENT_BINARY_DIR}/lib${LIB_NAME}.so,g'
                    -e 's,\$\${CONFIG},${CONFIG_FILE},g' "${CMAKE_CURRENT_SOURCE_DIR}/run.sh" > "${RUN_SCRIPT}"
        COMMAND chmod +x "${RUN_SCRIPT}"
        DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/run.sh" #"${CONFIG_FILE}"
        )
add_custom_target(run ALL DEPENDS "${RUN_SCRIPT}" ${LIB_NAME})
