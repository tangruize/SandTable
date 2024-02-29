find_path(ConcurrentQueue_INCLUDE_DIR
        NAMES concurrentqueue/concurrentqueue.h)

mark_as_advanced(
        ConcurrentQueue_INCLUDE_DIR)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(ConcurrentQueue
        DEFAULT_MSG ConcurrentQueue_INCLUDE_DIR)
