find_path(Readline_INCLUDE_DIR
        NAMES readline/readline.h)

find_library(Readline_LIBRARY
        NAMES readline)

mark_as_advanced(
        Readline_INCLUDE_DIR
        Readline_LIBRARY
)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Readline
        DEFAULT_MSG Readline_INCLUDE_DIR Readline_LIBRARY)
