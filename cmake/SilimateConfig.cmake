# Always force disable GNU Readline, GPL trap library
set(YOSYS_ENABLE_READLINE OFF CACHE BOOL "" FORCE)
set(YOSYS_WITHOUT_READLINE ON CACHE BOOL "" FORCE)
# Silimate fork has Verific in top-level directory
set(YOSYS_VERIFIC_DIR ${PROJECT_SOURCE_DIR}/verific)

add_library(verific INTERFACE)

# Homebrew's binutils ships libbfd but not libiberty, which backward-cpp's libbfd
# backend links against. When binutils happens to be installed, use_homebrew()
# puts it on the find path and backward-cpp prefers the libbfd backend, producing
# an unsatisfiable `-liberty` at link time. Hide binutils so backward-cpp selects
# the intended libdwarf backend (provided by the dwarfutils + libelf packages).
if (APPLE)
	list(FILTER CMAKE_FIND_ROOT_PATH EXCLUDE REGEX "binutils")
	unset(LIBBFD_LIBRARY CACHE)
	unset(LIBBFD_INCLUDE_DIR CACHE)
endif()

add_subdirectory(${PROJECT_SOURCE_DIR}/libs/backward-cpp)
option(YOSYS_WITHOUT_BACKWARD "Don't install backward-cpp's signal handler in yosys_setup" OFF)
if (YOSYS_WITHOUT_BACKWARD)
	add_compile_definitions(YOSYS_WITHOUT_BACKWARD)
endif()
