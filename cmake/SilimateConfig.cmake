# Always force disable GNU Readline, GPL trap library
set(YOSYS_ENABLE_READLINE OFF CACHE BOOL "" FORCE)
set(YOSYS_WITHOUT_READLINE ON CACHE BOOL "" FORCE)
# Silimate fork has Verific in top-level directory
set(YOSYS_VERIFIC_DIR ${PROJECT_SOURCE_DIR}/verific)
