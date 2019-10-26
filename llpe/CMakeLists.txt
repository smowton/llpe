cmake_minimum_required(VERSION 2.8)

find_package(LLVM REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

add_definitions("-std=c++11")

# RTTI-ness must match the LLVM we're building against.
if(NOT ${LLVM_ENABLE_RTTI})
  add_definitions("-fno-rtti")
endif()

add_definitions(${LLVM_DEFINITIONS})

include_directories(${LLVM_INCLUDE_DIRS} include)

add_subdirectory(main)
add_subdirectory(driver)
add_subdirectory(utils)
