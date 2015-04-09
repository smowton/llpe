cmake_minimum_required(VERSION 2.8)

find_package(LLVM REQUIRED CONFIG)

add_definitions("-std=c++11")

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS} include)

add_subdirectory(main)