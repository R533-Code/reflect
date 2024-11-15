cmake_minimum_required(VERSION 3.12)
project(Colt-Reflect LANGUAGES CXX VERSION 0.0.1.0)
# Set C++20 standard
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

file(GLOB_RECURSE ReflectHeaders CONFIGURE_DEPENDS "include/*.h")
file(GLOB_RECURSE ReflectUnitsT CONFIGURE_DEPENDS "test/*.cpp")

if (MSVC)
  add_compile_options(/Zc:preprocessor)
endif()

add_library(ColtReflect INTERFACE "${ReflectHeaders}")
target_include_directories(ColtReflect INTERFACE "include/")
add_library(clt::reflect ALIAS ColtReflect)

add_executable(ColtReflectTest "${ReflectHeaders}" "${ReflectUnitsT}")
target_link_libraries(ColtReflectTest PUBLIC clt::reflect)