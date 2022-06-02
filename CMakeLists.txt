cmake_minimum_required(VERSION 3.10)
project(dfvs)

set(CMAKE_CXX_STANDARD 17)


include(CheckIPOSupported)
check_ipo_supported(RESULT result)
if(result)
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()

set(MYAPP_PGO "")
SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++1z -Wall -O3 -march=native")

set(CMAKE_BUILD_TYPE Release)
add_compile_definitions(VERBOSITY=0)
add_subdirectory(external/EvalMaxSAT/lib/EvalMaxSAT EvalMaxSAT)
add_subdirectory(external/EvalMaxSAT/lib/glucose glucose)
add_subdirectory(external/EvalMaxSAT/lib/MaLib MaLib)
set(localLibs
        MaLib
        EvalMaxSAT
        glucose
        )
include_directories(external/EvalMaxSAT/lib/EvalMaxSAT/src)
include_directories(external/EvalMaxSAT/lib/MaLib/src)
include_directories(external/EvalMaxSAT/lib/glucose/src)

add_executable(dfvs cpp/main.cpp cpp/graph.h cpp/dfvs.h cpp/preprocessing.h cpp/ms_hs.h)
target_link_libraries (dfvs LINK_PUBLIC glucose MaLib EvalMaxSAT)

