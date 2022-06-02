cmake_minimum_required(VERSION 3.10)
project(cpp)

set(CMAKE_CXX_STANDARD 17)
include(CheckIPOSupported)
check_ipo_supported(RESULT result)
if(result)
    set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()

SET(PROFILE_GENERATE FALSE)
SET(PROFILE_USE FALSE)
set(MYAPP_PGO "")

if (PROFILE_GENERATE)
	set(MYAPP_PGO "-fprofile-generate")
endif()
if (PROFILE_USE)
	set(MYAPP_PGO "-fprofile-use")
endif()

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${MYAPP_PGO}")
set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} ${MYAPP_PGO}")
set(CMAKE_MODULE_LINKER_FLAGS "${CMAKE_MODULE_LINKER_FLAGS} ${MYAPP_PGO}")
SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++1z -Wall -O3 -march=native ${MYAPP_PGO}")

add_subdirectory(../external/EvalMaxSAT/lib/EvalMaxSAT EvalMaxSAT)
add_subdirectory(../external/EvalMaxSAT/lib/glucose glucose)
add_subdirectory(../external/EvalMaxSAT/lib/MaLib MaLib)

#add_compile_definitions(FIXRANDOM)

set(localLibs
        MaLib
        EvalMaxSAT
        glucose
        )
include_directories(../external/EvalMaxSAT/lib/EvalMaxSAT/src)
include_directories(../external/EvalMaxSAT/lib/MaLib/src)
include_directories(../external/EvalMaxSAT/lib/glucose/src)

add_executable(cpp main.cpp graph.h dfvs.h preprocessing.h ms_hs.h sat_encode.h heuristic.h bb.h)
target_link_libraries (cpp LINK_PUBLIC glucose MaLib EvalMaxSAT)
