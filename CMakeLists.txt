cmake_minimum_required(VERSION 3.21)
project(libecrs LANGUAGES C CXX)

include(CMakeDependentOption)

option(ECRS_ENABLE_TESTS "Weather or not Unit Tests should be built." ${PROJECT_IS_TOP_LEVEL})
cmake_dependent_option(ECRS_ENABLE_PROFILING "Weather profiling should be enabled for the tests." ${PROJECT_IS_TOP_LEVEL} ecrs_ENABLE_TESTS OFF)
set(FP_ENABLE_TESTS ${ECRS_ENABLE_TESTS})

add_subdirectory(libfp)

add_library(libecrs INTERFACE)
add_library(libecrs::ecs ALIAS libecrs)
target_include_directories(libecrs INTERFACE include)
target_link_libraries(libecrs INTERFACE libfp)


if(${ECRS_ENABLE_TESTS} AND ${FP_ENABLE_TESTS})
	add_executable(tst-libecrs tests/0_ECS.cpp tests/1_ECRS.cpp)
	target_link_libraries(tst-libecrs PUBLIC doctest libecrs)
	set_property(TARGET tst-libecrs PROPERTY CXX_STANDARD 23)
	set_property(TARGET tst-libecrs PROPERTY C_STANDARD 23)
endif()
