cmake_minimum_required(VERSION 3.21)
project(libECRS C CXX)

include(FetchContent)

if(NOT TARGET libfp)
	message(STATUS "libECRS Fetching libfp...")

	FetchContent_Declare(
		fetch_libfp
		GIT_REPOSITORY https://github.com/doir-lang/libfp.git
		GIT_TAG main
	)

	FetchContent_MakeAvailable(fetch_libfp)
endif()

add_library(libecrs INTERFACE)
target_include_directories(libecrs INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(libecrs INTERFACE libfp)

add_executable(tst-ecrs hello.cpp)
target_link_libraries(tst-ecrs PUBLIC libecrs)
set_target_properties(tst-ecrs PROPERTIES CXX_STANDARD 23)
set_target_properties(tst-ecrs PROPERTIES C_STANDARD 23)
