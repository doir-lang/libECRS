cmake_minimum_required(VERSION 3.21)
project(libECRS C CXX)

include(FetchContent)

if(NOT TARGET libfp)
    message(STATUS "Fetching libfp...")

	FetchContent_Declare(
		fetch_libfp
		GIT_REPOSITORY https://github.com/doir-lang/libfp.git
		GIT_TAG main
		# GIT_TAG Hash
	)

    FetchContent_MakeAvailable(libfp)
endif()


add_executable(tst-ecrs hello.cpp)
target_link_libraries(tst-ecrs PUBLIC libfp)
set_target_properties(tst-ecrs PROPERTIES CXX_STANDARD 23)
set_target_properties(tst-ecrs PROPERTIES C_STANDARD 23)
