#define FP_IMPLEMENTATION
#define ECRS_IMPLEMENTATION
#include "component_registry.hpp"

#include <iostream>

int main() {
	ecrs::register_components<int, float, fp::string_view>();
	std::cout << ecrs::lookup_component_id("fp::string_view") << std::endl;
}