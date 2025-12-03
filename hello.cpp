#define FP_IMPLEMENTATION
#define ECRS_IMPLEMENTATION
#include "component_registry.hpp"
#include "component_registry.h"

#include <iostream>

int main() {
	ecrs::register_components<int, float, fp::string_view>();
	std::cout << ecrs::lookup_component_id("fp::string_view") << std::endl;
	printf("%zu - ", ecrs_lookup_component_id(fp_string_view_from_literal("int")));

	auto sizes = ecrs_registry_get_size_map();
	ecrs_registry_size_lookup_pair key{.id = 1};
	key = *fpht_find(*sizes, key);
	printf("%zu\n", key.size);
}