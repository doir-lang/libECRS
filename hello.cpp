#define FP_IMPLEMENTATION
#define ECRS_IMPLEMENTATION
#include "storage.hpp"
#include "component_registry.h"

#include <iostream>

struct vec2 {
	float x, y;
};

using c = ecrs::with_entity<vec2>;
static_assert(ecrs::detail::has_swap_entities<c>);

int main() {
	ecrs::register_components<c, int, float, fp::string_view>();
	std::cout << ecrs::lookup_component_id("fp::string_view") << std::endl;
	printf("%zu - ", ecrs_lookup_component_id(fp_string_view_from_literal("int")));

	auto sizes = ecrs_registry_get_size_map();
	ecrs_registry_size_lookup_pair key{.id = 1};
	key = *fpht_find(*sizes, key);
	printf("%zu\n", key.size);

	fp::dynarray<fp::dynarray<size_t>> entity_component_indicies;
	entity_component_indicies.push_back(nullptr).push_back(0);
	entity_component_indicies.push_back(nullptr).push_back(1);

	ecrs::component_storage s(c{});
	s.get_or_allocate<c>(0) = {1, 2, 0};
	s.get_or_allocate<c>(1) = {3, 4, 1};
	s.swap<c>(entity_component_indicies, 0, 1);

	auto a = s.get<c>(0);
	std::cout << a.entity << std::endl;
	auto b  = s.get<c>(1);
	std::cout << b.entity << std::endl;
}