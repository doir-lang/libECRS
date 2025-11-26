#define FP_IMPLEMENTATION
#define ECRS_IMPLEMENTATION
#include "context.hpp"
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

	ecrs::raii::context ctx;
	ecrs::context::entity e1, e2, e3;
	{
		e1 = ctx.make_current().add_entity();
		auto& c1 = e1.add_component<c>();
		c1.value = {1, 2};

		e2 = ctx.add_entity();
		auto& c2 = e2.add_component<c>();
		c2.value = {3, 4};

		e3 = ctx.add_entity();
		auto& c3 = e3.add_component<c>();
		c3.value = {5, 6};
	}

	e2.remove();

	for(ecrs::context::entity e: ctx.entities()) {
		auto comp = e.get_component<c>();
		std::cout << e << ": " << comp->x << ", " << comp->y << std::endl;
	}
}