#pragma once

#include "context.hpp"
#include <span>

namespace ecrs {
	struct relation_base {}; // Used for constraints

	// Base
	template<size_t N = std::dynamic_extent, bool CAN_BE_TERM = false>
	struct relation : public relation_base {
		constexpr static bool can_be_term = CAN_BE_TERM;
		std::array<entity_t, N> related;

		constexpr relation() {}
		constexpr relation(std::array<entity_t, N> a): related(a) {}
		constexpr relation(std::initializer_list<entity_t> initializer) {
			assert(initializer.size() <= N);
			auto init = initializer.begin();
			for(size_t i = 0; i < initializer.size(); ++i, ++init)
				related[i] = *init;
		}
		relation(relation&&) = default;
		relation(const relation&) = default;
		relation& operator=(relation&&) = default;
		relation& operator=(const relation&) = default;
	};
	template<bool CAN_BE_TERM>

	struct relation<std::dynamic_extent, CAN_BE_TERM> : public relation_base {
		constexpr static bool can_be_term = CAN_BE_TERM;
		std::vector<entity_t> related;

		relation() {}
		relation(std::vector<entity_t> a): related(a) {}
		relation(std::initializer_list<entity_t> e) : related(e) {}
		relation(relation&&) = default;
		relation(const relation&) = default;
		relation& operator=(relation&&) = default;
		relation& operator=(const relation&) = default;
	};

}
