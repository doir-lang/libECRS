#pragma once

#include "context.hpp"
#include "storage.hpp"
#include <span>
#include <type_traits>

namespace ecrs {
	struct relation_base {}; // Used for constraints

	struct term {
		bool is_var;
		union { entity_t constant; size_t var_id; };

		term() : is_var(true), var_id(0) {}
		/*implicit*/ term(entity_t e) : is_var(false), constant(e) {}
		// /*implicit*/ term(var v) : is_var(true), var_id(v.id) {}
	};

	// Base
	template<size_t N = std::dynamic_extent, bool CAN_BE_TERM = false>
	struct relation : public relation_base {
		using maybe_term = std::conditional_t<CAN_BE_TERM, term, entity_t>;
		constexpr static bool can_be_term = CAN_BE_TERM;
		std::array<maybe_term, N> related;

		constexpr relation() {}
		constexpr relation(std::array<maybe_term, N> a): related(a) {}
		constexpr relation(std::initializer_list<maybe_term> initializer) {
			assert(initializer.size() <= N);
			auto init = initializer.begin();
			for(size_t i = 0; i < initializer.size(); ++i, ++init)
				related[i] = *init;
		}
		relation(relation&&) = default;
		relation(const relation&) = default;
		relation& operator=(relation&&) = default;
		relation& operator=(const relation&) = default;

		static void swap_entities(relation& self, const context&, entity_t a, entity_t b) {
			for(auto& e: self.related)
				if(e == a) e = b;
				else if(e == b) e = a;
		}
	};
	template<bool CAN_BE_TERM>

	struct relation<std::dynamic_extent, CAN_BE_TERM> : public relation_base {
		using maybe_term = std::conditional_t<CAN_BE_TERM, term, entity_t>;
		constexpr static bool can_be_term = CAN_BE_TERM;
		std::vector<maybe_term> related;

		relation() {}
		relation(std::vector<maybe_term> a): related(a) {}
		relation(std::initializer_list<maybe_term> e) : related(e) {}
		relation(relation&&) = default;
		relation(const relation&) = default;
		relation& operator=(relation&&) = default;
		relation& operator=(const relation&) = default;

		static void swap_entities(relation& self, const context&, entity_t a, entity_t b) {
			for(auto& e: self.related)
				if(e == a) e = b;
				else if(e == b) e = a;
		}
	};

}
