#pragma once

#ifdef ECRS_IMPLEMENTATION
#define FP_IMPLEMENTATION
#endif

#include <fp/hash/dictionary.hpp>
#include <fp/hash/fnv1a.hpp>

#include <stdexcept>

#include <typeinfo>
#ifdef __GNUC__
	#include <new>
	#include <cxxabi.h>
#endif

namespace ecrs {
#ifndef ecrs_DISABLE_STRING_COMPONENT_LOOKUP
	using ForwardPair = std::pair<fp::string, size_t>;
	using ReversePair = std::pair<size_t, fp::string>;

	fp_hashmap(ForwardPair)& ecrs_get_forward_map() noexcept
#ifdef ECRS_IMPLEMENTATION
	{
		static fp::dictionary<fp::string, size_t, fp::fnv1a<fp::string>> map;
		return map.raw;
	}
#else
		;
#endif

	fp_hashmap(ReversePair)& ecrs_get_reverse_map() noexcept
#ifdef ECRS_IMPLEMENTATION
	{
		static fp::dictionary<size_t, fp::string, fp::fnv1a<size_t>> map;
		return map.raw;
	}
#else
		;
#endif
#endif // ecrs_DISABLE_STRING_COMPONENT_LOOKUP

	extern "C" {
		size_t ecrs_get_next_component_id() noexcept
#ifdef ECRS_IMPLEMENTATION
		{
			static size_t id = 0;
			return id++;
		}
#else
		;
#endif

#ifndef ecrs_DISABLE_STRING_COMPONENT_LOOKUP
		size_t ecrs_component_id_from_name_view(const fp_string_view view, bool create_if_not_found = true) noexcept
#ifdef ECRS_IMPLEMENTATION
		{
			bool free = false;
			fp_string name = fp_string_view_make_dynamic(view); // TODO: Is there a way to skip the allocation here?
			ForwardPair lookup{name, 0};
			if(!fp_hash_map_contains(ForwardPair, ecrs_get_forward_map(), lookup)) {
				if(create_if_not_found) {
					size_t id = ecrs_get_next_component_id();
					lookup.second = id;
					fp_hash_map_insert(ForwardPair, ecrs_get_forward_map(), lookup);
					ReversePair reverse{id, name};
					fp_hash_map_insert(ReversePair, ecrs_get_reverse_map(), reverse);
					return id;
				} else {
					fp_string_free(name);
					return -1;
				}
			} else free = true;

			auto out = fp_hash_map_find(ForwardPair, ecrs_get_forward_map(), lookup)->second;
			if (free) fp_string_free(name);
			return out;
		}
#else
		;
#endif
		inline size_t ecrs_component_id_from_name(const fp_string str, bool create_if_not_found = true) noexcept {
			return ecrs_component_id_from_name_view(fp_string_to_view_const(str), create_if_not_found);
		}

		const fp_string ecrs_component_id_name(size_t componentID) noexcept
#ifdef ECRS_IMPLEMENTATION
		{
			ReversePair lookup{componentID, nullptr};
			auto res = fp_hash_map_find(ReversePair, ecrs_get_reverse_map(), lookup);
			if(res == nullptr) return nullptr;
			return res->second.raw;
		}
#else
		;
#endif

		void ecrs_component_id_free_maps() noexcept
#ifdef ECRS_IMPLEMENTATION
		{
			fp_hash_map_free_finalize_and_null(ForwardPair, ecrs_get_forward_map());
			fp_hash_map_free_finalize_and_null(ReversePair, ecrs_get_reverse_map());
		}
#else
		;
#endif
#endif // ecrs_DISABLE_STRING_COMPONENT_LOOKUP
	}

#ifndef ecrs_DISABLE_STRING_COMPONENT_LOOKUP
	inline void component_id_free_maps() noexcept { ecrs_component_id_free_maps(); }
#endif // ecrs_DISABLE_STRING_COMPONENT_LOOKUP

	template<typename T>
	fp_string get_type_name(T reference = {}) {
#ifdef __GNUC__
		int status;
		char* name = abi::__cxa_demangle(typeid(T).name(), 0, 0, &status);
		fp_string out = fp_string_promote_literal(name);
		free(name);
		switch(status) {
		break; case -1: throw std::bad_alloc();
		break; case -2: throw std::invalid_argument("mangled_name is not a valid name under the C++ ABI mangling rules.");
		break; case -3: throw std::invalid_argument("Type demangling failed, an argument is invalid");
		break; default: return out;
		}
#else
		return fp_string_promote_literal(typeid(T).name());
#endif
	}

	template<typename T, size_t Unique = 0>
	size_t& get_global_component_id_private(T reference = {}) noexcept {
		static size_t id = ecrs_get_next_component_id();
		return id;
	}

	// Warning: This function is very expensive (~5 microseconds vs ~350 nanoseconds) the first time it is called (for a new type)!
	template<typename T, size_t Unique = 0>
	size_t get_global_component_id(T reference = {}) noexcept {
		auto id = get_global_component_id_private<T, Unique>();
#ifndef ecrs_DISABLE_STRING_COMPONENT_LOOKUP
		static bool once = [id]{
			auto name = get_type_name<T>();
			if constexpr(Unique > 0) {
				fp_string num = fp_string_format("%u", Unique);
				fp_string_concatenate_inplace(name, num);
				fp_string_free(num);
			}
			ForwardPair forward{name, id};
			fp_hash_map_insert(ForwardPair, ecrs_get_forward_map(), forward);
			ReversePair reverse{id, name};
			fp_hash_map_insert(ReversePair, ecrs_get_reverse_map(), reverse);
			return false;
		}();
#endif
		return id;
	}

} // ecrs::ecs