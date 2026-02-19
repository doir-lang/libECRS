#pragma once
#include <fp/string.hpp>

#ifndef _MSC_VER
	#include <fp/hash.hpp>
	#define ECRS_HASH_MAP fp::hash_map
	#define ECRS_RAII_HASH_MAP fp::raii::hash_map
#else
	#include <unordered_map>
	#define ECRS_HASH_MAP std::unordered_map
	#define ECRS_RAII_HASH_MAP std::unordered_map

	namespace std {
		template<>
		struct hash<fp::raii::string> {
			uint64_t operator()(const fp::raii::string& s) const {
				auto view = s.full_view();
				return std::hash<std::string_view>{}({view.data(), view.size()});
			}
		};
	}
#endif
#include <limits>
#include <stdexcept>

#ifdef __GNUC__
#include <cxxabi.h>
#endif

namespace ecrs { inline namespace registry {

	ECRS_HASH_MAP<fp::raii::string, size_t>* get_forward_map()
	#ifdef ECRS_IMPLEMENTATION
	{
		static ECRS_RAII_HASH_MAP<fp::raii::string, size_t> map;
		return &map;
	}
	#else
	;
	#endif

	ECRS_HASH_MAP<size_t, fp::string::view>* get_reverse_map()
	#ifdef ECRS_IMPLEMENTATION
	{
		static ECRS_RAII_HASH_MAP<size_t, fp::string::view> map;
		return &map;
	}
	#else
	;
	#endif

	ECRS_HASH_MAP<size_t, size_t>* get_size_map()
	#ifdef ECRS_IMPLEMENTATION
	{
		static ECRS_RAII_HASH_MAP<size_t, size_t> map;
		return &map;
	}
	#else
	;
	#endif

	size_t next_component_id()
	#ifdef ECRS_IMPLEMENTATION
	{
		static size_t global_component_id = 0;
		return global_component_id++;
	}
	#else
	;
	#endif

	inline static size_t register_type(fp::raii::string name, size_t component_id, size_t type_size) {
		fp::string::view view = name.view_full();
		(*get_forward_map())[std::move(name)] = component_id;
		(*get_reverse_map())[component_id] = view;
		(*get_size_map())[component_id] = type_size;
		return component_id;
	}

	template<typename T>
	fp::raii::string get_type_name(T reference = {}) {
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
	size_t component_id(T reference = {}) {
		const static size_t component_id = register_type(get_type_name<T>(), next_component_id(), sizeof(T));
		return component_id;
	}

	template<typename... Ts>
	void register_components(){
		(component_id<Ts>() + ...);
	}

	inline static size_t lookup_component_id(fp::string::view name) {
		const auto& m = *get_forward_map();
		fp::auto_free key = name.make_dynamic();
		if(!m.contains(key)) return fp::not_found;
#ifdef _MSC_VER
		return m.at(name.make_dynamic());
#else
		return m[name.make_dynamic()];
#endif
	}

	inline static size_t lookup_component_size(size_t component_id) {
#ifdef _MSC_VER
		if (!get_size_map()->contains(component_id))
			return (std::numeric_limits<size_t>::max)();
		return get_size_map()->at(component_id);
#else
		return get_size_map()->get_or_default(component_id, (std::numeric_limits<size_t>::max)());
#endif
	}
}}
