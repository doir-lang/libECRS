#ifndef __LIB_ECRS_COMPONENT_REGISTRY_H__
#define __LIB_ECRS_COMPONENT_REGISTRY_H__

#ifdef ECRS_IMPLEMENTATION
	#ifdef __cplusplus
		#include "component_registry.hpp"
	#else
		#error "The implementation of the component registry requires a C++ compiler!"
	#endif
#endif

#include <fp/string.h>
#include <fp/hash.h>

struct ecrs_registry_forward_lookup_pair {
	fp_string name;
	size_t id;
};

fp_hashtable(ecrs_registry_forward_lookup_pair)* ecrs_registry_get_forward_map()
#ifdef ECRS_IMPLEMENTATION
{
	return (fp_hashtable(ecrs_registry_forward_lookup_pair)*)ecrs::registry::get_forward_map();
}
#else
;
#endif

struct ecrs_registry_reverse_lookup_pair {
	size_t id;
	fp_string name;
};

fp_hashtable(ecrs_registry_reverse_lookup_pair)* ecrs_registry_get_reverse_map()
#ifdef ECRS_IMPLEMENTATION
{
	return (fp_hashtable(ecrs_registry_reverse_lookup_pair)*)ecrs::registry::get_reverse_map();
}
#else
;
#endif

struct ecrs_registry_size_lookup_pair {
	size_t id;
	size_t size;
};

fp_hashtable(ecrs_registry_size_lookup_pair)* ecrs_registry_get_size_map()
#ifdef ECRS_IMPLEMENTATION
{
	return (fp_hashtable(ecrs_registry_size_lookup_pair)*)ecrs::registry::get_size_map();
}
#else
;
#endif

size_t ecrs_registry_next_component_id()
#ifdef ECRS_IMPLEMENTATION
{
	return ecrs::registry::next_component_id();
}
#else
;
#endif

size_t ecrs_register_type(fp_string name, size_t component_id, size_t type_size)
#ifdef ECRS_IMPLEMENTATION
{
	return ecrs::registry::register_type(name, component_id, type_size);
}
#else
;
#endif

size_t ecrs_lookup_component_id(fp_string_view name)
#ifdef ECRS_IMPLEMENTATION
{
	return ecrs::registry::lookup_component_id(name);
}
#else
;
#endif

size_t ecrs_lookup_component_size(size_t component_id)
#ifdef ECRS_IMPLEMENTATION
{
	return ecrs::registry::lookup_component_size(component_id);
}
#else
;
#endif

#endif