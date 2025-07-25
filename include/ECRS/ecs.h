#pragma once

#include <fp/string.h>

#ifdef ECRS_IMPLEMENTATION
	#ifndef __cplusplus
	#error The implementation of the C interface requires a C++ compiler!
	#endif

	#include "ecs.hpp"
	using namespace ecrs;

	extern "C" {
#else
	#ifdef __cplusplus
	extern "C" {
	#endif

	typedef size_t entity_t;

	size_t get_next_component_id();
	size_t ecrs_component_id_from_name_view(const fp_string_view view, bool create_if_not_found /*= true*/);
	size_t ecrs_component_id_from_name(const fp_string str, bool create_if_not_found /*= true*/);
	const fp_string ecrs_component_id_name(size_t componentID);
	void ecrs_component_id_free_maps();

	struct Storage;
	struct Module {
		fp_dynarray(fp_dynarray(size_t)) entity_component_indices;
		fp_dynarray(Storage) storages;
		fp_dynarray(entity_t) freelist;
		bool should_leak;
	};
#endif

#define ecrs_component_id_from_type(type) ecrs_component_id_from_name(#type)

Module ecrs_module_initialize()
#ifdef ECRS_IMPLEMENTATION
{ return {}; }
#else
;
#endif

void ecrs_module_free(Module* module)
#ifdef ECRS_IMPLEMENTATION
{ module->free(); }
#else
;
#endif

entity_t ecrs_module_create_entity(Module* module)
#ifdef ECRS_IMPLEMENTATION
{ return module->create_entity(); }
#else
;
#endif

bool ecrs_module_release_entity(Module* module, entity_t e, bool clearMemory /*= true*/)
#ifdef ECRS_IMPLEMENTATION
{ return module->release_entity(e, clearMemory); }
#else
;
#endif

void* ecrs_module_add_component(Module* module, entity_t e, size_t componentID, size_t element_size)
#ifdef ECRS_IMPLEMENTATION
{ return module->add_component(e, componentID, element_size); }
#else
;
#endif
#define ecrs_module_add_component_typed(type, module, e, componentID) ecrs_module_add_component((module), (e), (componentID), sizeof(type))

bool ecrs_module_remove_component(Module* module, entity_t e, size_t componentID)
#ifdef ECRS_IMPLEMENTATION
{ return module->remove_component(e, componentID); }
#else
;
#endif

void* ecrs_module_get_component(Module* module, entity_t e, size_t componentID)
#ifdef ECRS_IMPLEMENTATION
{ return module->get_component(e, componentID); }
#else
;
#endif

bool ecrs_module_has_component(Module* module, entity_t e, size_t componentID)
#ifdef ECRS_IMPLEMENTATION
{ return module->has_component(e, componentID); }
#else
;
#endif

#ifdef __cplusplus
} // extern "C"
#endif