#pragma once

#include "ecs.hpp"

#include <format>

namespace ecrs {
	inline namespace relational {
		struct TrivialRelationalModule;
	}

	struct Entity {
	protected:
		thread_local static TrivialModule* current_module;

	public:
		static void set_current_module(TrivialModule& module) noexcept {
			current_module = &module;
		}
		static const TrivialModule* get_current_module() noexcept {
			return current_module;
		}

		entity_t entity = invalid_entity;
		operator entity_t() const { return entity; }

		Entity() : entity(invalid_entity) {}
		Entity(entity_t e) : entity(e) {}
		Entity(const Entity&) = default;
		Entity(Entity&&) = default;
		Entity& operator=(const Entity&) = default;
		Entity& operator=(Entity&&) = default;
		friend std::strong_ordering operator<=>(Entity a, Entity b) { return a.entity <=> b.entity; };
		// bool operator==(Entity o) const { return entity == o.entity; }

		Entity operator++(/*pre*/) { return ++entity; }
		Entity operator++(/*post*/int) { return entity++; }
		Entity operator--(/*pre*/) { return --entity; }
		Entity operator--(/*post*/int) { return entity--; }

		inline static Entity create(TrivialModule& module) noexcept {
			return {module.create_entity()};
		}
		inline static Entity create() noexcept {
			assert(current_module != nullptr);
			return create(*current_module);
		}

		inline void release(TrivialModule& module, bool clear_memory = true) noexcept {
			module.release_entity(entity, clear_memory);
		}
		inline void release(bool clear_memory = true) noexcept {
			assert(current_module != nullptr);
			release(*current_module, clear_memory);
		}

		inline void* add_component(TrivialModule& module, size_t componentID, size_t element_size) noexcept {
			return module.add_component(entity, componentID, element_size);
		}
		inline void* add_component(size_t componentID, size_t element_size) noexcept {
			assert(current_module != nullptr);
			return add_component(*current_module, componentID, element_size);
		}

		template<typename T, size_t Unique = 0>
		inline T& add_component(TrivialModule& module) noexcept {
			return module.add_component<T, Unique>(entity);
		}
		template<typename T, size_t Unique = 0>
		inline T& add_component() noexcept {
			assert(current_module != nullptr);
			return add_component<T, Unique>(*current_module);
		}

		inline bool remove_component(TrivialModule& module, size_t componentID) noexcept {
			return module.remove_component(entity, componentID);
		}
		inline bool remove_component(size_t componentID) noexcept {
			assert(current_module != nullptr);
			return remove_component(*current_module, componentID);
		}

		template<typename T, size_t Unique = 0>
		inline bool remove_component(TrivialModule& module) noexcept {
			return module.remove_component<T, Unique>(entity);
		}
		template<typename T, size_t Unique = 0>
		inline bool remove_component() noexcept {
			assert(current_module != nullptr);
			return remove_component<T, Unique>(*current_module);
		}

		inline void* get_component(TrivialModule& module, size_t componentID) noexcept {
			return module.get_component(entity, componentID);
		}
		inline void* get_component(size_t componentID) noexcept {
			assert(current_module != nullptr);
			return get_component(*current_module, componentID);
		}

		inline const void* get_component(const TrivialModule& module, size_t componentID) const noexcept {
			return module.get_component(entity, componentID);
		}
		inline const void* get_component(size_t componentID) const noexcept {
			assert(current_module != nullptr);
			return get_component(*current_module, componentID);
		}

		template<typename T, size_t Unique = 0>
		inline T& get_component(TrivialModule& module) noexcept {
			return module.get_component<T, Unique>(entity);
		}
		template<typename T, size_t Unique = 0>
		inline T& get_component() noexcept {
			assert(current_module != nullptr);
			return get_component<T, Unique>(*current_module);
		}

		template<typename T, size_t Unique = 0>
		inline const T& get_component(const TrivialModule& module) const noexcept {
			return module.get_component<T, Unique>(entity);
		}
		template<typename T, size_t Unique = 0>
		inline const T& get_component() const noexcept {
			assert(current_module != nullptr);
			return get_component<T, Unique>(*current_module);
		}

		inline bool has_component(const TrivialModule& module, size_t componentID) const noexcept {
			return module.has_component(entity, componentID);
		}
		inline bool has_component(size_t componentID) const noexcept {
			assert(current_module != nullptr);
			return has_component(*current_module, componentID);
		}

		template<typename T, size_t Unique = 0>
		inline bool has_component(const TrivialModule& module) const noexcept {
			return module.has_component<T, Unique>(entity);
		}
		template<typename T, size_t Unique = 0>
		inline bool has_component() const noexcept {
			assert(current_module != nullptr);
			return has_component<T, Unique>(*current_module);
		}

		inline void* get_or_add_component(TrivialModule& module, size_t componentID, size_t element_size) noexcept {
			return module.get_or_add_component(entity, componentID, element_size);
		}
		inline void* get_or_add_component(size_t componentID, size_t element_size) noexcept {
			assert(current_module != nullptr);
			return get_or_add_component(*current_module, componentID, element_size);
		}

		template<typename T, size_t Unique = 0>
		inline T& get_or_add_component(TrivialModule& module) noexcept {
			return module.get_or_add_component<T, Unique>(entity);
		}
		template<typename T, size_t Unique = 0>
		inline T& get_or_add_component() noexcept {
			assert(current_module != nullptr);
			return get_or_add_component<T, Unique>(*current_module);
		}

#ifdef ECRS_RELATION_IS_AVAILABLE
		// NOTE: Defined in ecrs.hpp
		template<typename T, size_t Unique = 0>
		auto get_related_entities(const TrivialRelationalModule& module) const noexcept;
		template<typename T, size_t Unique = 0>
		auto get_related_entities() const noexcept;
#endif
	};

#ifdef ECRS_IMPLEMENTATION
	thread_local TrivialModule* Entity::current_module = nullptr;
#endif
}

template<>
struct std::formatter<ecrs::Entity, char> : public std::formatter<ecrs::entity_t, char> {
	using super = std::formatter<ecrs::entity_t, char>;

	template<class FmtContext>
	FmtContext::iterator format(ecrs::Entity e, FmtContext& ctx) const {
		return super::format(e.entity, ctx);
	}
};

template<>
struct std::hash<ecrs::Entity> : public std::hash<ecrs::entity_t> {
	using super = std::hash<ecrs::entity_t>;

	std::uint64_t operator()(const ecrs::Entity& e) const {
		return super::operator()(e);
	}
};