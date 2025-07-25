#pragma once

#include "ecs.hpp"
#define ECRS_RELATION_IS_AVAILABLE
#include "kanren.hpp"
#include "entity.hpp"

namespace ecrs { inline namespace relational {

	template<bool can_be_term>
	using entity_or_term = std::conditional_t<can_be_term, kanren::Term, Entity>;

	struct RelationBase {}; // Used for constraints

	// Base
	template<size_t N = std::dynamic_extent, bool CAN_BE_TERM = false>
	struct Relation : public RelationBase {
		constexpr static bool can_be_term = CAN_BE_TERM;
		std::array<entity_or_term<can_be_term>, N> related;

		constexpr Relation() {}
		constexpr Relation(std::array<entity_or_term<can_be_term>, N> a): related(a) {}
		constexpr Relation(std::initializer_list<entity_or_term<can_be_term>> initializer) {
			assert(initializer.size() <= N);
			auto init = initializer.begin();
			for(size_t i = 0; i < initializer.size(); ++i, ++init)
				related[i] = *init;
		}
		Relation(Relation&&) = default;
		Relation(const Relation&) = default;
		Relation& operator=(Relation&&) = default;
		Relation& operator=(const Relation&) = default;
	};
	template<bool CAN_BE_TERM>

	struct Relation<std::dynamic_extent, CAN_BE_TERM> : public RelationBase {
		constexpr static bool can_be_term = CAN_BE_TERM;
		std::vector<entity_or_term<can_be_term>> related;

		Relation() {}
		Relation(std::vector<entity_or_term<can_be_term>> a): related(a) {}
		Relation(std::initializer_list<entity_or_term<can_be_term>> e) : related(e) {}
		Relation(Relation&&) = default;
		Relation(const Relation&) = default;
		Relation& operator=(Relation&&) = default;
		Relation& operator=(const Relation&) = default;
	};

	struct TrivialRelationalModule : public TrivialModule {
		std::unordered_map<component_t, entity_t> component_lookup;
		kanren::State logic_state{this};

		Entity get_component_entity(component_t componentID) {
			if(component_lookup.contains(componentID)) return component_lookup[componentID];

			return component_lookup[componentID] = create_entity();
		}
		template<typename T, size_t Unique = 0>
		inline Storage& get_component_entity() noexcept { return get_component_entity(get_global_component_id<T, Unique>()); }

		std::optional<component_t> get_global_component_id_from_component_entity(entity_t e) {
			for(auto [c, ent]: component_lookup)
				if(e == ent)
					return c;
			return {};
		}

		template<std::derived_from<RelationBase> R>
		std::span<entity_or_term<R::can_be_term>> get_related_entities(entity_t e) {
			if(!has_component<R>()) return {};
			return get_component<R>().related;
		}

		kanren::Variable next_logic_variable() { return logic_state.next_variable(); }

		void free() {
			TrivialModule::free();
			// TODO: Free component_lookup
		}
	};

	struct RelationalModule : public TrivialRelationalModule {
		bool should_leak = false; // Useful when shutting down, if we are closing we can just leave memory cleanup to the operating system for a bit of added performance!

		RelationalModule() = default;
		RelationalModule(const RelationalModule&) = delete; // Storages need to become copyable to change this...
		RelationalModule(RelationalModule&& o) { *this = std::move(o); }
		RelationalModule& operator=(const RelationalModule& o) = delete;
		RelationalModule& operator=(RelationalModule&& o) {
			free();
			entity_component_indices = std::exchange(o.entity_component_indices, nullptr);
			storages = std::exchange(o.storages, nullptr);
			freelist = std::exchange(o.freelist, nullptr);
			return *this;
		}

		~RelationalModule() {
			if(!should_leak) free();
		}
	};

	kanren::Goal auto stream_of_all_entities(const kanren::Variable& var, bool include_error = false) {
		return [=](kanren::State state) -> std::generator<kanren::State> {
			auto [m, s, c] = state;
			for(size_t e = include_error ? 0 : 1, size = fp_size(state.module->entity_component_indices); e < size; ++e)
				if(!state.module->freelist || !fp_contains(state.module->freelist, e)) {
					s.emplace_front(var, kanren::Term{e});
					co_yield {m, s, c};
					s.pop_front();
				}
		};
	}

	kanren::Goal auto has_component(const kanren::Term& var, ecrs::component_t componentID) {
		return [=](kanren::State state) -> std::generator<kanren::State> {
			auto [m, s, c] = state;

			auto var_ = kanren::find(var, s);
			if(std::holds_alternative<ecrs::Entity>(var_)) {
				if(m->has_component(std::get<ecrs::Entity>(var_), componentID))
					co_yield state;

			} else if(std::holds_alternative<kanren::Variable>(var_))
				for(size_t e = 0, size = fp_size(m->entity_component_indices); e < size; ++e) {
					auto comps = m->entity_component_indices[e];
					if(fp_size(comps) > componentID && comps[componentID] != ecrs::Storage::invalid) {
						s.emplace_front(std::get<kanren::Variable>(var_), kanren::Term{e});
						co_yield {m, s, c};
						s.pop_front();
					}
				}
		};
	}
	template<typename T, size_t Unique = 0>
	inline kanren::Goal auto has_component(const kanren::Term& var) { return has_component(var, get_global_component_id<T, Unique>()); }

	template<std::derived_from<RelationBase> T, size_t Unique = 0>
	kanren::Goal auto related_entities(const kanren::Term& base, const kanren::Term& relate) {
		const auto componentID = get_global_component_id<T, Unique>();
		return [=](kanren::State state) -> std::generator<kanren::State> {
			auto [m, s, c] = state;
			auto base_ = kanren::find(base, s);
			auto relate_ = kanren::find(relate, s);

			// if(base_ && relate_) {
			// Two variables... generate a sequence of every possible relation
			if(std::holds_alternative<kanren::Variable>(base_) && std::holds_alternative<kanren::Variable>(relate_)) {
				for(size_t e = 0, size = fp_size(m->entity_component_indices); e < size; ++e)
					if(m->has_component<T, Unique>(e)) {
						auto& related = m->get_component<T, Unique>(e).related;
						if(related.size()) {
							s.emplace_front(std::get<kanren::Variable>(base_), kanren::Term{e});
							for(const auto& r: related) {
								s.emplace_front(std::get<kanren::Variable>(relate_), kanren::Term{r});
								co_yield {m, s, c};
								s.pop_front();
							}
							s.pop_front();
						}
					}

			// Base variable, Relation fixed... generate sequence of all entities who have related in their relation list
			} else if(std::holds_alternative<kanren::Variable>(base_) && std::holds_alternative<ecrs::Entity>(relate_)) {
				for(size_t e = 0, size = fp_size(m->entity_component_indices); e < size; ++e)
					if(m->has_component<T, Unique>(e)) {
						for(const auto& r: m->get_component<T, Unique>(e).related)
							if(kanren::term_equivalence({r}, relate_)) {
								s.emplace_front(std::get<kanren::Variable>(base_), kanren::Term{e});
								co_yield {m, s, c};
								s.pop_front();
							}
					}

			// Base fixed, Relation variable... generate sequence of all entities in the fixed entity's relation list
			} else if(std::holds_alternative<ecrs::Entity>(base_) && std::holds_alternative<kanren::Variable>(relate_)) {
				auto e = std::get<ecrs::Entity>(base_);
				if(m->has_component<T, Unique>(e)) {
					for(const auto& r: m->get_component<T, Unique>(e).related) {
						s.emplace_front(std::get<kanren::Variable>(relate_), kanren::Term{r});
						co_yield {m, s, c};
						s.pop_front();
					}
				}

			// Both fixed... confirm relate is in base's related list
			} else if(std::holds_alternative<ecrs::Entity>(base_) && std::holds_alternative<ecrs::Entity>(relate_)) {
				auto eBase = std::get<ecrs::Entity>(base_);
				auto eRelate = std::get<ecrs::Entity>(relate_);
				if(m->has_component<T, Unique>(eBase)) {
					for(const auto& r: m->get_component<T, Unique>(eBase).related)
						if(kanren::term_equivalence({r}, {eRelate})) {
							co_yield state;
							break;
						}
				}
			}
			// }
		};
	}

	template<std::derived_from<RelationBase> T, size_t Unique = 0>
	kanren::Goal auto related_entities_list(const kanren::Term& base, const kanren::Term& relate) {
		const auto componentID = get_global_component_id<T, Unique>();
		return [=](kanren::State state) -> std::generator<kanren::State> {
			auto [m, s, c] = state;
			auto base_ = kanren::find(base, s);
			auto relate_ = kanren::find(relate, s);

			// Two variables... generate a sequence of every possible relation
			if(std::holds_alternative<kanren::Variable>(base_) && std::holds_alternative<kanren::Variable>(relate_)) {
				for(size_t e = 0, size = fp_size(m->entity_component_indices); e < size; ++e)
					if(m->has_component<T, Unique>(e)) {
						auto& related = m->get_component<T, Unique>(e).related;
						if(related.size()) {
							s.emplace_front(std::get<kanren::Variable>(base_), kanren::Term{e});
							s.emplace_front(std::get<kanren::Variable>(relate_), kanren::Term{std::list<kanren::Term>(related.begin(), related.end())});
							co_yield {m, s, c};
							s.pop_front();
							s.pop_front();
						}
					}

			// Related fixed, base variable... try to convert related to list of entities and match against any entities list of related variables
			} else if(std::holds_alternative<kanren::Variable>(base_) && std::holds_alternative<std::list<kanren::Term>>(relate_)) {
					// Attempts to convert a term into a list of entities, returns an empty list if any terms aren't bound
					constexpr auto materialize_list = [](const kanren::Term& term, const kanren::Substitutions& s) -> std::list<kanren::Term> {
						switch(term.index()) {
						case 0: // Variable
							return std::list<kanren::Term>{};
						case 1: // ecrs::Entity
							return std::list<kanren::Term>{std::get<Entity>(term)};
						case 2: { // std::list<Term>
							std::list<kanren::Term> out;
							auto& l = std::get<std::list<kanren::Term>>(term);
							for(const auto& term: l) {
								auto term_ = find(term, s);
								if(!std::holds_alternative<Entity>(term_)) return std::list<kanren::Term>{};
								out.emplace_back(std::get<ecrs::Entity>(term_));
							}
							return out;
						}
						}
						return std::list<kanren::Term>{};
					};

					std::list<kanren::Term> related;
					if constexpr(T::can_be_term)
						related = std::get<std::list<kanren::Term>>(relate_);
					// If we can't reduce the list to a list of entities then we can't match it against anything in the ECS!
					else related = materialize_list(relate_, s);
					if(related.empty()) co_return;

					for(size_t e = 0, size = fp_size(m->entity_component_indices); e < size; ++e)
						if(m->has_component<T, Unique>(e)) {
							auto& eRelated = m->get_component<T, Unique>(e).related;
							if(auto sub = unify({related}, {std::list<kanren::Term>(eRelated.begin(), eRelated.end())}, s); sub)
								co_yield {m, *sub, c};
						}


			// Base fixed, Relation variable... generate sequence of all entities in the fixed entity's relation list
			} else if(std::holds_alternative<ecrs::Entity>(base_) && std::holds_alternative<kanren::Variable>(relate_)) {
				auto e = std::get<ecrs::Entity>(base_);
				if(m->has_component<T, Unique>(e))
					if(auto r = m->get_component<T, Unique>(e).related; r.size()) {
						s.emplace_front(relate_, kanren::Term{std::list<kanren::Term>(r.begin(), r.end())});
						co_yield {m, s, c};
						s.pop_front();
					}

			// Both fixed... unify the related lists
			} else if(std::holds_alternative<ecrs::Entity>(base_) && std::holds_alternative<std::list<kanren::Term>>(relate_)) {
				auto eBase = std::get<ecrs::Entity>(base_);
				auto& related = std::get<std::list<kanren::Term>>(relate_);
				if(m->has_component<T, Unique>(eBase)) {
					auto r = m->get_component<T, Unique>(eBase).related;
					if(auto sub = unify({related}, {std::list<kanren::Term>(r.begin(), r.end())}, s); sub)
						co_yield {m, *sub, c};
				}
			}
		};
	}
}}

namespace ecrs {
	template<typename T, size_t Unique>
	inline auto Entity::get_related_entities(const TrivialRelationalModule& module) const noexcept {
		return module.get_related_entities<T, Unique>(entity);
	}
	template<typename T, size_t Unique>
	inline auto Entity::get_related_entities() const noexcept {
		assert(current_module != nullptr);
		// assert(dynamic_cast<TrivialRelationalModule*>(current_module) != nullptr);
		return get_related_entities<T, Unique>(*current_module);
	}
}