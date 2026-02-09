#pragma once

#include "component_registry.hpp"
#include "fp/dynarray.hpp"
#include "fp/pointer.hpp"
#include "storage.hpp"

#include <cassert>
#include <compare>
#include <cstddef>
#include <fp/hash.hpp>

namespace ecrs {

	namespace detail {
		// From: https://stackoverflow.com/a/29753388
		template<int N, typename... Ts>
		using nth_type = typename std::tuple_element<N, std::tuple<Ts...>>::type;
	}

	struct context : protected fp::dynarray<component_storage> {
		fp::dynarray<fp::dynarray<size_t>> entity_component_indices = nullptr;
		fp::hash_table<size_t> freelist = nullptr;

		context() {}
		context(std::nullptr_t) {}
		context(const context&) = default;
		context(context&&) = default;
		context& operator=(const context&) = default;
		context& operator=(context&&) = default;

		component_storage& get_storage(size_t component_id, size_t element_size) {
			while(size() <= component_id)
				emplace_back();
			if((*this)[component_id].element_size == component_storage::invalid)
				(*this)[component_id] = component_storage(element_size);
			// This failing indicates the component ID was never registered!
			assert((*this)[component_id].element_size != component_storage::invalid);
			return (*this)[component_id];
		}
		const component_storage& get_storage(size_t component_id, size_t element_size) const {
			assert(size() > component_id);
			assert((*this)[component_id].element_size != component_storage::invalid);
			return (*this)[component_id];
		}

		template<typename Tcomponent, size_t Unique = 0>
		component_storage& get_storage() {
			return get_storage(component_id<Tcomponent, Unique>(), sizeof(Tcomponent));
		}
		template<typename Tcomponent, size_t Unique = 0>
		const component_storage& get_storage() const {
			return get_storage(component_id<Tcomponent, Unique>(), sizeof(Tcomponent));
		}

		size_t entity_count() {
			return size() - freelist.occupied_size();
		}

		entity_t add_entity() {
			if(freelist)
				if(auto pos = freelist.find_first_occupied_position(); pos != fp::not_found) {
					freelist.remove_at_position(pos);
					return pos;
				}
			entity_t out = entity_component_indices.size();
			entity_component_indices.emplace_back();
			return out;
		}

		void remove_entity(entity_t e) {
			assert(e < entity_component_indices.size());
			entity_component_indices[e].free(true);
			if (!freelist) {
				fp::hash_table<size_t>::config config;
				config.neighborhood_size = 2;
				freelist = fp::hash_table<size_t>::create(config);
			}
			freelist.insert(e);
		}

		bool has_component(entity_t e, size_t component_id) const {
			assert(!freelist || !freelist.contains(e));
			return entity_component_indices
				&& e < entity_component_indices.size()
				&& entity_component_indices[e]
				&& entity_component_indices[e].size() > component_id
				&& entity_component_indices[e][component_id] != component_storage::invalid;
		}
		template<typename Tcomponent, size_t Unique = 0>
		bool has_component(entity_t e) const {
			return has_component(e, component_id<Tcomponent, Unique>());
		}

		void* add_component(entity_t e, size_t component_id, std::optional<size_t> element_size = {}) {
			assert(!has_component(e, component_id));
			auto& storage = get_storage(component_id, element_size.value_or(lookup_component_size(component_id)));
			if(
				!entity_component_indices[e]
				|| !entity_component_indices.size()
				|| entity_component_indices[e].size() <= component_id
			)
				entity_component_indices[e].grow_to_size(component_id + 1, component_storage::invalid);
			auto idx = entity_component_indices[e][component_id] = storage.size();
			storage.allocate(1);
			return storage.get(idx);
		}
		template<typename Tcomponent, size_t Unique = 0>
		Tcomponent& add_component(entity_t e) {
			auto out = (Tcomponent*)add_component(e, component_id<Tcomponent, Unique>(), sizeof(Tcomponent));
			if constexpr (detail::is_with_entity_v<Tcomponent>)
				out->entity = e;
			return *out;
		}

		void* get_component(entity_t e, size_t component_id, std::optional<size_t> element_size = {}) {
			assert(has_component(e, component_id));
			auto& storage = get_storage(component_id, element_size.value_or(lookup_component_size(component_id)));
			return storage.get(entity_component_indices[e][component_id]);
		}
		const void* get_component(entity_t e, size_t component_id, std::optional<size_t> element_size = {}) const {
			assert(has_component(e, component_id));
			auto& storage = get_storage(component_id, element_size.value_or(lookup_component_size(component_id)));
			return storage.get(entity_component_indices[e][component_id]);
		}

		template<typename Tcomponent, size_t Unique = 0>
		Tcomponent& get_component(entity_t e) {
			return *(Tcomponent*)get_component(e, component_id<Tcomponent, Unique>(), sizeof(Tcomponent));
		}
		template<typename Tcomponent, size_t Unique = 0>
		const Tcomponent& get_component(entity_t e) const {
			return *(Tcomponent*)get_component(e, component_id<Tcomponent, Unique>(), sizeof(Tcomponent));
		}

		void* get_or_add_component(entity_t e, size_t component_id, std::optional<size_t> element_size = {}) {
			if(has_component(e, component_id))
				return get_component(e, component_id, element_size);
			return add_component(e, component_id, element_size);
		}
		template<typename Tcomponent, size_t Unique = 0>
		Tcomponent& get_or_add_component(entity_t e) {
			return *(Tcomponent*)get_or_add_component(e, component_id<Tcomponent, Unique>(), sizeof(Tcomponent));
		}

	protected:
		template<typename Tcomponent, size_t Unique = 0>
		struct NotifySwapOp {
			inline void operator()(context& self, entity_t a, entity_t b) const {
				// if constexpr(!detail::has_swap_entities<Tcomponent>) return true;
				auto& storage = self.get_storage<Tcomponent, Unique>();
				Tcomponent* data = storage.template data<Tcomponent>();
				for(size_t i = storage.size(); i--; ) {
					// This commented code runs half as fast as the current code!
					// if(!self.has_component<Tcomponent>(i)) continue;
					// Tcomponent::swap_entities(*self.get_component<Tcomponent>(i), a, b);
					Tcomponent::swap_entities(data[i], self, a, b);
				}
			}
		};
	public:
		void swap_entities(entity_t a, std::optional<entity_t> _b = {}) {
			entity_t b = _b.value_or(entity_component_indices.size() - 1);

			assert(a < entity_component_indices.size());
			assert(b < entity_component_indices.size());
			std::swap(entity_component_indices[a], entity_component_indices[b]);
		}

		template<typename... Tcomponents2notify>
		void swap_entities(entity_t a, std::optional<entity_t> _b = {}) {
			entity_t b = _b.value_or(entity_component_indices.size() - 1);

			[&, this]<std::size_t... I>(std::index_sequence<I...>) {
				(NotifySwapOp<detail::nth_type<I, Tcomponents2notify...>>{}(*this, a, b), ...);
			}(std::make_index_sequence<sizeof...(Tcomponents2notify)>{});

			swap_entities(a, b);
		}

protected:
    template<typename SwapFunc>
    void reorder_entities_impl(fp::view<size_t> order, SwapFunc&& swap_func) {
        size_t size = order.size();
        assert(size == this->size()); /* Require order to have an entry for every element in the array */
        auto swaps = fp_alloca(size_t, size);

        /* Transpose the order (it now stores what needs to be swapped with what) */
        for(size_t i = 0; i < size; ++i)
            swaps[order[i]] = i;

        /* Update the data storage and book keeping */
        for(size_t i = 0; i < size; ++i)
            while(swaps[i] != i) {
                swap_func(swaps[i], i);
                std::swap(swaps[swaps[i]], swaps[i]);
            }
		// TODO: How does this interact with the free list?
    }

public:
    void reorder_entities(fp::view<size_t> order) {
        reorder_entities_impl(order, [this](size_t a, size_t b) {
            swap_entities(a, b);
        });
    }

    template<typename... Tcomponents2notify>
    void reorder_entities(fp::view<size_t> order) {
        reorder_entities_impl(order, [this](size_t a, size_t b) {
            swap_entities<Tcomponents2notify...>(a, b);
        });
    }

	protected:
		template<typename Tcomponent>
		struct MonotonicOp {
			inline void operator()(context& self, component_storage& storage) const {
				storage.sort_monotonic<Tcomponent>(self.entity_component_indices);
			}
		};
	public:
		template<typename... Tcomponents>
		void make_monotonic() {
			[&, this]<std::size_t... I>(std::index_sequence<I...>) {
				(MonotonicOp<detail::nth_type<I, Tcomponents...>>{}(*this, get_storage<detail::nth_type<I, Tcomponents...>>()), ...);
			}(std::make_index_sequence<sizeof...(Tcomponents)>{});
		}
		template<typename Tcomponent, size_t Unique = 0>
		void make_monotonic() {
			get_storage<Tcomponent, Unique>()->template sort_monotonic<Tcomponent, Unique>(entity_component_indices);
		}
		void make_monotonic(fp_view(size_t) component_ids) {
			fp_view_iterate_named(size_t, component_ids, id)
				make_monotonic(*id);
		}
		void make_monotonic(size_t component_id, std::optional<size_t> element_size = {}) {
			get_storage(component_id, element_size.value_or(lookup_component_size(component_id))).sort_monotonic(entity_component_indices, component_id);
		}

		void make_all_monotonic() {
			size_t id = -1;
			for(auto& storage: *this) {
				++id;
				if(storage.element_size == component_storage::invalid) continue; // Only initialized storages can be made monotonic
				storage.sort_monotonic(entity_component_indices, id);
			}
		}

		void free(bool nullify = true) {
			fp::dynarray<component_storage>::free(nullify);
			entity_component_indices.free(nullify);
			freelist.free(nullify);
		}
		void free() const {
			fp::dynarray<component_storage>::free();
			entity_component_indices.free();
			freelist.free();
		}

		struct entity_iterator {
			const context* ctx;
			size_t index;

			entity_iterator(const context* ctx, size_t index) : ctx(ctx), index(index) {
				skip_freed();
			}

			void skip_freed() {
				while (index < ctx->entity_component_indices.size()
					&& ctx->freelist && ctx->freelist.contains(index)
				)
					++index;
			}

			entity_iterator& operator++() {
				++index;
				skip_freed();
				return *this;
			}

			entity_iterator operator++(int) {
				entity_iterator tmp = *this;
				++(*this);
				return tmp;
			}

			entity_t operator*() const {
				return index;
			}

			bool operator==(const entity_iterator& other) const {
				return index == other.index;
			}

			bool operator!=(const entity_iterator& other) const {
				return index != other.index;
			}
		};

		// Range class for convenient range-based for loops
		struct entity_range {
			const context* ctx;

			entity_range(const context* ctx) : ctx(ctx) {}

			entity_iterator begin() const {
				return entity_iterator(ctx, 0);
			}

			entity_iterator end() const {
				return entity_iterator(ctx, ctx->entity_component_indices.size());
			}
		};

		// Add these methods to the context struct:
		entity_range entities() const {
			return entity_range(this);
		}

		struct entity {
			static context*& current_context() {
				static thread_local context* current_context = nullptr;
				return current_context;
			}
			static void set_current_context(context& ctx) {
				current_context() = &ctx;
			}

			entity_t entity_;
			inline operator entity_t() const { return entity_; }

			entity() {}
			entity(entity_t entity) : entity_(entity) {}
			entity(const entity&) = default;
			entity(entity&&) = default;
			entity& operator=(const entity&) = default;
			entity& operator=(entity&&) = default;

			std::strong_ordering operator<=>(const entity&) const = default;
			bool operator==(const entity&) const = default;

			void remove() {
				assert(current_context());
				current_context()->remove_entity(*this);
			}

			bool has_component(size_t component_id) const {
				assert(current_context());
				return current_context()->has_component(*this, component_id);
			}
			template<typename Tcomponent, size_t Unique = 0>
			bool has_component() const {
				assert(current_context());
				return current_context()->has_component<Tcomponent, Unique>(*this);
			}

			void* add_component(size_t component_id, std::optional<size_t> element_size = {}) {
				assert(current_context());
				return current_context()->add_component(*this, component_id, element_size);
			}
			template<typename Tcomponent, size_t Unique = 0>
			Tcomponent& add_component() {
				assert(current_context());
				return current_context()->add_component<Tcomponent, Unique>(*this);
			}

			void* get_component(size_t component_id, std::optional<size_t> element_size = {}) {
				assert(current_context());
				return current_context()->get_component(*this, component_id, element_size);
			}
			const void* get_component(size_t component_id, std::optional<size_t> element_size = {}) const {
				assert(current_context());
				return current_context()->get_component(*this, component_id, element_size);
			}

			template<typename Tcomponent, size_t Unique = 0>
			Tcomponent& get_component() {
				assert(current_context());
				return current_context()->get_component<Tcomponent, Unique>(*this);
			}
			template<typename Tcomponent, size_t Unique = 0>
			const Tcomponent& get_component() const {
				assert(current_context());
				return current_context()->has_component<Tcomponent, Unique>(*this);
			}

			void* get_or_add_component(size_t component_id, std::optional<size_t> element_size = {}) {
				assert(current_context());
				return current_context()->get_or_add_component(*this, component_id, element_size);
			}
			template<typename Tcomponent, size_t Unique = 0>
			Tcomponent& get_or_add_component() {
				assert(current_context());
				return current_context()->get_or_add_component<Tcomponent, Unique>(*this);
			}
		};

		context& make_current() {
			entity::set_current_context(*this);
			return *this;
		}
	};

	namespace raii {
		using context = fp::auto_free<ecrs::context>;
	}

}
