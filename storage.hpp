#pragma once

// #include <cstddef>
#include <functional>
#include <limits>
#include <numeric>

#include "component_registry.hpp"
// #include "monitor.hpp"

namespace ecrs {
	using entity_t = uint32_t;
	static constexpr entity_t invalid_entity = 0;

	template<typename T>
	struct with_entity {
		T value;
		entity_t entity = invalid_entity;
		operator T() { return value; }
		operator const T() const { return value; }
		T* operator->() { return &value; }
		const T* operator->() const { return &value; }

		template<std::convertible_to<with_entity> To>
		std::partial_ordering operator<=>(const To& other) const requires(requires(T t) {
			{ t <=> t };
		}) {
			if(other.entity == entity) return other.value <=> value;
			return other.entity <=> entity;
		}
		bool operator==(const with_entity& other) const requires(requires(T t) {
			{ t == t };
		}) {
			return other.entity == entity && other.value == value;
		}

		static void swap_entities(with_entity& a, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t eA, entity_t eB) {
			if(a.entity == eA) a.entity = eB;
			else if(a.entity == eB) a.entity = eA;
		}
	};

	template<typename T>
	struct is_tag_t : public std::false_type {};
	template<typename T>
	requires(requires(T t) {{ T::is_tag } -> std::convertible_to<bool>; })
	struct is_tag_t<T> { constexpr static bool value = T::is_tag; };
	template<typename T>
	constexpr static bool is_tag_v = is_tag_t<T>::value;

	struct Tag { constexpr static bool is_tag = true; };

	namespace detail {
		template<typename T>
		requires(is_tag_v<T>)
		T& tag_value() {
			static T value;
			return value;
		}

		template<typename T>
		struct is_with_entity : public std::false_type {};
		template<typename T>
		struct is_with_entity<with_entity<T>> : public std::true_type {};
		template<typename T>
		constexpr static bool is_with_entity_v = is_with_entity<T>::value;

		template<typename T>
		struct remove_with_entity { using type = T; };
		template<typename T>
		struct remove_with_entity<with_entity<T>> { using type = typename remove_with_entity<T>::type; };
		template<typename T>
		using remove_with_entity_t = typename remove_with_entity<T>::type;

		template<typename T>
		concept has_swap_entities = requires(T t, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t e) {
			{T::swap_entities(t, entity_component_indices, e, e)};
		} || requires(T t, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t e) {
			{swap_entities(t, entity_component_indices, e, e)};
		} || requires(T t, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t e) {
			{t.swap_entities(entity_component_indices, e, e)};
		};

		template<has_swap_entities T>
		void swap_entities_impl(T& t, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t a, entity_t b){
			if constexpr (requires(T t, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t e) {
				{T::swap_entities(t, entity_component_indices, e, e)};
			}) {
				T::swap_entities(t, entity_component_indices, a, b);
			} else if constexpr (requires(T t, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t e) {
				{swap_entities(t, entity_component_indices, e, e)};
			}) {
				swap_entities(t, entity_component_indices, a, b);
			} else if constexpr (requires(T t, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t e) {
				{t.swap_entities(entity_component_indices, e, e)};
			}) {
				t.swap_entities(entity_component_indices, a, b);
			} else static_assert(false, "The type doesn't actually have a swap entities function!");
		}

		struct void_like{};

		// Gets the entity associated with a specific component index
		inline entity_t get_entity(const fp::dynarray<fp::dynarray<size_t>> entity_component_indices, size_t index, size_t component_id) {
			assert(entity_component_indices);
			for(size_t e = 0; e < entity_component_indices.size(); ++e)
				if(entity_component_indices[e].size() > component_id && entity_component_indices[e][component_id] == index)
					return e;
			return invalid_entity;
		}
		template<typename Tcomponent, size_t Unique = 0>
		inline entity_t get_entity(const fp::dynarray<fp::dynarray<size_t>> entity_component_indices, size_t index) {
			return get_entity(entity_component_indices, index, ecrs::component_id<Tcomponent, Unique>());
		}
	}

	struct component_storage: protected fp::dynarray<std::byte> {
		static constexpr size_t invalid = std::numeric_limits<size_t>::max();
		using super = fp::dynarray<std::byte>;

		size_t element_size = invalid;

		inline component_storage() noexcept : element_size(invalid), super(nullptr) {}
		inline component_storage(size_t element_size, size_t reserved_element_count = 64) : element_size(element_size), super(nullptr) { reserve(reserved_element_count * element_size); }

		template<typename Tcomponent>
		inline component_storage(Tcomponent reference = {}, size_t reserved_element_count = 64) : component_storage(sizeof(Tcomponent), reserved_element_count) {}
		component_storage(const component_storage& o) = delete;
		inline component_storage(component_storage&& o) { *this = std::move(o); }

		component_storage& operator=(const component_storage& o) = delete;
		inline component_storage& operator=(component_storage&& o) {
			element_size = o.element_size;
			if(raw) free();
			raw = std::exchange(o.raw, {nullptr});
			return *this;
		}

		inline ~component_storage() { free(); }

		template<typename T>
		inline T* data() noexcept {
			assert(sizeof(T) == element_size); // Implies element_size != invalid (since no type should ever be that big!)
			return (T*)raw;
		}
		template<typename T>
		inline const T* data() const noexcept {
			assert(sizeof(T) == element_size); // Implies element_size != invalid (since no type should ever be that big!)
			return (const T*)raw;
		}

		inline size_t size() const noexcept { return fpda_size(raw) / element_size; }
		inline bool empty() const noexcept { return size() == 0; }

		inline void* get(entity_t e) noexcept {
			assert(e < size());
			return raw + e * element_size;
		}
		inline const void* get(entity_t e) const noexcept {
			assert(e < size());
			return raw + e * element_size;
		}
		template<typename T>
		inline T& get(entity_t e) noexcept {
			assert(e < size());
			return *(data<T>() + e);
		}
		template<typename T>
		inline const T& get(entity_t e) const noexcept {
			assert(e < size());
			return *(data<T>() + e);
		}

		template<typename T>
		void allocate(size_t count = 1) noexcept {
			auto originalEnd = size();
			fpda_grow(raw, element_size * count);
			auto data = this->data<T>();
			for (size_t i = 0; i < count; i++)
				new(data + originalEnd + i) T();
		}
		inline void allocate(size_t count = 1) noexcept {
			grow(element_size * count, std::byte{0});
		}

		template<typename T>
		inline T& get_or_allocate(entity_t e) noexcept {
			size_t size = this->size();
			if(size <= e)
				allocate<T>(std::max<int64_t>(int64_t(e) - size + 1, 1));
			return get<T>(e);
		}
		inline void* get_or_allocate(entity_t e) noexcept {
			size_t size = this->size();
			if(size <= e)
				allocate(std::max<int64_t>(int64_t(e) - size + 1, 1));
			return get(e);
		}

		template<typename Tcomponent>
		void swap(size_t a, std::optional<size_t> _b = {}) {
			size_t b = _b.value_or(size() - 1);
			assert(a < size());
			assert(b < size());

			Tcomponent* aPtr = data<Tcomponent>() + a;
			Tcomponent* bPtr = data<Tcomponent>() + b;
			std::swap(*aPtr, *bPtr);
		}
		void swap(size_t a, std::optional<size_t> _b = {}) {
			size_t b = _b.value_or(size() - 1);
			assert(a < size());
			assert(b < size());

			void* aPtr = raw + a * element_size;
			void* bPtr = raw + b * element_size;
			memswap(aPtr, bPtr, element_size);
		}

		template<typename Tcomponent, size_t Unique /* = 0 */>
		inline friend entity_t get_entity(component_storage& storage, const fp::dynarray<fp::dynarray<size_t>> entity_component_indices, size_t index, std::optional<size_t> component_id /* = {} */) {
			if constexpr(detail::is_with_entity_v<Tcomponent>)
				return (storage.data<Tcomponent>() + index)->entity;
			else if constexpr(std::is_same_v<Tcomponent, detail::void_like>)
				return detail::get_entity(entity_component_indices, index, component_id.value());
			else return detail::get_entity<Tcomponent, Unique>(entity_component_indices, index);
		}

		template<typename Tcomponent, size_t Unique = 0>
		friend bool swap_impl(component_storage* self, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, size_t a, std::optional<size_t> _b = {}, bool swap_if_one_elementless = false, std::optional<size_t> _component_id = {}) {
			size_t b = _b.value_or(self->size() - 1);
			size_t component_id = _component_id.value_or(ecrs::component_id<Tcomponent, Unique>());
			entity_t eA = get_entity<Tcomponent, Unique>(*self, entity_component_indices, a, component_id);
			entity_t eB = get_entity<Tcomponent, Unique>(*self, entity_component_indices, b, component_id);
			if (swap_if_one_elementless) {
				if (eA == invalid_entity && eB == invalid_entity) return false;
			}
			else if (eA == invalid_entity || eB == invalid_entity) return false;

			if constexpr(std::is_same_v<Tcomponent, detail::void_like>)
				self->swap(a, b);
			else self->swap<Tcomponent>(a, b);
			if (swap_if_one_elementless && eA == invalid_entity) {
				if(auto& idx = entity_component_indices[eB]; idx.size() <= component_id) {
					idx.grow_to_size(component_id + 1, component_storage::invalid);
					// entity_component_indices[eB] = idx;
				}
				entity_component_indices[eB][component_id] = a;
			} else if (swap_if_one_elementless && eB == invalid_entity) {
				if(auto& idx = entity_component_indices[eA]; idx.size() <= component_id) {
					idx.grow_to_size(component_id + 1, component_storage::invalid);
					// module.entity_component_indices[eA] = idx;
				}
				entity_component_indices[eA][component_id] = b;
			} else std::swap(
				entity_component_indices[eA][component_id],
				entity_component_indices[eB][component_id]
			);
			return true;
		}
		template<typename Tcomponent, size_t Unique = 0>
		inline bool swap(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, size_t a, std::optional<size_t> b = {}, bool swap_if_one_elementless = false) {
			return swap_impl<Tcomponent, Unique>(this, entity_component_indices, a, b, swap_if_one_elementless);
		}
		inline bool swap(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, size_t component_id, size_t a, std::optional<size_t> b = {}, bool swap_if_one_elementless = false) {
			return swap_impl<detail::void_like, 0>(this, entity_component_indices, a, b, swap_if_one_elementless, component_id);
		}

		template<typename Tcomponent, size_t Unique = 0>
		bool remove(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t e) { return remove(entity_component_indices, e, ecrs::component_id<Tcomponent, Unique>()); }
		bool remove(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, entity_t e, size_t component_id) {
			size_t size = this->size();
			if(size == 0 || !entity_component_indices || e >= entity_component_indices.size()) return false;

			auto& indices = entity_component_indices[e];
			if(indices.size() <= component_id) return false;

			for(e = 0; e < entity_component_indices.size(); ++e)
				if(entity_component_indices[e].size() > component_id
					&& entity_component_indices[e][component_id] == size - 1
				)
					break;
			if(e >= entity_component_indices.size()) return false;

			swap(indices[component_id]);
			if(entity_component_indices[e].size() <= component_id) entity_component_indices[e].grow_to_size(component_id + 1, component_storage::invalid);
			std::swap(indices[component_id], entity_component_indices[e][component_id]);
			// delete_range((size - 1) * element_size, element_size); // TODO: Could we pop back instead?
			pop_back_n(element_size);
			indices[component_id] = invalid;
			return true;
		}

		template<typename Tcomponent, size_t Unique = 0>
		friend void reorder_impl(component_storage* self, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, fp::view<size_t> order, std::optional<size_t> _component_id = {}) {
			assert(order.size() == self->size()); // Require order to have an entry for every element in the array
			if(self->size() <= 1) return; // Zero or one elements are always sorted
			size_t component_id = _component_id.value_or(ecrs::component_id<Tcomponent, Unique>());

			size_t* swaps = fp_alloca(size_t, order.size());
			// Transpose the order (it now stores what needs to be swapped with what)
			for(size_t i = 0; i < order.size(); i++)
				swaps[order[i]] = i;

			// Update the data storage and book keeping
			for(size_t i = 0; i < order.size(); ++i)
				while(swaps[i] != i) {
					if constexpr(std::is_same_v<Tcomponent, detail::void_like>)
						self->swap(entity_component_indices, component_id, swaps[i], i);
					else self->swap<Tcomponent, Unique>(entity_component_indices, swaps[i], i);
					std::swap(swaps[swaps[i]], swaps[i]);
				}
		}
		inline void reorder(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, size_t component_id, fp::view<size_t> order) {
			reorder_impl<detail::void_like, 0>(this, entity_component_indices, order, component_id);
		}
		template<typename Tcomponent, size_t Unique = 0>
		inline void reorder(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, fp::view<size_t> order) {
			reorder_impl<Tcomponent, Unique>(this, entity_component_indices, order);
		}

		template<typename Tcomponent, typename F, bool with_entities /*= false*/, size_t Unique /*= 0*/>
		friend void sort_impl(component_storage* self, fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, const F& _comparator, std::optional<size_t> _component_id = {}) {
			size_t component_id = _component_id.value_or(ecrs::component_id<Tcomponent, Unique>());
			// Create a list of indices
			size_t size = self->size();
			if(size <= 1) return; // Zero or one elements are always sorted
			size_t* order = fp_alloca(size_t, size);
			std::iota(order, fp_end(order), 0);

			constexpr static auto data = std::is_same_v<Tcomponent, detail::void_like> ? +[](component_storage* self, size_t i) -> void* {
				return ((char*)self->raw) + i * self->element_size;
			} : +[](component_storage* self, size_t i) -> void* {
				return self->data<Tcomponent>() + i;
			};

			// Sort the list of indices into the correct order (possibly alongside a list of entities)
			if constexpr(with_entities) {
				entity_t* entities = fp_alloca(entity_t, size);
				for(size_t i = size; i--; )
					entities[i] = get_entity<Tcomponent, Unique>(*self, entity_component_indices, i, component_id);

				auto comparator = [self, entities, &_comparator](size_t _a, size_t _b) {
					void* a = data(self, _a);
					void* b = data(self, _b);
					return _comparator(a, entities[_a], b, entities[_b]);
				};

				std::sort(order, fp_end(order), comparator);
			} else {
				auto comparator = [self, &_comparator](size_t _a, size_t _b) {
					void* a = data(self, _a);
					void* b = data(self, _b);
					return _comparator(a, b);
				};

				std::sort(order, fp_end(order), comparator);
			}

			if constexpr(std::is_same_v<Tcomponent, detail::void_like>)
				self->reorder(entity_component_indices, component_id, fp_view_make_full(size_t, order));
			else self->reorder<Tcomponent, Unique>(entity_component_indices, fp_view_make_full(size_t, order));
		}
		template<typename F, bool with_entities>
		inline void sort(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, size_t component_id, const F& comparator) {
			sort_impl<detail::void_like, F, with_entities, 0>(this, entity_component_indices, comparator, component_id);
		}
		template<typename Tcomponent, typename F, bool with_entities = false, size_t Unique = 0>
		inline void sort(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, const F& _comparator) {
			if constexpr(with_entities) {
				auto comparator = [&_comparator](void* a, entity_t aE, void* b, entity_t bE) {
					return _comparator((Tcomponent*)a, aE, (Tcomponent*)b, bE);
				};
				sort_impl<Tcomponent, decltype(comparator), with_entities, Unique>(this, entity_component_indices, comparator);
			} else {
				auto comparator = [&_comparator](void* a, void* b) {
					return _comparator((Tcomponent*)a, (Tcomponent*)b);
				};
				sort_impl<Tcomponent, decltype(comparator), with_entities, Unique>(this, entity_component_indices, comparator);
			}
		}

		template<typename Tcomponent, size_t Unique = 0>
		void sort_by_value(struct fp::dynarray<fp::dynarray<size_t>>& entity_component_indices) {
			constexpr static auto comparator = [](Tcomponent* a, Tcomponent* b) {
				return std::less<Tcomponent>{}(*a, *b);
			};
			sort<Tcomponent, decltype(comparator), false, Unique>(entity_component_indices, comparator);
		}

		template<typename Tcomponent, size_t Unique = 0>
		void sort_monotonic(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices) {
			auto comparator = [](Tcomponent* a, entity_t eA, Tcomponent* b, entity_t eB) {
				return std::less<entity_t>{}(eA, eB);
			};
			sort<Tcomponent, decltype(comparator), true, Unique>(entity_component_indices, comparator);
		}
		void sort_monotonic(fp::dynarray<fp::dynarray<size_t>>& entity_component_indices, size_t component_id) {
			auto comparator = [](void* a, entity_t eA, void* b, entity_t eB) {
				return std::less<entity_t>{}(eA, eB);
			};
			sort<decltype(comparator), true>(entity_component_indices, component_id, comparator);
		}
	};
}
