#pragma once

#include "component_id.hpp"

#include <numeric>

namespace ecrs {

	using entity_t = size_t;
	static constexpr size_t invalid_entity = 0;

	using component_t = size_t;

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

		static void swap_entities(with_entity& a, struct TrivialModule& module, entity_t eA, entity_t eB) {
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
		concept has_swap_entities = requires(T t, struct TrivialModule module, entity_t e) {
			{T::swap_entities(t, module, e, e)};
		};

		// From: https://stackoverflow.com/a/29753388
		template<int N, typename... Ts>
		using nth_type = typename std::tuple_element<N, std::tuple<Ts...>>::type;

		struct void_like{};
	}

	struct Storage {
		static constexpr size_t invalid = std::numeric_limits<size_t>::max();
		size_t element_size = invalid;
		fp_dynarray(uint8_t) raw = nullptr;
		bool should_leak = false; // Useful when shutting down, if we are closing we can just leave memory cleanup to the operating system for a bit of added performance!


		inline Storage() noexcept : element_size(invalid), raw(nullptr) {}
		inline Storage(size_t element_size, size_t reserved_element_count = 64) noexcept : element_size(element_size), raw(nullptr) { fpda_reserve(raw, reserved_element_count * element_size); }

		template<typename Tcomponent>
		inline Storage(Tcomponent reference = {}, size_t reserved_element_count = 64) noexcept : Storage(sizeof(Tcomponent), reserved_element_count) {}
		Storage(const Storage& o) = delete;
		inline Storage(Storage&& o) { *this = std::move(o); }

		Storage& operator=(const Storage& o) = delete;
		inline Storage& operator=(Storage&& o) {
			element_size = o.element_size;
			if(raw) fpda_free_and_null(raw);
			raw = std::exchange(o.raw, nullptr);
			should_leak = o.should_leak;
			return *this;
		}

		inline ~Storage() noexcept { if(!should_leak && raw) fpda_free_and_null(raw); }

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
			fpda_grow_and_initialize(raw, element_size * count, 0);
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

		template<typename Tcomponent, size_t Unique = 0>
		bool swap(struct TrivialModule& module, size_t a, std::optional<size_t> _b = {}, bool swap_if_one_elementless = false);
		bool swap(struct TrivialModule& module, size_t component_id, size_t a, std::optional<size_t> _b = {}, bool swap_if_one_elementless = false);

		template<typename Tcomponent, size_t Unique = 0>
		bool remove(struct TrivialModule& module, entity_t e) { return remove(module, e, get_global_component_id<Tcomponent, Unique>()); }
		bool remove(struct TrivialModule&, entity_t, size_t component_id);

		template<typename Tcomponent, size_t Unique = 0>
		void reorder(struct TrivialModule& module, fp_view(size_t) order);
		void reorder(struct TrivialModule& module, size_t component_id, fp_view(size_t) order);

		template<typename Tcomponent, typename F, bool with_entities = false, size_t Unique = 0>
		void sort(struct TrivialModule& module, const F& _comparator);
		template<typename F, bool with_entities = false>
		void sort(struct TrivialModule& module, size_t component_id, const F& comparator);

		template<typename Tcomponent, size_t Unique = 0>
		void sort_by_value(struct TrivialModule& module) {
			constexpr static auto comparator = [](Tcomponent* a, Tcomponent* b) {
				return std::less<Tcomponent>{}(*a, *b);
			};
			sort<Tcomponent, decltype(comparator), false, Unique>(module, comparator);
		}

		template<typename Tcomponent, size_t Unique = 0>
		void sort_monotonic(struct TrivialModule& module) {
			auto comparator = [](Tcomponent* a, entity_t eA, Tcomponent* b, entity_t eB) {
				return std::less<entity_t>{}(eA, eB);
			};
			sort<Tcomponent, decltype(comparator), true, Unique>(module, comparator);
		}
		void sort_monotonic(struct TrivialModule& module, size_t component_id) {
			auto comparator = [](void* a, entity_t eA, void* b, entity_t eB) {
				return std::less<entity_t>{}(eA, eB);
			};
			sort<decltype(comparator), true>(module, component_id, comparator);
		}
	};

	struct TrivialModule {
		fp_dynarray(fp_dynarray(size_t)) entity_component_indices = nullptr;
		fp_dynarray(Storage) storages = nullptr;
		fp_dynarray(entity_t) freelist = nullptr;

		inline void free() {
			if(entity_component_indices) {
				fpda_iterate(entity_component_indices)
					if(*i) fpda_free_and_null(*i);
				fpda_free_and_null(entity_component_indices);
			}
			if(storages) {
				fpda_iterate(storages)
					i->~Storage();
				fpda_free_and_null(storages);
			}
			if(freelist) fpda_free_and_null(freelist);
		}

		size_t entity_count() const { return fpda_size(entity_component_indices); }

		Storage& get_storage(component_t componentID, size_t element_size = Storage::invalid) noexcept {
			if(!storages || fpda_size(storages) <= componentID) {
				size_t old = fpda_size(storages);
				fpda_grow_to_size(storages, componentID + 1);
				for(size_t i = old, size = fpda_size(storages); i < size; ++i)
					new(storages + i) Storage();
			}
			if(storages[componentID].element_size == Storage::invalid) {
				assert(element_size != Storage::invalid);
				storages[componentID] = Storage(element_size);
			}
			return storages[componentID];
		}
		inline const Storage& get_storage(component_t componentID, size_t element_size = Storage::invalid) const noexcept {
			assert(fpda_size(storages) > componentID);
			assert(storages[componentID].element_size != Storage::invalid);
			return storages[componentID];
		}

		template<typename T, size_t Unique = 0>
		inline Storage& get_storage() noexcept { return get_storage(get_global_component_id<T, Unique>(), sizeof(T)); }
		template<typename T, size_t Unique = 0>
		inline const Storage& get_storage() const noexcept { return get_storage(get_global_component_id<T, Unique>(), sizeof(T)); }

		bool release_storage(component_t componentID, bool update_entities = true) noexcept {
			if(fpda_size(storages) <= componentID) return false;
			if(storages[componentID].element_size == Storage::invalid) return false;
			storages[componentID] = Storage();

			if(update_entities) fp_iterate_named(entity_component_indices, e)
				if(fpda_size(*e) > componentID)
					(*e)[componentID] = Storage::invalid;
			return true;
		}
		template<typename T, size_t Unique = 0>
		inline bool release_storage(bool update_entities = true) noexcept { return release_storage(get_global_component_id<T, Unique>(), update_entities); }

		entity_t create_entity() noexcept {
			if(!freelist || fpda_empty(freelist)) {
				entity_t e = entity_component_indices ? fpda_size(entity_component_indices) : 0;
				if(e == 0) fpda_reserve(entity_component_indices, 16);
				fpda_push_back(entity_component_indices, nullptr);
				if(e == 0) return create_entity(); // Skip entity zero!
				return e;
			}

			entity_t e = *fpda_pop_back(freelist);
			if(entity_component_indices[e])
				fpda_free_and_null(entity_component_indices[e]);
			fpda_push_back(entity_component_indices[e], Storage::invalid);
			return e;
		}

		bool release_entity(entity_t e, bool clearMemory = true) noexcept {
			if(e >= fpda_size(entity_component_indices)) return false;

			if(clearMemory && storages && !fpda_empty(storages))
				for(size_t i = 0, size = fpda_size(storages); i < size; ++i)
					storages[i].remove(*this, e, i);

			if(entity_component_indices[e])
				fpda_free_and_null(entity_component_indices[e]);

			fpda_push_back(freelist, e);
			return true;
		}

		#define ECRS_ADD_COMPONENT_COMMON_A(componentID, element_size)\
			assert(fpda_size(entity_component_indices) > e);\
			if(!entity_component_indices[e] || fpda_empty(entity_component_indices[e]) || fpda_size(entity_component_indices[e]) <= componentID)\
				fpda_grow_to_size_and_initialize(entity_component_indices[e], componentID + 1, Storage::invalid);
		#define ECRS_ADD_COMPONENT_COMMON_B(componentID, element_size)\
			auto& storage = get_storage(componentID, element_size);\
			entity_component_indices[e][componentID] = storage.size()
		void* add_component(entity_t e, component_t componentID, size_t element_size) noexcept {
			ECRS_ADD_COMPONENT_COMMON_A(componentID, element_size);
			ECRS_ADD_COMPONENT_COMMON_B(componentID, element_size);
			return storage.get_or_allocate(e);
		}
		template<typename T, size_t Unique = 0>
		T& add_component(entity_t e) noexcept {
			component_t componentID = get_global_component_id<T, Unique>();
			{
				ECRS_ADD_COMPONENT_COMMON_A(componentID, sizeof(T));
				if constexpr(is_tag_v<T>) {
					entity_component_indices[e][componentID] = true; // Mark the tag as present
					return detail::tag_value<T>();
				}
				ECRS_ADD_COMPONENT_COMMON_B(componentID, sizeof(T));
				auto& res = storage.template get_or_allocate<T>(entity_component_indices[e][componentID]);

				if constexpr(detail::is_with_entity_v<T>)
					res.entity = e;
				return res;
			}
		}
		#undef ECRS_ADD_COMPONENT_COMMON

		bool remove_component(entity_t e, component_t componentID) noexcept {
			return get_storage(componentID).remove(*this, e, componentID);
		}
		template<typename Tcomponent, size_t Unique = 0>
		bool remove_component(entity_t e) noexcept {
			if constexpr(is_tag_v<Tcomponent>) {
				if(has_component<Tcomponent, Unique>(e))
					entity_component_indices[e][get_global_component_id<Tcomponent, Unique>()] = Storage::invalid;
			} else return get_storage<Tcomponent, Unique>().template remove<Tcomponent>(*this, e);
		}

		#define ECRS_GET_COMPONENT_COMMON(componentID)\
			assert(entity_component_indices);\
			assert(e < fpda_size(entity_component_indices));\
			assert(entity_component_indices[e]);\
			assert(fpda_size(entity_component_indices[e]) > componentID);\
			assert(entity_component_indices[e][componentID] != Storage::invalid);
		void* get_component(entity_t e, component_t componentID) noexcept {
			ECRS_GET_COMPONENT_COMMON(componentID);
			return get_storage(componentID).get(entity_component_indices[e][componentID]);
		}
		const void* get_component(entity_t e, component_t componentID) const noexcept {
			ECRS_GET_COMPONENT_COMMON(componentID);
			return get_storage(componentID).get(entity_component_indices[e][componentID]);
		}
		template<typename T, size_t Unique = 0>
		T& get_component(entity_t e) noexcept {
			if constexpr (is_tag_v<T>) return detail::tag_value<T>();
			component_t componentID = get_global_component_id<T, Unique>();
			ECRS_GET_COMPONENT_COMMON(componentID);
			return get_storage(componentID).template get<T>(entity_component_indices[e][componentID]);
		}
		template<typename T, size_t Unique = 0>
		const T& get_component(entity_t e) const noexcept {
			if constexpr (is_tag_v<T>) return detail::tag_value<T>();
			component_t componentID = get_global_component_id<T, Unique>();
			ECRS_GET_COMPONENT_COMMON(componentID);
			return get_storage(componentID).template get<T>(entity_component_indices[e][componentID]);
		}
		#undef ECRS_GET_COMPONENT_COMMON

		inline bool has_component(entity_t e, component_t componentID) const noexcept {
			return entity_component_indices && fpda_size(entity_component_indices) > e
				&& entity_component_indices[e] && fpda_size(entity_component_indices[e]) > componentID
				&& entity_component_indices[e][componentID] != Storage::invalid;
		}
		template<typename T, size_t Unique = 0>
		inline bool has_component(entity_t e) const noexcept {
			return has_component(e, get_global_component_id<T, Unique>());
		}

		void* get_or_add_component(entity_t e, component_t componentID, size_t element_size) noexcept {
			if(has_component(e, componentID))
				return get_component(e, componentID);
			else return add_component(e, componentID, element_size);
		}
		template<typename T, size_t Unique = 0>
		T& get_or_add_component(entity_t e) noexcept {
			if(has_component<T, Unique>(e))
				return get_component<T, Unique>(e);
			else return add_component<T, Unique>(e);
		}



	protected:
		template<typename Tcomponent, size_t Unique = 0>
		struct NotifySwapOp {
			inline void operator()(TrivialModule& self, entity_t a, entity_t b) const {
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
			entity_t b = _b.value_or(fpda_size(entity_component_indices) - 1);

			assert(a < fpda_size(entity_component_indices));
			assert(b < fpda_size(entity_component_indices));
			std::swap(entity_component_indices[a], entity_component_indices[b]);
		}

		template<typename... Tcomponents2notify>
		void swap_entities(entity_t a, std::optional<entity_t> _b = {}) {
			entity_t b = _b.value_or(fpda_size(entity_component_indices) - 1);

			[&, this]<std::size_t... I>(std::index_sequence<I...>) {
				(NotifySwapOp<detail::nth_type<I, Tcomponents2notify...>>{}(*this, a, b), ...);
			}(std::make_index_sequence<sizeof...(Tcomponents2notify)>{});

			swap_entities(a, b);
		}

#define ECRS_REORDER_ENTITIES_COMMON(_order, SWAP_ENTITIES)\
			size_t size = fp_view_size(_order);\
			assert(size == entity_count()); /* Require order to have an entry for every element in the array */\
			auto swaps = fp_alloca(size_t, size);\
			/* Transpose the order (it now stores what needs to be swapped with what) */\
			for(size_t i = 0; i < size; ++i)\
				swaps[*fp_view_access(size_t, order, i)] = i;\
			/* Update the data storage and book keeping */\
			for(size_t i = 0; i < size; ++i)\
				while(swaps[i] != i) {\
					SWAP_ENTITIES;\
					std::swap(swaps[swaps[i]], swaps[i]);\
				}
		void reorder_entities(fp_view(size_t) order) {
			ECRS_REORDER_ENTITIES_COMMON(order, swap_entities(swaps[i], i));
		}
		template<typename... Tcomponents2notify>
		void reorder_entities(fp_view(size_t) order) {
			ECRS_REORDER_ENTITIES_COMMON(order, swap_entities<Tcomponents2notify...>(swaps[i], i));
			// auto& _order = order;

			// assert(fp_view_size(_order) == entity_count()); /* Require order to have an entry for every element in the array */
			// auto swaps = fp_alloca(size_t, size);
			// /* Transpose the order (it now stores what needs to be swapped with what) */
			// for(size_t i = 0; i < size; ++i)
			// 	swaps[*fp_view_access(size_t, order, i)] = i;
			// /* Update the data storage and book keeping */\
			// for(size_t i = 0; i < size; ++i)
			// 	while(swaps[i] != i) {
			// 		swap_entities<Tcomponents2notify...>(swaps[i], i);
			// 		std::swap(swaps[swaps[i]], swaps[i]);
			// 	}
		}

	protected:
		template<typename Tcomponent>
		struct MonotonicOp {
			inline void operator()(TrivialModule& module, Storage& storage) const {
				storage.sort_monotonic<Tcomponent>(module);
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
			get_storage<Tcomponent, Unique>()->template sort_monotonic<Tcomponent, Unique>(*this);
		}
		void make_monotonic(fp_view(size_t) component_ids) {
			fp_view_iterate_named(size_t, component_ids, id)
				make_monotonic(*id);
		}
		void make_monotonic(size_t component_id) {
			get_storage(component_id).sort_monotonic(*this, component_id);
		}

		void make_all_monotonic() {
			fp_iterate_named(storages, storage) {
				if(storage->element_size == Storage::invalid) continue; // Only initialized storages can be made monotonic
				auto id = fp_iterate_calculate_index(storages, storage);
				storage->sort_monotonic(*this, id);
			}
		}

	};

	struct Module : public TrivialModule {
		bool should_leak = false; // Useful when shutting down, if we are closing we can just leave memory cleanup to the operating system for a bit of added performance!

		Module() = default;
		Module(const Module&) = delete; // Storages need to become copyable to change this...
		Module(Module&& o) { *this = std::move(o); }
		Module& operator=(const Module& o) = delete;
		Module& operator=(Module&& o) {
			free();
			entity_component_indices = std::exchange(o.entity_component_indices, nullptr);
			storages = std::exchange(o.storages, nullptr);
			freelist = std::exchange(o.freelist, nullptr);
			return *this;
		}

		~Module() {
			if(!should_leak) free();
		}
	};

	namespace detail {
		// Gets the entity associated with a specific component index
		inline entity_t get_entity(TrivialModule& module, size_t index, size_t component_id) {
			assert(module.entity_component_indices);
			for(size_t e = 0; e < fpda_size(module.entity_component_indices); ++e)
				if(fpda_size(module.entity_component_indices[e]) > component_id && module.entity_component_indices[e][component_id] == index)
					return e;
			return invalid_entity;
		}
		template<typename Tcomponent, size_t Unique = 0>
		inline entity_t get_entity(TrivialModule& module, size_t index) {
			return get_entity(module, index, get_global_component_id<Tcomponent, Unique>());
		}

		template<typename Tcomponent, size_t Unique = 0>
		inline entity_t get_entity(Storage& storage, TrivialModule& module, size_t index, std::optional<size_t> component_id = {}) {
			if constexpr(detail::is_with_entity_v<Tcomponent>)
				return (storage.data<Tcomponent>() + index)->entity;
			else if constexpr(std::is_same_v<Tcomponent, detail::void_like>)
				return get_entity(module, index, component_id.value());
			else return get_entity<Tcomponent, Unique>(module, index);
		}
	}


	template<typename Tcomponent, size_t Unique = 0>
	inline bool swap_impl(Storage* self, TrivialModule& module, size_t a, std::optional<size_t> _b = {}, bool swap_if_one_elementless = false, std::optional<size_t> _component_id = {}) {
		size_t b = _b.value_or(self->size() - 1);
		size_t component_id = _component_id.value_or(get_global_component_id<Tcomponent, Unique>());
		entity_t eA = detail::get_entity<Tcomponent, Unique>(*self, module, a, component_id);
		entity_t eB = detail::get_entity<Tcomponent, Unique>(*self, module, b, component_id);
		if (swap_if_one_elementless) {
			if (eA == invalid_entity && eB == invalid_entity) return false;
		}
		else if (eA == invalid_entity || eB == invalid_entity) return false;

		if constexpr(std::is_same_v<Tcomponent, detail::void_like>)
			self->swap(a, b);
		else self->swap<Tcomponent>(a, b);
		if (swap_if_one_elementless && eA == invalid_entity) {
			if(auto idx = module.entity_component_indices[eB]; fpda_size(idx) <= component_id) {
				fpda_grow_to_size_and_initialize(idx, component_id + 1, Storage::invalid);
				module.entity_component_indices[eB] = idx;
			}
			module.entity_component_indices[eB][component_id] = a;
		} else if (swap_if_one_elementless && eB == invalid_entity) {
			if(auto idx = module.entity_component_indices[eA]; fpda_size(idx) <= component_id) {
				fpda_grow_to_size_and_initialize(idx, component_id + 1, Storage::invalid);
				module.entity_component_indices[eA] = idx;
			}
			module.entity_component_indices[eA][component_id] = b;
		} else std::swap(
			module.entity_component_indices[eA][component_id],
			module.entity_component_indices[eB][component_id]
		);
		return true;
	}
	template<typename Tcomponent, size_t Unique /*= 0*/>
	bool Storage::swap(TrivialModule& module, size_t a, std::optional<size_t> b /*= {}*/, bool swap_if_one_elementless /*= false*/) {
		return swap_impl<Tcomponent, Unique>(this, module, a, b, swap_if_one_elementless);
	}
	inline bool Storage::swap(TrivialModule& module, size_t component_id, size_t a, std::optional<size_t> b /*= {}*/, bool swap_if_one_elementless /*= false*/) {
		return swap_impl<detail::void_like, 0>(this, module, a, b, swap_if_one_elementless, component_id);
	}


	inline bool Storage::remove(TrivialModule& module, entity_t e, size_t component_id) {
		size_t size = this->size();
		if(size == 0 || !module.entity_component_indices || e >= fpda_size(module.entity_component_indices)) return false;

		auto& indices = module.entity_component_indices[e];
		if(fpda_size(indices) <= component_id) return false;

		for(e = 0; e < fpda_size(module.entity_component_indices); ++e)
			if(fpda_size(module.entity_component_indices[e]) > component_id
				&& module.entity_component_indices[e][component_id] == size - 1
			)
				break;
		if(e >= fpda_size(module.entity_component_indices)) return false;

		swap(indices[component_id]);
		if(fpda_size(module.entity_component_indices[e]) <= component_id) fpda_grow_to_size_and_initialize(module.entity_component_indices[e], component_id + 1, Storage::invalid);
		std::swap(indices[component_id], module.entity_component_indices[e][component_id]);
		fpda_delete_range(raw, (size - 1) * element_size, element_size); // TODO: Could we pop back instead?
		indices[component_id] = invalid;
		return true;
	}


	template<typename Tcomponent, size_t Unique = 0>
	inline void reorder_impl(Storage* self, TrivialModule& module, fp_view(size_t) order, std::optional<size_t> _component_id = {}) {
		assert(fp_view_size(order) == self->size()); // Require order to have an entry for every element in the array
		if(self->size() <= 1) return; // Zero or one elements are always sorted
		size_t component_id = _component_id.value_or(get_global_component_id<Tcomponent, Unique>());

		size_t* swaps = fp_alloca(size_t, fp_view_size(order));
		// Transpose the order (it now stores what needs to be swapped with what)
		for(size_t i = 0; i < fp_view_size(order); i++)
			swaps[*fp_view_access(size_t, order, i)] = i;

		// Update the data storage and book keeping
		for(size_t i = 0; i < fp_view_size(order); ++i)
			while(swaps[i] != i) {
				if constexpr(std::is_same_v<Tcomponent, detail::void_like>)
					self->swap(module, component_id, swaps[i], i);
				else self->swap<Tcomponent, Unique>(module, swaps[i], i);
				std::swap(swaps[swaps[i]], swaps[i]);
			}
	}
	inline void Storage::reorder(TrivialModule& module, size_t component_id, fp_view(size_t) order) {
		reorder_impl<detail::void_like, 0>(this, module, order, component_id);
	}
	template<typename Tcomponent, size_t Unique /*= 0*/>
	inline void Storage::reorder(TrivialModule& module, fp_view(size_t) order) {
		reorder_impl<Tcomponent, Unique>(this, module, order);
	}


	template<typename Tcomponent, typename F, bool with_entities /*= false*/, size_t Unique /*= 0*/>
	void sort_impl(Storage* self, TrivialModule& module, const F& _comparator, std::optional<size_t> _component_id = {}) {
		size_t component_id = _component_id.value_or(get_global_component_id<Tcomponent, Unique>());
		// Create a list of indices
		size_t size = self->size();
		if(size <= 1) return; // Zero or one elements are always sorted
		size_t* order = fp_alloca(size_t, size);
		std::iota(order, fp_end(order), 0);

		constexpr static auto data = std::is_same_v<Tcomponent, detail::void_like> ? +[](Storage* self, size_t i) -> void* {
			return ((char*)self->raw) + i * self->element_size;
		} : +[](Storage* self, size_t i) -> void* {
			return self->data<Tcomponent>() + i;
		};

		// Sort the list of indices into the correct order (possibly alongside a list of entities)
		if constexpr(with_entities) {
			entity_t* entities = fp_alloca(entity_t, size);
			for(size_t i = size; i--; )
				entities[i] = detail::get_entity<Tcomponent, Unique>(*self, module, i, component_id);

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
			self->reorder(module, component_id, fp_view_make_full(size_t, order));
		else self->reorder<Tcomponent, Unique>(module, fp_view_make_full(size_t, order));
	}
	template<typename F, bool with_entities>
	inline void Storage::sort(TrivialModule& module, size_t component_id, const F& comparator) {
		sort_impl<detail::void_like, F, with_entities, 0>(this, module, comparator, component_id);
	}
	template<typename Tcomponent, typename F, bool with_entities /*= false*/, size_t Unique /*= 0*/>
	inline void Storage::sort(TrivialModule& module, const F& _comparator) {
		if constexpr(with_entities) {
			auto comparator = [&_comparator](void* a, entity_t aE, void* b, entity_t bE) {
				return _comparator((Tcomponent*)a, aE, (Tcomponent*)b, bE);
			};
			sort_impl<Tcomponent, decltype(comparator), with_entities, Unique>(this, module, comparator);
		} else {
			auto comparator = [&_comparator](void* a, void* b) {
				return _comparator((Tcomponent*)a, (Tcomponent*)b);
			};
			sort_impl<Tcomponent, decltype(comparator), with_entities, Unique>(this, module, comparator);
		}
	}
}