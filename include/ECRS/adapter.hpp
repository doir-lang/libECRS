#ifndef __ECS_ADAPTER_HPP__
#define __ECS_ADAPTER_HPP__

#include "ecrs.hpp"

namespace ecrs {
	template<typename T>
	T& get_adapted_storage(TrivialModule& module) {
		auto& res = module.get_storage<typename T::component_type>();
		return {*(T*)&res};
	}

	namespace typed {
		template<typename Tcomponent, size_t Unique = 0>
		struct Storage : public ecrs::Storage {
			using Base = ecrs::Storage;
			using component_type = Tcomponent;
			using Base::Base;
			inline const Tcomponent& get(entity_t e) const { return Base::get<Tcomponent>(e); }
			inline Tcomponent& get(entity_t e) { return Base::get<Tcomponent>(e); }
			void allocate(size_t count = 1) { Base::allocate<Tcomponent>(count); }
			inline Tcomponent& get_or_allocate(entity_t e) { return Base::get_or_allocate<Tcomponent>(e); }
			inline bool remove(TrivialModule& module, entity_t e) { return Base::remove<Tcomponent, Unique>(module, e); }
			inline void reorder(TrivialModule& module, fp_view(size_t) order) { Base::reorder<Tcomponent, Unique>(module, order); }
			template<typename F, bool with_entities = false>
			inline void sort(TrivialModule& module, const F& comparator) { Base::sort<Tcomponent, F, with_entities, Unique>(module, comparator); }
			inline void sort_by_value(TrivialModule& module) { Base::sort_by_value<Tcomponent, Unique>(module); }
			inline void sort_monotonic(TrivialModule& module) { Base::sort_monotonic<Tcomponent, Unique>(module); }
			inline bool swap(size_t a, std::optional<size_t> b = {}) { return Base::swap<Tcomponent>(a, b); }
			inline bool swap(TrivialModule& module, size_t a, std::optional<size_t> b = {}, bool swap_if_one_elementless = false) {
				return Base::swap<Tcomponent, Unique>(module, a, b, swap_if_one_elementless);
			}

			inline Tcomponent* data() { return Base::data<Tcomponent>(); }
			inline const Tcomponent* data() const { return Base::data<Tcomponent>(); }
			inline fp_view(Tcomponent) view() { return {data(), Base::size()}; }
			inline fp_view(const Tcomponent) view() const { return {data(), Base::size()}; }
		};
	}

	namespace hashtable {
		template<typename T>
		struct is_costly_to_compare : public std::false_type {};
		template<>
		struct is_costly_to_compare<std::string> : public std::true_type {};
		template<>
		struct is_costly_to_compare<std::string_view> : public std::true_type {};

		template<typename T>
		constexpr static bool is_costly_to_compare_v = is_costly_to_compare<T>::value;

		namespace detail {
			struct hash_entry_base {
				uint32_t hopInfo = 0;  // Bitmask to track neighbors (occupied stored in highest bit)

				bool is_occupied() const {
					return hopInfo & (1 << 31);
				}
				void set_occupied(bool value) {
					if(value) hopInfo |=(1 << 31);
					else hopInfo &= ~(1 << 31);
				}
			};

			template<typename Tkey, typename Tvalue>
			struct hash_entry : public hash_entry_base {
				Tkey key;
				Tvalue value;

				static inline void swap_entities(hash_entry& e, ecrs::entity_t eA, ecrs::entity_t eB)
					requires(requires(Tkey t){Tkey::swap_entities(t, eA, eB);} || requires(Tvalue t){Tvalue::swap_entities(t, eA, eB);})
				{
					if constexpr(requires(Tkey t){Tkey::swap_entities(t, eA, eB);})
						Tkey::swap_entities(e.key, eA, eB);
					if constexpr(requires(Tvalue t){Tvalue::swap_entities(t, eA, eB);})
						Tvalue::swap_entities(e.value, eA, eB);
				}
			};
			template<typename Tkey>
			struct hash_entry<Tkey, void> : public hash_entry_base {
				Tkey key;

				static inline void swap_entities(hash_entry& e, ecrs::entity_t eA, ecrs::entity_t eB)
					requires(requires(Tkey t){Tkey::swap_entities(t, eA, eB);})
				{
					Tkey::swap_entities(e.key, eA, eB);
				}
			};

			template<typename Tkey, typename Tvalue>
			struct hash_entry_with_hash: public hash_entry<Tkey, Tvalue> {
				size_t hash;

				using Entry = hash_entry<Tkey, Tvalue>;
				static inline void swap_entities(hash_entry_with_hash& e, ecrs::entity_t eA, ecrs::entity_t eB)
					requires(requires(Entry e){Entry::swap_entities(e, eA, eB);})
				{
					Entry::swap_entities(e, eA, eB);
				}
			};
		}

		template<typename Tkey, typename Tvalue = void>
		struct component_wrapper : public with_entity<std::conditional_t<
			is_costly_to_compare_v<Tkey>, detail::hash_entry_with_hash<Tkey, Tvalue>, detail::hash_entry<Tkey, Tvalue>>
		> {
			using Entry = std::conditional_t<is_costly_to_compare_v<Tkey>, detail::hash_entry_with_hash<Tkey, Tvalue>, detail::hash_entry<Tkey, Tvalue>>;
			using Base = with_entity<Entry>;
			static inline void swap_entities(component_wrapper& w, ecrs::TrivialModule& module, ecrs::entity_t eA, ecrs::entity_t eB) {
				Base::swap_entities(w, module, eA, eB);
				if constexpr(requires(Entry e){Entry::swap_entities(e, module, eA, eB);})
					Entry::swap_entities(w.value, module, eA, eB);
			}
		};

		/*constexpr*/ size_t one_over_one_minus(float factor)
#ifdef ECS_IMPLEMENTATION
		{
			assert(0 < factor); assert(factor < 1);
			return std::round(1 / (1 - factor));
		}
#else
		;
#endif

		// An adapter over a component storage which treats the underlying data as a hopscotch hash table
		template<
			typename Tkey,
			typename Tvalue = void,
			typename Hash = std::hash<Tkey>,
			size_t Unique = 0,
			size_t OneOverOneMinusMaxLoadFactor = /*one_over_one_minus(.95)*/20,
			size_t NeighborhoodSize = 8,
			size_t MaxRetries = 5
		>
		class Storage
			: public typed::Storage<
				component_wrapper<ecrs::detail::remove_with_entity_t<Tkey>, ecrs::detail::remove_with_entity_t<Tvalue>>, Unique
			>
		{
		protected:
			using key_type = ecrs::detail::remove_with_entity_t<Tkey>;
			using value_type = ecrs::detail::remove_with_entity_t<Tvalue>;
			using component_t = component_wrapper<key_type, value_type>;
			using Base = typed::Storage<component_t, Unique>;

			static constexpr float maxLoadFactor = 1 - 1.0 / OneOverOneMinusMaxLoadFactor;
			static constexpr float store_hash = is_costly_to_compare_v<key_type>;

			size_t current_size() const {
				size_t size = 0;
				for(auto& e: Base::span())
					if(e.is_occupied())
						++size;
				return size;
			}

			inline float load_factor() const {
				return float(current_size()) / Base::size();
			}

			inline size_t hash(const key_type& key) const {
				return Hash{}(key) % std::max<size_t>(Base::size(), 1);
			}

			std::optional<size_t> find_position(const key_type& key) const {
				size_t hash = this->hash(key);
				auto data = Base::data();
				auto size = Base::size();
				for(size_t i = 0; i < NeighborhoodSize; ++i) {
					size_t probe = (hash + i) % size;
					if constexpr(store_hash) if(!data[probe]->is_occupied() || data[probe]->hash != hash) continue;
					if(data[probe]->is_occupied() && data[probe]->key == key)
						return probe;
				}
				return {};
			}

			std::optional<size_t> find_empty_spot(size_t start) const {
				auto data = Base::data();
				auto size = Base::size();
				for(size_t i = 0; i < NeighborhoodSize; ++i) {
					size_t probe = (start + i) % size;
					if(!data[probe]->is_occupied())
						return probe;
				}
				return {};
			}

			std::optional<size_t> find_nearest_neighbor(size_t start) const {
				auto data = Base::data();
				auto size = Base::size();
				for(size_t j = 0; j < NeighborhoodSize; ++j) {
					size_t probe = (start + j) % size;
					if((data[start]->hopInfo & (1 << j)) && !data[probe]->is_occupied())
						return probe;
				}
				return {};
			}

			inline bool is_in_neighborhood(size_t start, size_t needle) const {
				if(NeighborhoodSize > Base::size()) return true;
				size_t end = (start + NeighborhoodSize) % Base::size();
				if(start <= end)
					return needle >= start && needle <= end; // TODO: should be < instead?
				else // The neighborhood range wraps around the end of the table
					return needle >= start || needle <= end;
			}

			inline bool double_size_and_rehash(TrivialModule& module, size_t retries = 0) {
				size_t size = Base::size();
				Base::allocate(size);
				auto data = Base::data();
				for(size_t i = size, size = Base::size(); i < size; ++i)
					data[i] = {}; // TODO: Necessary?

				// Make sure all of the new cells are initialized with invalid entities
				for(size_t i = 0; i < size; ++i)
					if(!data[i]->is_occupied())
						data[i].entity = invalid_entity;
				return rehash(module, retries, true);
			}

			bool rehash(TrivialModule& module, size_t retries, bool resized = false) {
				// Clear the neighborhood information
				auto data = Base::data();
				size_t size = Base::size(), half = size / 2;
				if(size == 0) return false;
				for(size_t i = 0; i < size; ++i) {
					auto dbg = data[i];
					bool occupied = data[i]->is_occupied();
					data[i]->hopInfo = 0;
					if(resized && occupied && i < half && (i % 2) == 1) { // Distribute every other element to the second half of the newly resized space
						if(!Base::swap(module, i, size - i, true)) return false;
						data[size - i]->set_occupied(occupied);
						data[i]->set_occupied(false);
					} else data[i]->set_occupied(occupied);
				}

				// Traverse through the old table and "reinsert" elements into the table
				for(size_t i = 0; i < size; ++i)
					if(data[i]->is_occupied()) {
						size_t hash = this->hash(data[i]->key);

						// If the value is already in the correct neighborhood... no need to move around just mark as present
						if(is_in_neighborhood(hash, i)) {
							if constexpr(store_hash) data[i]->hash = hash;
							size_t distance = i > hash ? i - hash : size - (hash - i);
							data[hash]->hopInfo |= (1 << distance);
							continue;
						}

						// Find an empty spot in the new table starting from the new hash value
						auto emptyIndex = find_empty_spot(hash);
						if(!emptyIndex) {
							if(retries >= MaxRetries) return false;
							return double_size_and_rehash(module, retries + 1); // TODO: We can probably use a better strategy than "resize and try again"
						}

						// Move the element to its new position in the table
						size_t hopInfoI = data[i]->hopInfo, hopInfoEmpty = data[*emptyIndex]->hopInfo;
						if(!Base::swap(module, *emptyIndex, i, true)) return false;
						data[i]->hopInfo = hopInfoI;
						data[i]->set_occupied(false);
						data[*emptyIndex]->hopInfo = hopInfoEmpty;
						data[*emptyIndex]->set_occupied(true);

						// Mark it as present in the element it hashes to
						size_t distance = *emptyIndex > hash ? *emptyIndex - hash : size - (hash - *emptyIndex);
						data[hash]->hopInfo |= (1 << distance);
					}

				return true;
			}

		public:
			using component_type = component_t;

			inline bool rehash(TrivialModule& module) {
				return rehash(module, 0);
			}

			inline std::optional<entity_t> find(const key_type& key) const {
				if(Base::size() == 0) return {};
				if(auto index = find_position(key); index)
					return Base::data()[*index].entity;
				return {};  // Key not found
			}

			inline std::optional<entity_t> rehash_and_find(TrivialModule& module, const key_type& key) {
				if(!rehash(module)) return {};
				return find(key);
			}
		};

		template<typename Tkey, typename Tvalue = void>
		inline void mark_occupied(component_wrapper<Tkey, Tvalue>& comp) {
			comp->set_occupied(true);
		}

		template<typename Tkey, typename Tvalue = void>
		inline Tkey& get_key(component_wrapper<Tkey, Tvalue>& comp) {
			return comp->key;
		}
		template<typename Tkey, typename Tvalue = void>
		inline const Tkey& get_key(const component_wrapper<Tkey, Tvalue>& comp) {
			return comp->key;
		}

		template<typename Tkey, typename Tvalue = void>
		inline Tkey& get_key_and_mark_occupied(component_wrapper<Tkey, Tvalue>& comp) {
			mark_occupied<Tkey, Tvalue>(comp);
			return get_key<Tkey, Tvalue>(comp);
		}

		template<typename Tkey, typename Tvalue = void>
			requires((!std::is_same_v<Tvalue, void>))
		inline Tvalue& get_value(component_wrapper<Tkey, Tvalue>& comp) {
			return comp.value.value;
		}
		template<typename Tkey, typename Tvalue = void>
			requires((!std::is_same_v<Tvalue, void>))
		inline const Tvalue& get_value(const component_wrapper<Tkey, Tvalue>& comp) {
			return comp.value.value;
		}
	}

	namespace detail {
		// Make sure machinery in module can detect that component wrapers are a type of with_entity
		template<typename Tkey, typename Tvalue>
		struct is_with_entity<ecrs::hashtable::component_wrapper<Tkey, Tvalue>> : public std::true_type {};
	}

	using hashtable::get_key;
	using hashtable::get_key_and_mark_occupied;
	using hashtable::get_value;
}

#endif // __ECS_ADAPTER_HPP__