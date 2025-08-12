#pragma once

#include "ecrs.hpp"

namespace ecrs::serialize {

	template<typename T>
	struct component_info {
		size_t largest_size(const Storage& storage) const {
			return sizeof(T);
		}

		size_t size(const Storage& storage, size_t index) const {
			return sizeof(T);
		}

		fp::dynarray<std::byte> to_bytes(const Storage& storage, size_t index, std::optional<size_t> largest = {}) const {
			return fp::dynarray<std::byte>{nullptr}.concatenate_view_in_place({(std::byte*)&storage.get<T>(index), size(storage, index)});
		}

		size_t from_bytes(fp::view<std::byte> bytes, T& component, size_t largest = {}) const {
			assert(bytes.size() >= sizeof(T));
			std::memcpy(&component, bytes.data(), sizeof(T));
			return sizeof(T);
		}
		size_t from_bytes(fp::view<std::byte> bytes, const Storage& storage, T& component) const {
			return from_bytes(bytes, component, largest_size(storage));
		}
	};

	template<std::derived_from<RelationBase> R>
	struct component_info<R> {
		size_t largest_size(const Storage& storage) const {
			size_t out = 0;
			for(size_t i = 0; i < storage.size(); ++i)
				out = std::max(out, size(storage, i));
			return out;
		}

		size_t size(const Storage& storage, size_t index) const {
			return storage.get<R>(index).related.size() * sizeof(entity_t);
		}

		fp::dynarray<std::byte> to_bytes(const Storage& storage, size_t index, std::optional<size_t> largest = {}) const {
			if(!largest) largest = largest_size(storage);
			auto out = fp::dynarray<std::byte>{nullptr}.resize(*largest);
			auto& related = storage.get<R>(index).related;
			std::memcpy(out.raw, related.data(), *largest);
			return out;
		}

		size_t from_bytes(fp::view<std::byte> bytes, R& component, size_t largest) const {
			assert(bytes.size() >= largest);
			auto& related = component.related;
			if constexpr(requires{related.capacity();}) // if related is dynamicly sized...
				related.resize(largest / sizeof(entity_t));
			else related.__header = related.__default_header;
			std::memcpy(related.data(), bytes.data(), largest);
			if constexpr(requires{related.pop_back();}) 
				while(kanren::term_equivalence(kanren::Term{related.back()}, kanren::Term{0})) related.pop_back(); // Trim trailing zeros
			return largest;
		}
		size_t from_bytes(fp::view<std::byte> bytes, const Storage& storage, R& component) const {
			return from_bytes(bytes, component, largest_size(storage));
		}
	};

	// Tuint component_count;
	// Tuint size_of_each_component;
	// component data[component_count];
	template<std::integral Tuint, typename Tcomponent, size_t Unique = 0>
	fp::dynarray<std::byte> serialize(const TrivialModule& module) {
		constexpr static component_info<Tcomponent> info;
		fp::array<std::byte, sizeof(Tuint)> number_source;
		auto& storage = module.get_storage<Tcomponent, Unique>();
		Tuint largest = info.largest_size(storage);
		Tuint component_count = storage.size();

		auto out = fp::dynarray<std::byte>{nullptr}.reserve(2 * sizeof(Tuint) + largest * component_count);
		out.concatenate_view_in_place(fp::view<Tuint>::from_variable(component_count).byte_view());
		out.concatenate_view_in_place(fp::view<Tuint>::from_variable(largest).byte_view());

		for(size_t i = 0; i < component_count; ++i) {
			fp::raii::dynarray<std::byte> tmp = info.to_bytes(storage, i, largest);
			out.concatenate_in_place(tmp.raw);
		}
		return out;
	}

	template<std::integral Tuint, typename Tcomponent, size_t Unique = 0>
	size_t deserialize(TrivialModule& module, fp::view<std::byte> bytes) {
		constexpr static component_info<Tcomponent> info;
		size_t offset = 0;
		Tuint count = *(Tuint*)(bytes.data() + offset); assert_with_side_effects((offset += sizeof(Tuint)) <= bytes.size());
		Tuint largest = *(Tuint*)(bytes.data() + offset); assert_with_side_effects((offset += sizeof(Tuint)) <= bytes.size());
		assert(count * largest <= bytes.size());

		auto& storage = module.get_storage<Tcomponent, Unique>();
		storage.allocate(count);
		for(size_t i = 0; i < count; ++i) {
			auto jump = info.from_bytes(bytes.subview(offset), storage.template get<Tcomponent>(i), largest); assert_with_side_effects((offset += jump) <= bytes.size());
		}
		// storage.raw = (uint8_t*)components.data();
		return offset;
	}


	template<typename... Tcomponents>
	fp::dynarray<size_t> make_component_id_map() { // TODO: Can we make this an fp::array?
		fp::dynarray<size_t> out = nullptr;
		(out.push_back(get_global_component_id<Tcomponents, 0>()), ...);
		return out;
	}

	// Tuint component_type_count;
	// struct {
	//   Tuint component_count;
	//   Tuint size_of_each_component;
	//   component data[component_count];
	// } components[component_type_count]
	template<std::integral Tuint, typename... Tcomponents>
	fp::dynarray<std::byte> serialize_component_data(const TrivialModule& module) {
		fp::array<std::byte, sizeof(Tuint)> number_source;
		auto out = fp::dynarray<std::byte>{nullptr}.resize(sizeof(Tuint));

		*(Tuint*)out.data() = sizeof...(Tcomponents);
		constexpr static auto op = []<typename Tcomponent>(const TrivialModule& module, fp::dynarray<std::byte>& out) {
			fp::raii::dynarray<std::byte> tmp = serialize<Tuint, Tcomponent>(module);
			out.concatenate_in_place(tmp.raw);
		};
		(op.template operator()<Tcomponents>(module, out), ...);
		return out;
	}
	template<std::integral Tuint, typename... Tcomponents>
	size_t deserialize_component_data(TrivialModule& module, const fp::view<std::byte> bytes) {
		size_t offset = 0;

		Tuint component_type_count = *(Tuint*)bytes.data(); assert_with_side_effects((offset += sizeof(Tuint)) <= bytes.size());
		assert(component_type_count == sizeof...(Tcomponents));

		constexpr auto apply_component = []<typename Tcomponent>(const fp::view<std::byte>& bytes, size_t& offset, TrivialModule& module) {
			size_t consumed = deserialize<Tuint, Tcomponent>(module, bytes.subview(offset));
			assert_with_side_effects((offset += consumed) <= bytes.size());
		};
		(apply_component.template operator()<Tcomponents>(bytes, offset, module), ...);
		return offset;
	}



	inline static void apply_component_id_map(fp::dynarray<size_t>& out, const fp::dynarray<size_t> entity_component_indices, const fp::view<size_t> component_id_map) {
		out.resize(component_id_map.size());
		for(size_t i = 0; i < component_id_map.size(); ++i)
			if(entity_component_indices.size() <= component_id_map[i])
				out[i] = -1;
			else out[i] = entity_component_indices[component_id_map[i]];
	}
	inline static fp::dynarray<size_t> apply_component_id_map(const fp::dynarray<size_t> entity_component_indices, const fp::view<size_t> component_id_map) {
		fp::dynarray<size_t> out; apply_component_id_map(out, entity_component_indices, component_id_map); return out;
	}
	inline static void unapply_component_id_map(fp::dynarray<size_t>& entity_component_indices, const fp::view<size_t> mapped_entity_component_indices, const fp::view<size_t> component_id_map) {
		for(size_t i = 0; i < component_id_map.size(); ++i) {
			size_t unmapped = component_id_map[i];
			if(entity_component_indices.size() <= unmapped)
				entity_component_indices.grow_to_size(unmapped + 1, -1);
			if(mapped_entity_component_indices[i] >= 0)
				entity_component_indices[unmapped] = mapped_entity_component_indices[i];
		}
	}
	inline static fp::view<size_t> full_map(const TrivialModule& module) {
		thread_local static fp::raii::dynarray<size_t> full_map{nullptr};
		full_map.free_and_null();
		full_map.resize(fpda_size(module.storages));
		for(size_t i = 0; i < full_map.size(); ++i)
			full_map[i] = i; // Map to itself
		return full_map.view_full();
	}

	// Tuint entity_count;
	// Tuint component_id_map_size;
	// Tuint component_id_map[component_id_map_size];
	// Tuint entity_component_indices[entity_count][component_id_map_size];
	template<std::integral Tuint, typename... Tcomponents>
	fp::dynarray<std::byte> serialize_entity_data(const TrivialModule& module, std::optional<fp::view<size_t>> component_id_map = {}) {
		constexpr static auto concat_size_t_view = [](fp::dynarray<std::byte>& out, const fp::view<size_t> view) {
			if constexpr(sizeof(size_t) == sizeof(Tuint)) {
				out.concatenate_view_in_place(view.byte_view());
			} else {
				size_t offset = out.size();
				out.grow(view.size() * sizeof(Tuint));
				for(size_t i = 0; i < view.size(); ++i)
					((Tuint*)(out.data() + offset))[i] = view[i];
			}
		};

		size_t map_size = component_id_map.value_or(fp::view<size_t>{}).size();
		if(!component_id_map) component_id_map = full_map(module);
		auto out = fp::dynarray<std::byte>{nullptr}
			.reserve(sizeof(Tuint) * 2 + map_size * sizeof(Tuint) + component_id_map->size() * module.entity_count() * sizeof(Tuint))
			.grow(sizeof(Tuint) * 2);

		((Tuint*)out.data())[0] = module.entity_count();
		((Tuint*)out.data())[1] = map_size;
		if(component_id_map) concat_size_t_view(out, *component_id_map);

		fp::raii::dynarray<size_t> mapped{nullptr};
		for(entity_t e = 0; e < module.entity_count(); ++e) {
			apply_component_id_map((fp::dynarray<size_t>&)mapped, module.entity_component_indices[e], *component_id_map);
			concat_size_t_view(out, mapped.full_view());
		}
		return out;
	}
	template<std::integral Tuint>
	std::pair<size_t, fp::dynarray<size_t>> deserialize_entity_data(TrivialModule& module, const fp::view<std::byte> bytes) {
		size_t offset = 0;
		Tuint entity_count = *(Tuint*)(bytes.data() + offset); assert_with_side_effects((offset += sizeof(Tuint)) <= bytes.size());
		Tuint map_size = *(Tuint*)(bytes.data() + offset); assert_with_side_effects((offset += sizeof(Tuint)) <= bytes.size());

		auto component_id_map = fp::dynarray<size_t>{nullptr};
		if(map_size > 0) {
			component_id_map.resize(map_size);
			if constexpr(sizeof(Tuint) == sizeof(size_t)) {
				std::memcpy(component_id_map.data(), bytes.data() + offset, sizeof(Tuint) * map_size); assert_with_side_effects((offset += sizeof(Tuint) * map_size) <= bytes.size());
			} else for (size_t i = 0; i < map_size; ++i) {
				component_id_map[i] = *(Tuint*)(bytes.data() + offset); assert_with_side_effects((offset += sizeof(Tuint)) <= bytes.size());
			}
		} else component_id_map = fp::dynarray<size_t>{nullptr}.concatenate_view_in_place(full_map(module));

		auto entity_component_indices = fp::dynarray<fp::dynarray<size_t>>{(fp::dynarray<size_t>*)module.entity_component_indices};
		if(entity_component_indices.size() < entity_count) entity_component_indices.grow_to_size(entity_count, nullptr);
		auto tmp = fp::raii::dynarray<size_t>{nullptr}.resize(map_size);
		for (size_t e = 0; e < entity_count; ++e) {
			if constexpr(sizeof(Tuint) == sizeof(size_t)) {
				std::memcpy(tmp.raw, bytes.data() + offset, sizeof(size_t) * map_size); assert_with_side_effects((offset += sizeof(size_t) * map_size) <= bytes.size());
			} else for (size_t i = 0; i < map_size; ++i) {
				tmp[i] = *(Tuint*)(bytes.data() + offset); assert_with_side_effects((offset += sizeof(Tuint)) <= bytes.size());
			}
			if(!entity_component_indices[e].is_dynarray() && entity_component_indices[e].raw != nullptr) 
				entity_component_indices.free_and_null();
			unapply_component_id_map(entity_component_indices[e], tmp.full_view(), component_id_map.full_view());
		}
		module.entity_component_indices = (size_t**)entity_component_indices.raw;
		return {offset, component_id_map};
	}

	// entity_data
	// component_data
	template<std::integral Tuint, typename... Tcomponents>
	requires(sizeof...(Tcomponents) > 1)
	fp::dynarray<std::byte> serialize(const TrivialModule& module) {
		fp::raii::dynarray<size_t> map = make_component_id_map<Tcomponents...>();
		auto out = serialize_entity_data<Tuint, Tcomponents...>(module, map.full_view());
		fp::raii::dynarray<std::byte> tmp = serialize_component_data<Tuint, Tcomponents...>(module);
		return out.concatenate_in_place(tmp.raw);
	}
	template<std::integral Tuint, typename... Tcomponents>
	requires(sizeof...(Tcomponents) > 1)
	size_t deserialize(TrivialModule& module, const fp::view<std::byte> data) {
		size_t offset;
		fp::raii::dynarray<size_t> component_id_map;
		std::tie(offset, component_id_map) = deserialize_entity_data<Tuint>(module, data);
		return offset + deserialize_component_data<Tuint, Tcomponents...>(module, data.subview(offset));
	}
}