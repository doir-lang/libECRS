#include <doctest/doctest.h>

#include <ECRS/serialize.hpp>
#include <fstream>

#ifdef FP_ENABLE_BENCHMARKING
	#include <nanobench.h>
#endif

#include "../libfp/tests/profile.config.hpp"

namespace ecrs::serialize {
	template<>
	struct component_info<fp::raii::string> {
		size_t largest_size(const Storage& storage) const {
			size_t out = 0;
			for(size_t i = 0; i < storage.size(); ++i)
				out = std::max(out, size(storage, i));
			return out;
		}

		size_t size(const Storage& storage, size_t index) const {
			return storage.get<fp::raii::string>(index).size() + sizeof(size_t);
		}

		fp::dynarray<std::byte> to_bytes(const Storage& storage, size_t index, std::optional<size_t> largest = {}) const {
			if(!largest) largest = largest_size(storage);
			auto& string = storage.get<fp::raii::string>(index);
			auto out = fp::dynarray<std::byte>{nullptr}.reserve(*largest).grow(sizeof(size_t));
			*(size_t*)out.data() = string.size();
			out.concatenate_view_in_place({(std::byte*)string.data(), string.size()});
			if(out.size() == *largest) return out;
			return out.grow(*largest - out.size(), std::byte{0});
		}

		size_t from_bytes(fp::view<std::byte> bytes, fp::raii::string& string, size_t largest) const {
			assert(bytes.size() >= largest);
			auto size = *(size_t*)bytes.data();
			string.resize(size);
			std::memcpy(string.data(), bytes.data() + sizeof(size_t), size);
			return largest;
		}
		size_t from_bytes(fp::view<std::byte> bytes, const Storage& storage, fp::raii::string& component) const {
			return from_bytes(bytes, component, largest_size(storage));
		}
	};
}

TEST_SUITE("ecrs::serialize") {
    TEST_CASE("round_trip") {
        ecrs::RelationalModule mod; ecrs::Entity::set_current_module(mod);
		ecrs::Entity i32 = mod.create_entity();
		i32.add_component<fp::raii::string>() = "i32"_fp;
		ecrs::Entity u1 = mod.create_entity();
		u1.add_component<fp::raii::string>() = "u1"_fp;
		ecrs::Entity pu8 = mod.create_entity();
		pu8.add_component<fp::raii::string>() = "pu8"_fp;

		struct function_types: public ecrs::Relation<std::dynamic_extent> {}; // First is return, rest are parameters
		struct arguments: public ecrs::Relation<> {};
		struct call : public ecrs::Relation<1> {};
		struct type_of: public ecrs::Relation<1> {};

		ecrs::Entity A = mod.create_entity();
		A.add_relation<type_of>() = {{i32}};
		A.add_component<fp::raii::string>() = "A"_fp;
		ecrs::Entity B = mod.create_entity();
		B.add_relation<type_of>() = {{i32}};
		B.add_component<fp::raii::string>() = "B"_fp;

		ecrs::Entity add = mod.create_entity();
		add.add_relation<function_types>() = {{i32}, {i32}, {i32}};
		add.add_component<fp::raii::string>() = "add"_fp;

		ecrs::Entity call = mod.create_entity();
		call.add_relation<struct call>() = {add};
		call.add_relation<arguments>() = {A, B};

		fp::raii::dynarray<std::byte> bytes = ecrs::serialize::serialize<size_t, fp::raii::string, type_of, function_types, struct call, arguments>(mod);
		CHECK(bytes.size() == 594);
        bytes = ecrs::serialize::serialize<uint8_t, fp::raii::string, type_of, function_types, struct call, arguments>(mod);
		CHECK(bytes.size() == 188);
		// {
		// 	std::ofstream fout("dump.bin", std::ios::binary);
		// 	fout.write((char*)bytes.data(), bytes.size());
		// }

		{
			ecrs::RelationalModule mod; ecrs::Entity::set_current_module(mod);
			auto consumed = ecrs::serialize::deserialize<uint8_t, fp::raii::string, type_of, function_types, struct call, arguments>(mod, bytes.full_view());
			CHECK(consumed == bytes.size());
			CHECK(A.get_related_entities<type_of>()[0] == i32);
			CHECK(B.get_related_entities<type_of>()[0] == i32);
			for(auto t: add.get_related_entities<function_types>())
				CHECK(t == i32);
			CHECK(call.get_related_entities<struct call>()[0] == add);
			auto args = call.get_related_entities<arguments>();
			CHECK(args[0] == A);
			CHECK(args[1] == B);
		}
    }
}