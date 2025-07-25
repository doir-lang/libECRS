#define DOCTEST_CONFIG_IMPLEMENT_WITH_MAIN
#include <doctest/doctest.h>

#define ECRS_IMPLEMENTATION
#include <ECRS/ecs.hpp>
#include <ECRS/adapter.hpp>

#ifdef FP_ENABLE_BENCHMARKING
	#include <nanobench.h>
#endif

TEST_SUITE("ECS") {
#ifndef FP_DISABLE_STRING_COMPONENT_LOOKUP
	TEST_CASE("ecrs::get_global_component_id") {
		FP_ZONE_SCOPED_NAMED("ecrs::get_global_component_id");
		{FP_ZONE_SCOPED_NAMED("First"); CHECK(ecrs::get_global_component_id<float>() == 0);}
		{FP_ZONE_SCOPED_NAMED("Second"); CHECK(ecrs::get_global_component_id<float>() == 0);}
		{FP_ZONE_SCOPED_NAMED("Int"); CHECK(ecrs::get_global_component_id<int>() == 1);}
		{FP_ZONE_SCOPED_NAMED("Lookup"); CHECK(ecrs::ecrs_component_id_from_name("float") == 0);}
		{FP_ZONE_SCOPED_NAMED("Lookup::NonExist"); CHECK(ecrs::ecrs_component_id_from_name("alice") == 2);}
		{FP_ZONE_SCOPED_NAMED("Lookup::NonExistNorCreate"); CHECK(ecrs::ecrs_component_id_from_name("bob", false) == -1);}
		{FP_ZONE_SCOPED_NAMED("Name");
			CHECK(std::string_view(ecrs::ecrs_component_id_name(0)) == "float");
			CHECK(std::string_view(ecrs::ecrs_component_id_name(1)) == "int");
			CHECK(std::string_view(ecrs::ecrs_component_id_name(2)) == "alice");
		}
		FP_FRAME_MARK;
	}
#endif

	TEST_CASE("ecrs::Basic") {
#ifdef FP_ENABLE_BENCHMARKING
		ankerl::nanobench::Bench().run("ecrs::Basic", []{
#endif
			FP_ZONE_SCOPED_NAMED("ecrs::Basic");
			ecrs::Module module;
			ecrs::entity_t e = module.create_entity();
			CHECK(e == 1);
			{
				FP_ZONE_SCOPED_NAMED("Add::Initial");
				CHECK((module.add_component<float>(e) = 5) == 5);
			}
			{
				FP_ZONE_SCOPED_NAMED("Get");
				CHECK(module.get_component<float>(e) == 5);
				module.get_component<float>(e) = 6;
				CHECK(module.get_component<float>(e) == 6);
				CHECK(module.has_component<int>(e) == false);
			}

			{
				FP_ZONE_SCOPED_NAMED("E2");
				ecrs::entity_t e2 = module.create_entity();
				CHECK(e2 == 2);
				CHECK((module.add_component<float>(e2) = 5) == 5);
				CHECK(module.get_component<float>(e) == 6);
			}
			// module.should_leak = true; // Don't bother cleaning up after ourselves...
#ifdef FP_ENABLE_BENCHMARKING
		});
#endif
		FP_FRAME_MARK;
	}

	TEST_CASE("ecrs::Removal") {
#ifdef FP_ENABLE_BENCHMARKING
		ankerl::nanobench::Bench().run("ecrs::Removal", []{
#endif
			FP_ZONE_SCOPED_NAMED("ecrs::Removal");
			ecrs::Module module;
			ecrs::entity_t e = module.create_entity();
			CHECK(e == 1);
			module.add_component<float>(e);
			CHECK(module.release_entity(e));

			e = module.create_entity();
			CHECK(e == 1);
			CHECK(module.has_component<float>(e) == false);

			ecrs::entity_t e2 = module.create_entity();
			CHECK(e2 == 2);
			ecrs::entity_t e3 = module.create_entity();
			CHECK(e3 == 3);
			module.add_component<float>(e) = 1;
			module.add_component<float>(e2) = 2;
			module.add_component<float>(e3) = 3;
			CHECK(module.get_component<float>(e) == 1);
			CHECK(module.get_component<float>(e2) == 2);
			CHECK(module.get_component<float>(e3) == 3);

			CHECK(module.remove_component<float>(e2) == true);
			CHECK(module.get_component<float>(e) == 1);
			CHECK(module.has_component<float>(e2) == false);
			CHECK(module.get_component<float>(e3) == 3);
			// module.should_leak = true; // Don't bother cleaning up after ourselves...
#ifdef FP_ENABLE_BENCHMARKING
		});
#endif
		FP_FRAME_MARK;
	}

	TEST_CASE("ecrs::SortByValue") {
#ifdef FP_ENABLE_BENCHMARKING
		ankerl::nanobench::Bench().run("ecrs::SortByValue", []{
#endif
			FP_ZONE_SCOPED_NAMED("ecrs::SortByValue");
			ecrs::Module module;
			auto e0 = module.create_entity();
			module.add_component<float>(e0) = 3;
			auto e1 = module.create_entity();
			module.add_component<float>(e1) = 27;
			auto e2 = module.create_entity();
			module.add_component<float>(e2) = 5;
			auto e3 = module.create_entity();
			module.add_component<float>(e3) = 0;

			auto& storage = module.get_storage<float>();
			storage.sort_by_value<float>(module);
			float* storage_as_float = storage.data<float>();
			CHECK(storage_as_float[0] == 0);
			CHECK(module.get_component<float>(e0) == 3);
			CHECK(storage_as_float[1] == 3);
			CHECK(module.get_component<float>(e1) == 27);
			CHECK(storage_as_float[2] == 5);
			CHECK(module.get_component<float>(e2) == 5);
			CHECK(storage_as_float[3] == 27);
			CHECK(module.get_component<float>(e3) == 0);
			// module.should_leak = true; // Don't bother cleaning up after ourselves...
#ifdef FP_ENABLE_BENCHMARKING
		});
#endif
		FP_FRAME_MARK;
	}

	TEST_CASE("ecrs::SortMontonic") {
#ifdef FP_ENABLE_BENCHMARKING
		ankerl::nanobench::Bench().run("ecrs::SortMontonic", []{
#endif
			FP_ZONE_SCOPED_NAMED("ecrs::SortMontonic");
			ecrs::Module module;
			auto e0 = module.create_entity();
			auto e1 = module.create_entity();
			auto e2 = module.create_entity();
			auto e3 = module.create_entity();
			module.add_component<float>(e3) = 0;
			module.add_component<float>(e0) = 3;
			module.add_component<float>(e2) = 5;
			module.add_component<float>(e1) = 27;

			auto& storage = module.get_storage<float>();
			storage.sort_monotonic<float>(module);
			// module.make_monotonic();
			float* storage_as_float = storage.data<float>();
			CHECK(storage_as_float[0] == 3);
			CHECK(module.get_component<float>(e0) == 3);
			CHECK(storage_as_float[1] == 27);
			CHECK(module.get_component<float>(e1) == 27);
			CHECK(storage_as_float[2] == 5);
			CHECK(module.get_component<float>(e2) == 5);
			CHECK(storage_as_float[3] == 0);
			CHECK(module.get_component<float>(e3) == 0);
			// module.should_leak = true; // Don't bother cleaning up after ourselves...
#ifdef FP_ENABLE_BENCHMARKING
		});
#endif
		FP_FRAME_MARK;
	}

	TEST_CASE("ecrs::WithEntity") {
#ifdef FP_ENABLE_BENCHMARKING
		ankerl::nanobench::Bench().run("ecrs::WithEntity", []{
#endif
			FP_ZONE_SCOPED_NAMED("ecrs::WithEntity");
			ecrs::Module module;
			ecrs::entity_t e = module.create_entity();
			CHECK(e == 1);
			CHECK((module.add_component<ecrs::with_entity<float>>(e).value = 5) == 5);
			CHECK(module.get_component<ecrs::with_entity<float>>(e).entity == e);
			CHECK(module.get_component<ecrs::with_entity<float>>(e) == 5);
			CHECK(module.get_component<ecrs::with_entity<float>>(e).entity == e);
			module.get_component<ecrs::with_entity<float>>(e).value = 6;
			CHECK(module.get_component<ecrs::with_entity<float>>(e) == 6);
			CHECK(module.get_component<ecrs::with_entity<float>>(e).entity == e);

			ecrs::entity_t e2 = module.create_entity();
			CHECK(e2 == 2);
			CHECK((module.add_component<ecrs::with_entity<float>>(e2).value = 5) == 5);
			CHECK(module.get_component<ecrs::with_entity<float>>(e2).entity == e2);
			CHECK(module.get_component<ecrs::with_entity<float>>(e2) == 5);
			CHECK(module.get_component<ecrs::with_entity<float>>(e) == 6);
			CHECK(module.get_component<ecrs::with_entity<float>>(e2).entity == e2);

			module.get_storage<ecrs::with_entity<float>>().sort_by_value<ecrs::with_entity<float>>(module);
			CHECK(module.get_component<ecrs::with_entity<float>>(e) == 6);
			CHECK(module.get_component<ecrs::with_entity<float>>(e).entity == e);
			CHECK(module.get_component<ecrs::with_entity<float>>(e2) == 5);
			CHECK(module.get_component<ecrs::with_entity<float>>(e2).entity == e2);

			module.get_storage<ecrs::with_entity<float>>().sort_monotonic<ecrs::with_entity<float>>(module);
			CHECK(module.get_component<ecrs::with_entity<float>>(e) == 6);
			CHECK(module.get_component<ecrs::with_entity<float>>(e).entity == e);
			CHECK(module.get_component<ecrs::with_entity<float>>(e2) == 5);
			CHECK(module.get_component<ecrs::with_entity<float>>(e2).entity == e2);
			// module.should_leak = true; // Don't bother cleaning up after ourselves...
#ifdef FP_ENABLE_BENCHMARKING
		});
#endif
		FP_FRAME_MARK;
	}

	TEST_CASE("ecrs::UniqueTag") {
#ifdef FP_ENABLE_BENCHMARKING
		ankerl::nanobench::Bench().run("ecrs::UniqueTag", []{
#endif
			FP_ZONE_SCOPED_NAMED("ecrs::UniqueTag");
			ecrs::Module module;
			auto e0 = module.create_entity();
			auto e1 = module.create_entity();
			auto e2 = module.create_entity();
			auto e3 = module.create_entity();
			module.add_component<float>(e3) = 0;
			module.add_component<float>(e0) = 3;
			module.add_component<float>(e2) = 5;
			module.add_component<float>(e1) = 27;
			module.add_component<float, 1>(e3) = 27;
			module.add_component<float, 1>(e0) = 5;
			module.add_component<float, 1>(e2) = 3;
			module.add_component<float, 1>(e1) = 0;

			{
				auto& storage = module.get_storage<float>();
				storage.sort_monotonic<float>(module);
				float* storage_as_float = storage.data<float>();
				CHECK(storage_as_float[0] == 3);
				CHECK(module.get_component<float>(e0) == 3);
				CHECK(storage_as_float[1] == 27);
				CHECK(module.get_component<float>(e1) == 27);
				CHECK(storage_as_float[2] == 5);
				CHECK(module.get_component<float>(e2) == 5);
				CHECK(storage_as_float[3] == 0);
				CHECK(module.get_component<float>(e3) == 0);
			}
			{
				auto& storage = module.get_storage<float, 1>();
				storage.sort_monotonic<float, 1>(module);
				float* storage_as_float = storage.data<float>();
				CHECK(storage_as_float[0] == 5);
				CHECK(module.get_component<float, 1>(e0) == 5);
				CHECK(storage_as_float[1] == 0);
				CHECK(module.get_component<float, 1>(e1) == 0);
				CHECK(storage_as_float[2] == 3);
				CHECK(module.get_component<float, 1>(e2) == 3);
				CHECK(storage_as_float[3] == 27);
				CHECK(module.get_component<float, 1>(e3) == 27);
			}
			// module.should_leak = true; // Don't bother cleaning up after ourselves...
#ifdef FP_ENABLE_BENCHMARKING
		});
#endif
		FP_FRAME_MARK;
	}

	// TEST_CASE("ecrs::Query") {
	// 	ZoneScoped;
	// 	ecrs::module module;
	// 	*module.add_component<float>(module.create_entity()) = 1;
	// 	*module.add_component<float>(module.create_entity()) = 2;
	// 	*module.add_component<float>(module.create_entity()) = 3;

	// 	for(auto [e, value]: ecrs::query<ecrs::include_entity, float>(module))
	// 		CHECK(e + 1 == value);

	// 	for(auto [e, value]: ecrs::query<ecrs::include_entity, std::optional<float>>(module))
	// 		CHECK(e + 1 == *value);

	// 	for(auto [e, value]: ecrs::query<ecrs::include_entity, ecrs::or_<float, double>>(module)) {
	// 		CHECK(e + 1 == std::get<std::reference_wrapper<float>>(value));
	// 		REQUIRE_THROWS((void)std::get<std::reference_wrapper<double>>(value));
	// 	}
	// }

	TEST_CASE("ecrs::Typed") {
#ifdef FP_ENABLE_BENCHMARKING
		ankerl::nanobench::Bench().run("ecrs::Typed", []{
#endif
			FP_ZONE_SCOPED_NAMED("ecrs::Typed");
			ecrs::Module module;
			ecrs::entity_t e = module.create_entity();
			module.add_component<float>(e) = 5;
			size_t floatID = ecrs::get_global_component_id<float>();
			auto& storage = get_adapted_storage<ecrs::typed::Storage<float>>(module);
			CHECK(storage.get(module.entity_component_indices[e][floatID]) == 5);
			// module.should_leak = true; // Don't bother cleaning up after ourselves...
#ifdef FP_ENABLE_BENCHMARKING
		});
#endif
		FP_FRAME_MARK;
	}

	TEST_CASE("ecrs::Hashtable") {
#ifdef FP_ENABLE_BENCHMARKING
		ankerl::nanobench::Bench().run("ecrs::Hashtable", []{
#endif
			FP_ZONE_SCOPED_NAMED("ecrs::Hashtable");
			using C = ecrs::hashtable::Storage<int>::component_type;

			ecrs::Module module;
			ecrs::entity_t first = module.create_entity();
			ecrs::entity_t current = first;
			for(size_t i = 0; i < 100; ++i) {
				get_key_and_mark_occupied<int>(module.add_component<C>(current)) = current;
				current = module.create_entity();
			}

			auto& hashtable = get_adapted_storage<ecrs::hashtable::Storage<int>>(module);
			CHECK(hashtable.rehash(module) == true);
			// CHECK(hashtable.rehash(module) == true);
			for(ecrs::entity_t e = first; e < first + 50; ++e) {
				CHECK(*hashtable.find(e) == e);
				CHECK(get_key<int>(module.get_component<C>(*hashtable.find(e))) == e);
			}
			// module.should_leak = true; // Don't bother cleaning up after ourselves...
#ifdef FP_ENABLE_BENCHMARKING
		});
#endif
		FP_FRAME_MARK;
	}

	// TEST_CASE("ecrs::component_id_free_maps") {
	// 	FP_ZONE_SCOPED_NAMED("ecrs::component_id_free_maps");
	// 	ecrs::component_id_free_maps();
	// }
}