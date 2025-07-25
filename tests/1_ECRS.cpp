#include "fp/string.hpp"
#include <doctest/doctest.h>

#include <iostream>
#include <ECRS/ecrs.hpp>

#ifdef FP_ENABLE_BENCHMARKING
	#include <nanobench.h>
#endif

#include "../libfp/tests/profile.config.hpp"

namespace kr = ecrs::kanren;

TEST_SUITE("ECRS") {
	TEST_CASE("ecrs::simpson") {
		ecrs::RelationalModule mod; ecrs::Entity::set_current_module(mod);
		ecrs::Entity bart = mod.create_entity();
		bart.add_component<fp::raii::string>() = "Bart"_fp;
		ecrs::Entity lisa = mod.create_entity();
		lisa.add_component<fp::raii::string>() = "Lisa"_fp;
		ecrs::Entity homer = mod.create_entity();
		homer.add_component<fp::raii::string>() = "Homer"_fp;
		ecrs::Entity marg = mod.create_entity();
		marg.add_component<fp::raii::string>() = "Marg"_fp;
		ecrs::Entity abraham = mod.create_entity();
		abraham.add_component<fp::raii::string>() = "Abraham"_fp;
		ecrs::Entity jackie = mod.create_entity();
		jackie.add_component<fp::raii::string>() = "Jackie"_fp;

		struct parent : public ecrs::Relation<> {};
		bart.add_component<parent>() = {{homer, marg}};
		lisa.add_component<parent>() = {{homer, marg}};
		homer.add_component<parent>() = {{abraham}};
		marg.add_component<parent>() = {{jackie}};

		struct male : public ecrs::Tag {};
		bart.add_component<male>();
		homer.add_component<male>();
		abraham.add_component<male>();

		struct female : public ecrs::Tag {};
		lisa.add_component<female>();
		marg.add_component<female>();
		jackie.add_component<female>();

		auto ancestor = [](const kr::Term& child, const kr::Term& ancestor) -> kr::Goal auto {
			auto impl = [](const kr::Term& child, const kr::Term& ancestor, auto impl) -> std::function<std::generator<kr::State>(kr::State)> {
				return kr::next_variables([=](kr::Variable tmp) -> kr::Goal auto {
					return kr::disjunction(
						ecrs::related_entities<parent>(child, ancestor),
						kr::conjunction(ecrs::related_entities<parent>(child, {tmp}), impl({tmp}, ancestor, impl))
					);
				});
			};
			return impl(child, ancestor, impl);
		};

		auto x = mod.next_logic_variable();
		auto y = mod.next_logic_variable();
		auto g = ancestor({x}, {y});

		for (const auto& [v, val] : kr::all_substitutions(g, mod.logic_state))
			if (std::holds_alternative<kr::Variable>(v) && std::holds_alternative<ecrs::Entity>(val)) {
				auto e = std::get<ecrs::Entity>(val);
				auto id = std::get<kr::Variable>(v).id;
				std::cout << "Var " << id << " = " << e.get_component<fp::raii::string>().raw << "\n";
			}
	}

	TEST_CASE("ecrs::type_inference") {
		ecrs::RelationalModule mod; ecrs::Entity::set_current_module(mod);
		ecrs::Entity i32 = mod.create_entity();
		i32.add_component<fp::raii::string>() = "i32"_fp;
		ecrs::Entity u1 = mod.create_entity();
		u1.add_component<fp::raii::string>() = "u1"_fp;
		ecrs::Entity pu8 = mod.create_entity();
		pu8.add_component<fp::raii::string>() = "pu8"_fp;

		struct function_types: public ecrs::Relation<std::dynamic_extent, true> {}; // First is return, rest are parameters
		struct arguments: public ecrs::Relation<> {};
		struct call : public ecrs::Relation<1> {};
		struct type_of: public ecrs::Relation<1, true> {};

		ecrs::Entity A = mod.create_entity();
		A.add_component<type_of>() = {{{i32}}};
		A.add_component<fp::raii::string>() = "A"_fp;
		ecrs::Entity B = mod.create_entity();
		B.add_component<type_of>() = {{{i32}}};
		B.add_component<fp::raii::string>() = "B"_fp;

		auto T = mod.next_logic_variable();
		ecrs::Entity add = mod.create_entity();
		add.add_component<function_types>() = {{{T}, {T}, {T}}};
		add.add_component<fp::raii::string>() = "add"_fp;

		ecrs::Entity call = mod.create_entity();
		call.add_component<struct call>() = {{add}};
		call.add_component<arguments>() = {{A, B}};

		constexpr auto typecheck_function = [](ecrs::Entity function, ecrs::Entity call) {
			return kr::next_variables([=](kr::Variable func_type, kr::Variable param_types, kr::Variable args, kr::Variable arg_types) {
				return kr::conjunction(
					ecrs::related_entities_list<function_types>({function}, {func_type}),
					kr::split_tail({func_type}, {param_types}),
					ecrs::related_entities_list<arguments>({call}, {args}),
					kr::map({args}, {arg_types}, ecrs::related_entities<type_of>),
					kr::eq({param_types}, {arg_types})
				);
			});
		};
		auto g = typecheck_function(add, call);

		kr::Term res;
		for (const auto& [v, val] : kr::all_substitutions(g, mod.logic_state))
			if (std::holds_alternative<kr::Variable>(v)) {
				auto var = std::get<kr::Variable>(v);
				if(var == T) res = val;
			}
		CHECK(ecrs::kanren::term_equivalence(res, {i32}));
	}
}