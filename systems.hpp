#pragma once

#include "context.hpp"
#ifdef ECRS_PARALLEL_SYSTEMS
	#include <execution>
#endif

namespace ecrs::system {
	template<typename... Targs, std::invocable<context&, entity_t, Targs...> Tfunc>
	auto sequential(Tfunc&& func) {
		return [func](context& context, Targs... args) -> bool {
			bool valid = true;
			for(entity_t e = 0; e < context.entity_component_indices.size(); e++)
				valid &= func(context, e, std::forward<Targs>(args)...);
			return valid;
		};
	}

	template<typename... Tsystems>
	auto sequential(Tsystems... systems) {
		return [=](context& context, auto... args) -> bool {
			return (systems(context, args...) && ...);
		};
	}

	template<typename... Targs>
	auto sequential(const std::vector<std::function<bool(context&, entity_t, Targs...)>>& systems) {
		return [=](context& context, auto... args) -> bool {
			bool valid = true;
			for(auto& system: systems)
				valid &= system(context, args...);
			return valid;
		};
	}

#ifdef ECRS_PARALLEL_SYSTEMS
	template<typename... Targs, std::invocable<context&, entity_t, Targs...> Tfunc>
	auto parallel(Tfunc&& func) {
		return [func](context& context, Targs... args) -> bool {
			std::vector<size_t> indices(context.entity_component_indices.size());
			std::iota(indices.begin(), indices.end(), 0);
			bool valid = true;
			std::for_each(std::execution::par_unseq, indices.begin(), indices.end(), [&](size_t e) {
				valid &= func(context, e, std::forward<Targs>(args)...);
			});
			return valid;
		};
	}

	template<typename... Tsystems>
	auto parallel(Tsystems... systems) {
		return [systems = std::move(std::make_tuple(systems...))]
			(context& context, auto... args) -> bool
		{
			std::array<size_t, sizeof...(Tsystems)> indices{};
			std::iota(indices.begin(), indices.end(), 0);
			bool valid = true;

			std::for_each(std::execution::par_unseq, indices.begin(), indices.end(), [&](size_t i) {
				std::apply([&](auto&... sys) {
					size_t index = 0;
					valid &= ((index++ == i ? sys(context, args...) : true) && ...);
				}, systems);
			});

			return valid;
		};
	}

	template<typename... Targs>
	auto parallel(const std::vector<std::function<bool(context&, entity_t, Targs...)>>& systems) {
		return [=](context& context, auto... args) -> bool {
			std::atomic<uint8_t> valid = 1;
			std::for_each(std::execution::par_unseq, systems.begin(), systems.end(), [&](const auto& system){
				valid.fetch_and(system(context, args...));
			});
			return valid.load();
		};
	}
#endif
}
