#pragma once
#include "entity.hpp"

#include <functional>
#include <generator>
#include <list>
#include <unordered_set>
#include <variant>

// Based on: https://github.com/jasonhemann/microKanren-DLS-16

namespace ecrs::kanren {

	namespace detail {
		// Primary template
		template<typename T>
		struct function_traits;

		// Specialization for function pointer
		template<typename R, typename... Args>
		struct function_traits<R(*)(Args...)> {
			using result_type = R;
			using argument_types = std::tuple<Args...>;
			static constexpr std::size_t arity = sizeof...(Args);
		};

		// Specialization for std::function
		template<typename R, typename... Args>
		struct function_traits<std::function<R(Args...)>> {
			using result_type = R;
			using argument_types = std::tuple<Args...>;
			static constexpr std::size_t arity = sizeof...(Args);
		};

		// Specialization for member function pointers (const and non-const)
		template<typename C, typename R, typename... Args>
		struct function_traits<R(C::*)(Args...) const> {
			using result_type = R;
			using argument_types = std::tuple<Args...>;
			static constexpr std::size_t arity = sizeof...(Args);
		};

		template<typename C, typename R, typename... Args>
		struct function_traits<R(C::*)(Args...)> {
			using result_type = R;
			using argument_types = std::tuple<Args...>;
			static constexpr std::size_t arity = sizeof...(Args);
		};

		// Fallback: deduce from operator()
		template<typename F>
		struct function_traits : function_traits<decltype(&F::operator())> {};
	}

	struct Variable {
		size_t id;
		bool operator==(const Variable& other) const { return id == other.id; }
		std::strong_ordering operator<=>(const Variable& other) const { return id <=> other.id; }
		explicit operator size_t() { return id; }

		static Variable next(struct State&);
		void become_next_variable(struct State& s) { *this = next(s); }
	};

	struct Term: public std::variant<Variable, ecrs::Entity, std::list<Term>> {};
	size_t term2size_t(const Term& t) {
		switch (t.index()) {
		case 0: // Variable
			return std::get<Variable>(t).id;
		case 1: // ecrs::Entity
			return std::get<ecrs::Entity>(t);
		case 2: { // std::list<Term>
			size_t out = 0;
			for(const auto& term: std::get<std::list<Term>>(t))
				out ^= term2size_t(term);
			return out;
		}
		default: return -1;
		}
	}
	bool term_equivalence(const Term& a, const Term& b) {
		if(a.index() != b.index()) return false;
		switch (a.index()) {
		case 0: // Variable
			return std::get<Variable>(a).id == std::get<Variable>(b).id;
		case 1: // ecrs::Entity
			return std::get<ecrs::Entity>(a) == std::get<ecrs::Entity>(b);
		case 2: { // std::list<Term>
			auto& la = std::get<std::list<Term>>(a);
			auto& lb = std::get<std::list<Term>>(b);
			if(la.size() != lb.size()) return false;
			auto u = la.begin();
			auto v = lb.begin();
			auto end = la.end();
			for(; u != end; ++u, ++v)
				if(!term_equivalence(*u, *v))
					return false;
			return true;
		}
		default: return false;
		}
	}

	using Substitution = std::pair<Term, Term>;
	using Substitutions = std::list<Substitution>;
	struct State {
		ecrs::TrivialModule* module;
		Substitutions sub;
		size_t counter = 0;

		Variable next_variable() { return Variable::next(*this); }
	};
	using OwnedGoal = std::function<std::generator<State>(State)>;
	template<typename T>
	concept Goal = std::convertible_to<T, OwnedGoal> || std::is_same_v<T, OwnedGoal>;

	Variable Variable::next(State& state) {
		return {state.counter++};
	}

	inline namespace micro {
		std::optional<Term> assoc(const Term& key, const Substitutions& s) {
			for (const auto& [k, v] : s)
				if (term_equivalence(k, key))
					return v;
			return std::nullopt;
		}

		Term find(const Term& u, const Substitutions& s) {
			if (std::holds_alternative<Variable>(u))
				if (auto res = assoc(u, s); res)
					return find(*res, s);
			return u;
		}

		bool occurs(const Term& x, const Term& u, const Substitutions& s) {
			Term u_ = find(u, s);
			if (std::holds_alternative<Variable>(u_)) return term_equivalence(x, u_);
			if (std::holds_alternative<std::list<Term>>(u_)) {
				auto& l = std::get<std::list<Term>>(u_);
				if(l.empty()) return false; // Unify empty lists
				for(const auto& t:l)
					if(occurs(x, t, s)) return true;
			}
			return false;
		}

		std::optional<Substitutions> extend_substitutions(const Term& x, const Term& v, const Substitutions& s) {
			if (occurs(x, v, s)) return std::nullopt;
			auto new_s = s;
			new_s.emplace_back(x, v);
			return new_s;
		}

		std::optional<Substitutions> unify(const Term& u, const Term& v, Substitutions s) {
			Term u_ = find(u, s);
			Term v_ = find(v, s);
			if (term_equivalence(u_, v_)) return s;
			if (std::holds_alternative<Variable>(u_)) return extend_substitutions(u_, v_, s);
			if (std::holds_alternative<Variable>(v_)) return unify(v_, u_, s);
			if (std::holds_alternative<std::list<Term>>(u_) && std::holds_alternative<std::list<Term>>(v_)) {
				auto lu = std::get<std::list<Term>>(u_);
				auto lv = std::get<std::list<Term>>(v_);
				if(lu.size() != lv.size()) return std::nullopt;
				auto u = lu.begin();
				auto v = lv.begin();
				auto end = lu.end();
				for(--end; u != end; ++u, ++v)
					if(auto sNew = unify(*u, *v, s); !sNew)
						return std::nullopt;
					else s = *sNew;
				// ++u, ++v; // TODO: Needed?
				return unify(*u, *v, s);
			}
			// if(std::holds_alternative<ecrs::Entity>(u_) && std::holds_alternative<ecrs::Entity>(v_))
			// 	if(std::get<ecrs::Entity>(u_) == std::get<ecrs::Entity>(v_)) return s;
			return std::nullopt;
		}

		std::generator<State> unit(State s) {
			co_yield s;
		}

		std::generator<State> null(State s) {
			co_return;
		}

		Goal auto eq(const Term& u, const Term& v) {
			return [=](State sc) -> std::generator<State> {
				auto [m, s, c] = sc;
				if (auto s_ = unify(u, v, s); s_)
					co_yield {m, *s_, c};
			};
		}
		inline Goal auto operator==(const Term& u, const Term& v) { return eq(u, v); }

		template<Goal G>
		Goal auto next_variable(std::convertible_to<std::function<G(Variable)>> auto f) {
			return [f](State state) -> std::generator<State> {
				Variable next{state.counter++};
				auto f_next = f(next);
				for(auto s: f_next(state))
					co_yield s;
			};
		}
		template<Goal G>
		inline Goal auto fresh(std::convertible_to<std::function<G(Variable)>> auto f) { return next_variable(f); }

		template<typename F, size_t arity = detail::function_traits<F>::arity>
		Goal auto next_variables(const F& f) {
			return [f](State state) -> std::generator<State> {
				Variable next{state.counter++};
				if constexpr(arity > 1) {
					auto b = [f, next](auto... args){
						return f(next, args...);
					};
					auto f_next = next_variables<decltype(b), arity - 1>(b);
					for(auto s: f_next(state))
						co_yield s;
				} else {
					auto f_next = f(next);
					for(auto s: f_next(state)) co_yield s;
				}
			};
		}

		std::generator<State> append(std::generator<State> g1, std::generator<State> g2) {
			auto it1 = g1.begin();
			auto it2 = g2.begin();

			while (it1 != g1.end() || it2 != g2.end()) {
				if (it1 != g1.end()) {
					co_yield *it1;
					++it1;
				}
				if (it2 != g2.end()) {
					co_yield *it2;
					++it2;
				}
			}
		}

		Goal auto disjunction(Goal auto g1, Goal auto g2) {
			return [=](State state) {
				return append(g1(state), g2(state));
			};
		}
		inline Goal auto operator|(Goal auto g1, Goal auto g2) { return disjunction(g1, g2); }

		template <Goal... Goals>
		Goal auto disjunction(Goal auto g1, Goal auto g2, Goals... rest) {
			return disjunction(g1, disjunction(g2, rest...));
		}

		std::generator<State> append_map(std::generator<State> g, Goal auto goal) {
			for (auto s1 : g)
				for(auto s2: goal(s1))
					co_yield s2;
		}

		Goal auto conjunction(Goal auto g1, Goal auto g2) {
			return [=](State state) {
				return append_map(g1(state), g2);
			};
		}
		inline Goal auto operator&(Goal auto g1, Goal auto g2) { return conjunction(g1, g2); }

		template <Goal... Goals>
		Goal auto conjunction(Goal auto g1, Goal auto g2, Goals... rest) {
			return conjunction(g1, conjunction(g2, rest...));
		}
	} // kanren::micro

	inline namespace mini {
		Goal auto split_head(const Term& list, const Term& out) {
			return [=](State state) -> std::generator<State> {
				auto& [m, subs, c] = state;
				auto out_ = find(out, subs);
				auto list_ = find(list, subs);

				switch(list_.index()) {
				break; case 0: // Variable
					if(auto s = unify({std::list<Term>{out_}}, list_, subs); s)
						co_yield {m, *s, c};
				break; case 1: // ecrs::Entity
					if(auto s = unify(out, list_, subs); s)
						co_yield {m, *s, c};
				break; case 2: // std::list<Term>
					if(auto& l = std::get<std::list<Term>>(list_); l.size() > 0)
						if(auto s = unify(out_, l.front(), subs); s)
							co_yield {m, *s, c};
				}
			};
		}

		Goal auto split_tail(const Term& list, const Term& out) {
			return [=](State state) -> std::generator<State> {
				auto& [m, subs, c] = state;
				auto out_ = find(out, subs);
				auto list_ = find(list, subs);

				switch(list_.index()) {
				break; case 0: // Variable
					if(auto s = unify(out_, list_, subs); s)
						co_yield {m, *s, c};
				break; case 1: // ecrs::Entity
					if(auto s = unify(out_, {std::list<Term>{list_}}, subs); s)
						co_yield {m, *s, c};
				break; case 2: // std::list<Term>
					if(auto& l = std::get<std::list<Term>>(list_); l.size() <= 1) {
						if(auto s = unify(out_, {std::list<Term>{}}, subs); s)
							co_yield {m, *s, c};
					} else if(l.size() == 2 && !std::holds_alternative<std::list<Term>>(out)) {
						if(auto s = unify(out_, {l.back()}, subs); s)
							co_yield {m, *s, c};
					} else {
						auto copy = l;
						copy.pop_front();
						if(auto s = unify(out_, {copy}, subs); s)
							co_yield {m, *s, c};
					}
				}
			};
		}

		Goal auto wrap_list(const Term& var, const Term& list) {
			return [=](State state) -> std::generator<State> {
				auto& [m, subs, c] = state;
				auto var_ = find(var, subs);
				auto list_ = find(list, subs);

				switch(var_.index()) {
				case 0: [[fallthrough]]; // Variable
				case 1: // ecrs::Entity
					if(auto s = unify(list_, {std::list<Term>{var_}}, subs); s)
						co_yield {m, *s, c};
				break; case 2: // std::list<Term>
					if(auto s = unify(list_, var_, subs); s)
						co_yield {m, *s, c};
				}
			};
		}

		Goal auto split_tail_ensure_list(const Term& list, const Term& out) {
			return next_variables([=](Variable tmp){
				return split_tail(list, {tmp}) & wrap_list({tmp}, out);
			});
		}

		Goal auto split_head_and_tail(const Term& list, const Term& head, const Term& tail) {
			return [=](State state) -> std::generator<State> {
				auto& [m, subs, c] = state;
				auto list_ = find(list, subs);
				auto head_ = find(head, subs);
				auto tail_ = find(tail, subs);

				if(std::holds_alternative<std::list<Term>>(tail_) && std::holds_alternative<Variable>(list_)) {
					auto l = std::get<std::list<Term>>(tail_);
					l.push_front(head_);
					if(auto s = unify({l}, list_, subs); s)
						co_yield {m, *s, c};
				} else if(std::holds_alternative<Variable>(tail_) && std::holds_alternative<Variable>(list_)) {
					if(auto sub = unify({std::list<Term>{}}, tail_, subs); sub) {
						auto split = split_head(list, head_);
						for(const auto& s: split({m, *sub, c}))
							co_yield s;
					}
				} else {
					auto head = split_head(list_, head_);
					auto tail = split_tail_ensure_list(list_, tail_);
					for(const auto& s1: head(state))
						for(const auto& s: tail(s1))
							co_yield s;
				}
			};
		}

		Goal auto append(const Term& a, const Term& b, const Term& out) {
			return [=](State state) -> std::generator<State> {
				auto& [m, subs, c] = state;
				auto a_ = find(a, subs);
				auto b_ = find(b, subs);
				auto out_ = find(out, subs);

				if(std::holds_alternative<ecrs::Entity>(a_))
					a_ = {std::list<Term>{a_}};
				if(std::holds_alternative<ecrs::Entity>(b_))
					b_ = {std::list<Term>{b_}};
				if(std::holds_alternative<ecrs::Entity>(out_))
					out_ = {std::list<Term>{out_}};

				if(std::holds_alternative<std::list<Term>>(a_) && std::holds_alternative<std::list<Term>>(b_)) {
					auto appended = std::get<std::list<Term>>(a_);
					auto& bl = std::get<std::list<Term>>(b_);
					std::copy(bl.begin(), bl.end(), std::back_inserter(appended));
					if(auto s = unify({appended}, out, subs); s)
						co_yield {m, *s, c};
				} else if(std::holds_alternative<Variable>(a_) && std::holds_alternative<Variable>(b_) && std::holds_alternative<std::list<Term>>(out_)) {
					auto& full = std::get<std::list<Term>>(out_);
					auto mid = full.begin();
					for( ; mid != full.end(); ++mid) {
						auto first = std::list(full.begin(), mid);
						auto second = std::list(mid, full.end());
						if(auto sub = unify(a, {first}, subs); sub)
							if(auto s = unify(b, {second}, *sub); s)
								co_yield {m, *s, c};
					}
					if(auto sub = unify(a, {full}, subs); sub)
						if(auto s = unify(b, {std::list<Term>{}}, *sub); s)
							co_yield {m, *s, c};
				} else if(std::holds_alternative<std::list<Term>>(a_) && std::holds_alternative<std::list<Term>>(out_)) {
					auto& al = std::get<std::list<Term>>(a_);
					auto& full = std::get<std::list<Term>>(out_);
					if(al.size() > full.size()) co_return;

					auto mid = full.begin();
					for(size_t i = 0; i < al.size(); ++i) ++mid;
					auto first = std::list(full.begin(), mid);
					auto second = std::list(mid, full.end());
					if(auto sub = unify(a, {first}, subs); sub)
						if(auto s = unify(b, {second}, *sub); s)
							co_yield {m, *s, c};
				} else if(std::holds_alternative<std::list<Term>>(b_) && std::holds_alternative<std::list<Term>>(out_)) {
					auto& bl = std::get<std::list<Term>>(b_);
					auto& full = std::get<std::list<Term>>(out_);
					if(bl.size() > full.size()) co_return;

					auto mid = full.end();
					for(size_t i = 0; i < bl.size(); ++i) --mid;
					auto first = std::list(full.begin(), mid);
					auto second = std::list(mid, full.end());
					if(auto sub = unify(a, {first}, subs); sub)
						if(auto s = unify(b, {second}, *sub); s)
							co_yield {m, *s, c};
				}
			};
		}

		Goal auto element_of(const Term& list, const Term& element) {
			return [=](State state) -> std::generator<State> {
				auto& [m, subs, c] = state;
				auto list_ = find(list, subs);
				auto element_ = find(element, subs);

				switch(list_.index()) {
				break; case 0: [[fallthrough]]; // Variable
				case 1: // ecrs::Entity
					if(auto s = unify(list_, element_, subs); s)
						co_yield {m, *s, c};
				break; case 2: { // std::list<Term>
					auto elem = std::holds_alternative<Variable>(element_) ? std::optional<Variable>{std::get<Variable>(element_)} : std::optional<Variable>{};

					for(auto& term: std::get<std::list<Term>>(list_))
						if(elem || term_equivalence(term, element_)) {
							subs.emplace_front(element_, term);
							co_yield {m, subs, c};
							subs.pop_front();
						} else if(std::holds_alternative<Variable>(term) && !std::holds_alternative<Variable>(element_)) {
							subs.emplace_front(term, element_);
							term = element_; // TODO: Is this bad?
							co_yield {m, subs, c};
							subs.pop_front();
						}
				}
				}
			};
		}

		OwnedGoal map(const Term& a, const Term& b, auto f) {
			return next_variables([=](Variable aHead, Variable aTail, Variable bHead, Variable bTail){
				return disjunction(
					conjunction(eq(a, {std::list<Term>{}}), eq(b, {std::list<Term>{}})),
					conjunction(
						split_head(a, {aHead}),
						split_tail_ensure_list(a, {aTail}),
						f(Term{aHead}, Term{bHead}),
						map({aTail}, {bTail}, f),
						append({bHead}, {bTail}, {b})
					)
				);
			});
		}

		Goal auto passthrough_if_not(Goal auto goal) {
			return [=](State state) -> std::generator<State> {
				for(auto s: goal(state))
					co_return;
				co_yield state;
			};
		}
	}

	Goal auto condition(bool condition) {
		return [=](State state) -> std::generator<State> {
			if(condition)
				co_yield state;
		};
	}

	Goal auto condition(const Goal auto& g, bool cond) {
		return g & condition(cond);
	}
}

namespace std {
	template<>
	struct hash<std::pair<ecrs::kanren::Term, ecrs::kanren::Term>> {
		size_t operator()(const std::pair<ecrs::kanren::Term, ecrs::kanren::Term>& pair) const {
			return ecrs::kanren::term2size_t(pair.first) ^ ecrs::kanren::term2size_t(pair.second);
		}
	};

	bool operator==(const std::pair<ecrs::kanren::Term, ecrs::kanren::Term>& a, const std::pair<ecrs::kanren::Term, ecrs::kanren::Term>& b) {
		return ecrs::kanren::term_equivalence(a.first, b.first) && ecrs::kanren::term_equivalence(a.second, b.second);
	}
}

namespace ecrs::kanren { inline namespace query {
	std::generator<Substitution> unique_substitutions(auto& substitutions, std::unordered_set<Substitution>& found)
		requires(std::convertible_to<decltype(*substitutions.begin()), Substitution>)
	{
		for(auto& sub: substitutions)
			if(!found.contains(sub)) {
				found.insert(sub);
				co_yield sub;
			}
	}

	std::generator<Substitution> unique_substitutions(auto& substitutions)
		requires(std::convertible_to<decltype(*substitutions.begin()), Substitution>)
	{
		std::unordered_set<Substitution> found;
		for(const auto& sub: unique_substitutions(substitutions, found))
			co_yield sub;
	}

	std::generator<Substitution> unique_substitutions(std::convertible_to<std::generator<State>> auto states) {
		std::unordered_set<Substitution> found;
		for (const auto& [module, subs, counter] : states)
			for(auto sub: unique_substitutions(subs, found))
				co_yield sub;
	}

	std::generator<Substitution> unique_substitutions(Goal auto& goal, State& state) {
		for(const auto& s: unique_substitutions(goal(state)))
			co_yield s;
	}

	std::generator<Substitution> all_substitutions(std::convertible_to<std::generator<State>> auto states) {
		for (const auto& [module, subs, counter] : states)
			for(const auto& sub: subs)
				co_yield sub;
	}

	std::generator<Substitution> all_substitutions(Goal auto& goal, State& state) {
		for(const auto& s: all_substitutions(goal(state)))
			co_yield s;
	}
}}
