/// Type inference in Datalog over a tiny expression language, whose syntax tree is entities and relation components. Rules propagate types from literals and annotations through bindings, additions and calls, then flag ill-typed expressions by negation.
///
/// The program it checks:
/// ---
/// let one = 1
/// let two = 2
/// let isZero: Int -> Bool
/// let sum = one + two
/// let test = isZero(sum)
/// let bad = isZero(test)
/// let oops = test + one
/// ---
module examples.typeinference;

import core.stdc.stdio : printf;
static import ecrs.context;
static import ecrs.datalog;
static import ecrs.registry;
static import ecrs.relation;
static import fp.dynarray;

struct Name { const(char)* text; }
struct IntLiteral {}
struct AddExpr {}

// The same component type, kept apart as distinct relations by its `unique` parameter.
alias Link = ecrs.relation.Relation!1;
enum : size_t { initUnique = 1, calleeUnique, argumentUnique, annotationUnique, paramUnique, returnsUnique }
alias Operands = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);

extern(C) int main() {
	scope(exit) ecrs.registry.free();
	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	// Each step can fail only by running out of memory, which a real program would handle more gracefully.
	bool failed = false;
	ecrs.registry.EntityId node(const(char)* name) {
		immutable e = ecrs.context.addEntity(ctx);
		auto component = e == ecrs.registry.invalidEntity ? null : ecrs.context.addComponent!Name(ctx, e);
		if (component is null) {
			failed = true;
			return ecrs.registry.invalidEntity;
		}
		component.text = name;
		return e;
	}
	void link(size_t unique)(ecrs.registry.EntityId from, ecrs.registry.EntityId to) {
		auto component = failed ? null : ecrs.context.addComponent!(Link, unique)(ctx, from);
		if (component is null) failed = true;
		else component.related[0] = to;
	}
	void tag(T)(ecrs.registry.EntityId e) {
		if (!failed && ecrs.context.addComponent!T(ctx, e) is null) failed = true;
	}
	ecrs.registry.EntityId literal(const(char)* text) {
		auto e = node(text);
		tag!IntLiteral(e);
		return e;
	}
	ecrs.registry.EntityId add(ecrs.registry.EntityId left, ecrs.registry.EntityId right) {
		auto e = node("+");
		tag!AddExpr(e);
		auto operands = failed ? null : ecrs.context.addComponent!Operands(ctx, e);
		failed |= operands is null || !fp.dynarray.pushBack(operands.related, left) || !fp.dynarray.pushBack(operands.related, right);
		return e;
	}
	ecrs.registry.EntityId call(ecrs.registry.EntityId callee, ecrs.registry.EntityId argument) {
		auto e = node("call");
		link!calleeUnique(e, callee);
		link!argumentUnique(e, argument);
		return e;
	}
	ecrs.registry.EntityId let(const(char)* name, ecrs.registry.EntityId initializer) {
		auto e = node(name);
		link!initUnique(e, initializer);
		return e;
	}

	auto intType = node("Int"), boolType = node("Bool"), predicate = node("Int -> Bool");
	link!paramUnique(predicate, intType);
	link!returnsUnique(predicate, boolType);

	auto one = let("one", literal("1"));
	auto two = let("two", literal("2"));
	auto isZero = node("isZero");
	link!annotationUnique(isZero, predicate);
	auto sum = let("sum", add(one, two));
	auto test = let("test", call(isZero, sum));
	auto bad = let("bad", call(isZero, test));
	auto oops = let("oops", add(test, one));
	if (failed) return 1;

	ecrs.datalog.Program p;
	scope(exit) ecrs.datalog.free(p);
	immutable intLiteral = ecrs.registry.componentId!IntLiteral();
	immutable addExpr = ecrs.registry.componentId!AddExpr();
	immutable operand = ecrs.registry.componentId!Operands();
	immutable initOf = ecrs.registry.componentId!(Link, initUnique)();
	immutable callee = ecrs.registry.componentId!(Link, calleeUnique)();
	immutable argument = ecrs.registry.componentId!(Link, argumentUnique)();
	immutable annotation = ecrs.registry.componentId!(Link, annotationUnique)();
	immutable param = ecrs.registry.componentId!(Link, paramUnique)();
	immutable returns = ecrs.registry.componentId!(Link, returnsUnique)();
	immutable hasType = ecrs.datalog.derive(p, "types.hasType", 1);
	immutable badOperand = ecrs.datalog.derive(p, "types.badOperand", 0);
	immutable badArgument = ecrs.datalog.derive(p, "types.badArgument", 0);

	mixin(ecrs.datalog.createVariables!("e", "t", "x", "f", "a"));
	auto i = ecrs.datalog.constant(intType);
	ecrs.datalog.Status[7] added = [
		// hasType(e, Int) :- intLiteral(e).   hasType(e, Int) :- addExpr(e).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(hasType, e, i), ecrs.datalog.atom(intLiteral, e)),
		ecrs.datalog.addRule(p, ecrs.datalog.atom(hasType, e, i), ecrs.datalog.atom(addExpr, e)),
		// hasType(e, t) :- annotation(e, t).   hasType(e, t) :- init(e, x), hasType(x, t).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(hasType, e, t), ecrs.datalog.atom(annotation, e, t)),
		ecrs.datalog.addRule(p, ecrs.datalog.atom(hasType, e, t), ecrs.datalog.atom(initOf, e, x), ecrs.datalog.atom(hasType, x, t)),
		// hasType(e, t) :- callee(e, x), hasType(x, f), returns(f, t).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(hasType, e, t), ecrs.datalog.atom(callee, e, x), ecrs.datalog.atom(hasType, x, f), ecrs.datalog.atom(returns, f, t)),
		// badOperand(e) :- operand(e, x), not hasType(x, Int).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(badOperand, e), ecrs.datalog.atom(operand, e, x), ecrs.datalog.negate(ecrs.datalog.atom(hasType, x, i))),
		// badArgument(e) :- callee(e, f), hasType(f, t), param(t, x), argument(e, a), not hasType(a, x).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(badArgument, e), ecrs.datalog.atom(callee, e, f), ecrs.datalog.atom(hasType, f, t), ecrs.datalog.atom(param, t, x),
			ecrs.datalog.atom(argument, e, a), ecrs.datalog.negate(ecrs.datalog.atom(hasType, a, x))),
	];
	foreach (status; added)
		if (status != ecrs.datalog.Status.ok) return 1;

	// Results are read through a const view: a const read is not a change, so the next query need not re-evaluate.
	const(ecrs.context.Context)* view = &ctx;
	const(char)* nameOf(ecrs.registry.EntityId entity) { return ecrs.context.getComponent!Name(*view, entity).text; }

	immutable ecrs.registry.EntityId[7] bindings = [one, two, isZero, sum, test, bad, oops];
	foreach (binding; bindings) {
		ecrs.datalog.Atom[1] typeOf = [ecrs.datalog.atom(hasType, ecrs.datalog.constant(binding), t)];
		cast(void) printf("%s:", nameOf(binding));
		if (ecrs.datalog.query(p, ctx, typeOf[], (b) { cast(void) printf(" %s", nameOf(b[1])); return true; }) != ecrs.datalog.Status.ok) return 1;
		cast(void) printf("\n");
	}

	// An error names the binding whose initializer is ill-typed.
	bool report(size_t errors, const(char)* message) {
		ecrs.datalog.Atom[2] body = [ecrs.datalog.atom(errors, x), ecrs.datalog.atom(initOf, e, x)];
		return ecrs.datalog.query(p, ctx, body[], (b) {
			cast(void) printf("error in %s: %s\n", nameOf(b[0]), message);
			return true;
		}) == ecrs.datalog.Status.ok;
	}
	if (!report(badOperand, "an operand of + is not an Int") || !report(badArgument, "an argument does not match its parameter type")) return 1;
	return 0;
}
