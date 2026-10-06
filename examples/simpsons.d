/// The classic Datalog family example over the Simpsons: parenthood as a relation component, grandparents and ancestors derived by rules, founders by negation, and marriage as a symmetric relation.
module examples.simpsons;

import core.stdc.stdio : printf;
static import ecrs.context;
static import ecrs.datalog;
static import ecrs.registry;
static import ecrs.relation;
static import fp.dynarray;

struct Name { const(char)* text; }
struct Person {}
alias Parents = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);
alias Spouse = ecrs.relation.Relation!1;

enum : size_t { abraham, mona, clancy, jackie, homer, marge, patty, selma, bart, lisa, maggie, ling, familySize }

immutable const(char)*[familySize] names = ["Abraham", "Mona", "Clancy", "Jackie", "Homer", "Marge", "Patty", "Selma", "Bart", "Lisa", "Maggie", "Ling"];

// Prints `label`, then the name each solution of `body` binds variable `var` to.
bool list(const(char)* label, ref ecrs.datalog.Program p, ref ecrs.context.Context ctx, size_t var, const(ecrs.datalog.Atom)[] body...) {
	const(ecrs.context.Context)* view = &ctx; // a const read is not a change, so the next query need not re-evaluate
	cast(void) printf("%s:", label);
	immutable status = ecrs.datalog.query(p, ctx, body, (b) {
		cast(void) printf(" %s", ecrs.context.getComponent!Name(*view, b[var]).text);
		return true;
	});
	cast(void) printf("\n");
	return status == ecrs.datalog.Status.ok;
}

extern(C) int main() {
	scope(exit) ecrs.registry.free();
	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	ecrs.registry.EntityId[familySize] family;
	foreach (i, ref e; family) {
		e = ecrs.context.addEntity(ctx);
		if (e == ecrs.registry.invalidEntity || ecrs.context.addComponent!Person(ctx, e) is null) return 1;
		auto name = ecrs.context.addComponent!Name(ctx, e);
		if (name is null) return 1;
		name.text = names[i];
	}

	// Each step can fail only by running out of memory, which a real program would handle more gracefully.
	bool parents(size_t child, size_t[] of...) {
		auto component = ecrs.context.getOrAddComponent!Parents(ctx, family[child]);
		if (component is null) return false;
		foreach (parent; of)
			if (!fp.dynarray.pushBack(component.related, family[parent])) return false;
		return true;
	}
	bool marry(size_t a, size_t b) {
		auto component = ecrs.context.addComponent!Spouse(ctx, family[a]);
		if (component is null) return false;
		component.related[0] = family[b];
		return true;
	}
	if (!parents(homer, abraham, mona) || !parents(marge, clancy, jackie) || !parents(patty, clancy, jackie) || !parents(selma, clancy, jackie)
		|| !parents(bart, homer, marge) || !parents(lisa, homer, marge) || !parents(maggie, homer, marge) || !parents(ling, selma))
		return 1;
	if (!marry(abraham, mona) || !marry(clancy, jackie) || !marry(homer, marge)) return 1;

	// Each marriage is stored once; the trait makes queries read it both ways.
	immutable spouse = ecrs.registry.componentId!Spouse();
	ecrs.registry.setRelationTraits(spouse, ecrs.registry.RelationTrait.symmetric);

	ecrs.datalog.Program p;
	scope(exit) ecrs.datalog.free(p);
	immutable parent = ecrs.registry.componentId!Parents();
	immutable person = ecrs.registry.componentId!Person();
	immutable grandparent = ecrs.datalog.derive(p, "simpsons.grandparent", 1);
	immutable ancestor = ecrs.datalog.derive(p, "simpsons.ancestor", 1);
	immutable hasParent = ecrs.datalog.derive(p, "simpsons.hasParent", 0);
	immutable founder = ecrs.datalog.derive(p, "simpsons.founder", 0);
	immutable parentInLaw = ecrs.datalog.derive(p, "simpsons.parentInLaw", 1);

	mixin(ecrs.datalog.createVariables!("x", "y", "z"));
	ecrs.datalog.Status[6] added = [
		// grandparent(x, z) :- parent(x, y), parent(y, z).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(grandparent, x, z), ecrs.datalog.atom(parent, x, y), ecrs.datalog.atom(parent, y, z)),
		// ancestor(x, y) :- parent(x, y).   ancestor(x, z) :- parent(x, y), ancestor(y, z).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(ancestor, x, y), ecrs.datalog.atom(parent, x, y)),
		ecrs.datalog.addRule(p, ecrs.datalog.atom(ancestor, x, z), ecrs.datalog.atom(parent, x, y), ecrs.datalog.atom(ancestor, y, z)),
		// founder(x) :- person(x), not hasParent(x).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(hasParent, x), ecrs.datalog.atom(parent, x, y)),
		ecrs.datalog.addRule(p, ecrs.datalog.atom(founder, x), ecrs.datalog.atom(person, x), ecrs.datalog.negate(ecrs.datalog.atom(hasParent, x))),
		// parentInLaw(x, z) :- spouse(x, y), parent(y, z).
		ecrs.datalog.addRule(p, ecrs.datalog.atom(parentInLaw, x, z), ecrs.datalog.atom(spouse, x, y), ecrs.datalog.atom(parent, y, z)),
	];
	foreach (status; added)
		if (status != ecrs.datalog.Status.ok) return 1;

	if (!list("Bart's grandparents", p, ctx, 1, ecrs.datalog.atom(grandparent, ecrs.datalog.constant(family[bart]), y))
		|| !list("Lisa's ancestors", p, ctx, 1, ecrs.datalog.atom(ancestor, ecrs.datalog.constant(family[lisa]), y))
		|| !list("Jackie's descendants", p, ctx, 0, ecrs.datalog.atom(ancestor, x, ecrs.datalog.constant(family[jackie])))
		|| !list("Founders", p, ctx, 0, ecrs.datalog.atom(founder, x))
		|| !list("Marge's spouse", p, ctx, 1, ecrs.datalog.atom(spouse, ecrs.datalog.constant(family[marge]), y))
		|| !list("Marge's parents-in-law", p, ctx, 1, ecrs.datalog.atom(parentInLaw, ecrs.datalog.constant(family[marge]), y))
		|| !list("Homer's parents-in-law", p, ctx, 1, ecrs.datalog.atom(parentInLaw, ecrs.datalog.constant(family[homer]), y)))
		return 1;
	return 0;
}
