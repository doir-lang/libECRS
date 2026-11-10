/// The classic Datalog family example over the Simpsons: parenthood as a relation component, grandparents and ancestors derived by rules, founders by negation, and marriage as a symmetric relation.
module examples.simpsons;

static import ecrs.context;
static import ecrs.datalog;
static import ecrs.registry;
static import ecrs.relation;
static import fp.dynarray;
static import fp.io;

struct Name { const(char)* text; }
struct Person {}
alias Parents = ecrs.relation.Relation!(ecrs.relation.dynamicArity);
alias Spouse = ecrs.relation.Relation!1;

enum : size_t { abraham, mona, clancy, jackie, homer, marge, patty, selma, bart, lisa, maggie, ling, familySize }

immutable const(char)*[familySize] names = ["Abraham", "Mona", "Clancy", "Jackie", "Homer", "Marge", "Patty", "Selma", "Bart", "Lisa", "Maggie", "Ling"];

// Prints `label`, then the name each solution of `body` binds variable `var` to.
bool list(const(char)* label, ref ecrs.datalog.Program p, ref ecrs.context.Context context, size_t var, const(ecrs.datalog.Atom)[] body...) {
	const(ecrs.context.Context)* view = &context; // a const read is not a change, so the next query need not re-evaluate
	cast(void) fp.io.print(label, ':');
	immutable status = ecrs.datalog.query(p, context, body, (b) {
		cast(void) fp.io.print(' ', ecrs.context.getComponent!Name(*view, b[var]).text);
		return true;
	});
	cast(void) fp.io.print('\n');
	return status == ecrs.datalog.Status.ok;
}

extern(C) int main() {
	scope(exit) ecrs.registry.free();
	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);

	ecrs.registry.EntityId[familySize] family;
	foreach (i, ref e; family) {
		e = ecrs.context.addEntity(context);
		if (e == ecrs.registry.invalidEntity || ecrs.context.addComponent!Person(context, e) is null) return 1;
		auto name = ecrs.context.addComponent!Name(context, e);
		if (name is null) return 1;
		name.text = names[i];
	}

	// Each step can fail only by running out of memory, which a real program would handle more gracefully.
	bool parents(size_t child, size_t[] of...) {
		auto component = ecrs.context.ensureComponent!Parents(context, family[child]);
		if (component is null) return false;
		foreach (parent; of)
			if (!fp.dynarray.pushBack(component.related, family[parent])) return false;
		return true;
	}
	bool marry(size_t a, size_t b) {
		auto component = ecrs.context.addComponent!Spouse(context, family[a]);
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

	if (!list("Bart's grandparents", p, context, 1, ecrs.datalog.atom(grandparent, ecrs.relation.Term(family[bart]), y))
		|| !list("Lisa's ancestors", p, context, 1, ecrs.datalog.atom(ancestor, ecrs.relation.Term(family[lisa]), y))
		|| !list("Jackie's descendants", p, context, 0, ecrs.datalog.atom(ancestor, x, ecrs.relation.Term(family[jackie])))
		|| !list("Founders", p, context, 0, ecrs.datalog.atom(founder, x))
		|| !list("Marge's spouse", p, context, 1, ecrs.datalog.atom(spouse, ecrs.relation.Term(family[marge]), y))
		|| !list("Marge's parents-in-law", p, context, 1, ecrs.datalog.atom(parentInLaw, ecrs.relation.Term(family[marge]), y))
		|| !list("Homer's parents-in-law", p, context, 1, ecrs.datalog.atom(parentInLaw, ecrs.relation.Term(family[homer]), y)))
		return 1;
	return 0;
}
