/// Differential stress test for `ecrs.datalog`: random graphs and every rule shape the engine treats differently, each answer checked against a brute-force reference over adjacency matrices. Each case then mutates the base relation and renumbers the store, and must still agree.
module datalog_hammer;

import core.stdc.stdio : fprintf, stderr;
import core.stdc.string : memcpy, memset;

static import bc.threadpool;
static import ecrs.context;
static import ecrs.datalog;
static import ecrs.registry;
static import ecrs.relation;
static import fp.dynarray;
static import fp.pointer;

@nogc nothrow:


private struct Rng {
	ulong state;
	uint next() @nogc nothrow {
		state ^= state << 13;
		state ^= state >> 7;
		state ^= state << 17;
		return cast(uint)(state >> 16);
	}
	uint below(size_t n) @nogc nothrow { return cast(uint)(next() % n); }
}

// An n x n boolean matrix.
private struct Matrix {
	size_t n;
	bool* cells;
	ref bool opIndex(size_t i, size_t j) @trusted @nogc nothrow { return cells[i * n + j]; }
}

private Matrix matrix(size_t n) @trusted {
	auto m = Matrix(n, cast(bool*) fp.pointer.allocFunction(null, n * n + 1));
	assert(m.cells !is null);
	memset(m.cells, 0, n * n + 1);
	return m;
}

private void release(ref Matrix m) @trusted { cast(void) fp.pointer.allocFunction(m.cells, 0); m.cells = null; }
private bool equal(ref Matrix a, ref Matrix b) @trusted { return a.cells[0 .. a.n * a.n] == b.cells[0 .. b.n * b.n]; }

// Every pair joined by a path of one or more edges.
private Matrix transitive(ref Matrix adj) {
	auto r = matrix(adj.n);
	foreach (i; 0 .. adj.n) foreach (j; 0 .. adj.n) r[i, j] = adj[i, j];
	foreach (k; 0 .. adj.n) foreach (i; 0 .. adj.n) if (r[i, k]) foreach (j; 0 .. adj.n) if (r[k, j]) r[i, j] = true;
	return r;
}

// The reading of `adj` under `traits`, per `ecrs.registry.RelationTrait`'s definitions.
private Matrix withTraits(ref Matrix adj, uint traits) {
	immutable n = adj.n;
	auto base = matrix(n);
	scope(exit) release(base);
	foreach (i; 0 .. n) foreach (j; 0 .. n)
		base[i, j] = adj[i, j] || ((traits & ecrs.registry.RelationTrait.symmetric) && adj[j, i]);
	auto r = (traits & ecrs.registry.RelationTrait.transitive) ? transitive(base) : matrix(n);
	if (!(traits & ecrs.registry.RelationTrait.transitive)) foreach (i; 0 .. n) foreach (j; 0 .. n) r[i, j] = base[i, j];
	if (traits & ecrs.registry.RelationTrait.reflexive)
		foreach (i; 0 .. n) {
			bool inField = false;
			foreach (j; 0 .. n) inField |= adj[i, j] || adj[j, i];
			if (inField) r[i, i] = true;
		}
	return r;
}

// sg(x, y) :- e(p, x), e(p, y).   sg(x, y) :- e(a, x), sg(a, b), e(b, y).
private Matrix sameGeneration(ref Matrix adj) {
	immutable n = adj.n;
	auto sg = matrix(n);
	foreach (p; 0 .. n) foreach (x; 0 .. n) if (adj[p, x]) foreach (y; 0 .. n) if (adj[p, y]) sg[x, y] = true;
	for (bool changed = true; changed;) {
		changed = false;
		foreach (a; 0 .. n) foreach (b; 0 .. n) if (sg[a, b])
			foreach (x; 0 .. n) if (adj[a, x]) foreach (y; 0 .. n) if (adj[b, y] && !sg[x, y])
				sg[x, y] = changed = true;
	}
	return sg;
}

// Pairs joined by a path of odd, or with `even`, even nonzero, length.
private Matrix parity(ref Matrix adj, bool even) {
	immutable n = adj.n;
	auto odd = matrix(n), ev = matrix(n);
	foreach (i; 0 .. n) foreach (j; 0 .. n) odd[i, j] = adj[i, j];
	for (bool changed = true; changed;) {
		changed = false;
		foreach (x; 0 .. n) foreach (z; 0 .. n) foreach (y; 0 .. n) {
			if (!adj[z, y]) continue;
			if (odd[x, z] && !ev[x, y]) ev[x, y] = changed = true;
			if (ev[x, z] && !odd[x, y]) odd[x, y] = changed = true;
		}
	}
	if (even) { release(odd); return ev; }
	release(ev);
	return odd;
}


private alias Edge = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);
private enum edgeUnique = 101, traitUnique = 102;
private struct Node {}

// One random graph held twice in the store: under `Edge`, which rules read plainly, and under the trait-bearing copy.
private struct Case {
	ecrs.context.Context ctx;
	size_t n;
	ecrs.registry.EntityId[64] nodes;
	Matrix adj;
	size_t* indexOf; // entity id -> node index, or size_t.max
}

private void setEdge(ref Case c, size_t i, size_t j, bool present) @trusted {
	size_t[2] ids = [ecrs.registry.componentId!(Edge, edgeUnique)(), ecrs.registry.componentId!(Edge, traitUnique)()];
	foreach (id; ids) {
		auto list = &(cast(Edge*) ecrs.context.getOrAddComponent(c.ctx, c.nodes[i], id)).related;
		if (present) assert(fp.dynarray.pushBack(*list, c.nodes[j]));
		else
			for (size_t k = fp.dynarray.length(*list); k-- > 0;)
				if ((*list)[k] == c.nodes[j]) cast(void) fp.dynarray.removeAt(*list, k);
	}
	c.adj[i, j] = present;
}

private void rebuildIndex(ref Case c) @trusted {
	immutable slots = fp.dynarray.length(c.ctx.indexTable);
	c.indexOf = cast(size_t*) fp.pointer.allocFunction(c.indexOf, slots * size_t.sizeof);
	assert(c.indexOf !is null);
	foreach (k; 0 .. slots) c.indexOf[k] = size_t.max;
	foreach (i; 0 .. c.n) c.indexOf[c.nodes[i]] = i;
}

private Case makeCase(ref Rng rng) @trusted {
	Case c;
	c.ctx = ecrs.context.create();
	c.n = 2 + rng.below(38);
	c.adj = matrix(c.n);
	// Spare entities around the nodes, so ids and node indices differ.
	foreach (i; 0 .. c.n) {
		if (rng.below(4) == 0) assert(ecrs.context.addEntity(c.ctx) != ecrs.registry.invalidEntity);
		c.nodes[i] = ecrs.context.addEntity(c.ctx);
		assert(ecrs.context.addComponent!Node(c.ctx, c.nodes[i]) !is null);
	}
	immutable edges = rng.below(3 * c.n + 1);
	foreach (k; 0 .. edges) {
		immutable i = rng.below(c.n), j = rng.below(c.n);
		setEdge(c, i, j, true); // duplicates and self-loops included
	}
	// Empty slots are not facts.
	assert(fp.dynarray.pushBack(ecrs.context.getOrAddComponent!(Edge, edgeUnique)(c.ctx, c.nodes[0]).related, ecrs.registry.invalidEntity));
	rebuildIndex(c);
	return c;
}

private void release(ref Case c) @trusted {
	release(c.adj);
	cast(void) fp.pointer.allocFunction(c.indexOf, 0);
	ecrs.context.free(c.ctx);
}

// The answers to `relation(x, y)` as a matrix.
private Matrix answers(ref ecrs.datalog.Program p, ref Case c, size_t relation, bc.threadpool.ThreadPool* pool, ecrs.registry.EntityId x = ecrs.registry.invalidEntity, ecrs.registry.EntityId y = ecrs.registry.invalidEntity) @trusted {
	auto m = matrix(c.n);
	ecrs.datalog.Atom[1] q = [ecrs.datalog.atom(relation, x == ecrs.registry.invalidEntity ? ecrs.datalog.variable(0) : ecrs.datalog.constant(x), y == ecrs.registry.invalidEntity ? ecrs.datalog.variable(1) : ecrs.datalog.constant(y))];
	immutable status = ecrs.datalog.query(p, c.ctx, q[], (b) {
		immutable from = x == ecrs.registry.invalidEntity ? b[0] : x, to = y == ecrs.registry.invalidEntity ? b[1] : y;
		assert(c.indexOf[from] != size_t.max && c.indexOf[to] != size_t.max, "answer outside the graph");
		m[c.indexOf[from], c.indexOf[to]] = true;
		return true;
	}, pool);
	assert(status == ecrs.datalog.Status.ok);
	return m;
}

// `expected` restricted to row `x`, column `y`, or both, as node indices.
private Matrix restrict(ref Matrix expected, size_t x, size_t y) {
	auto m = matrix(expected.n);
	foreach (i; 0 .. m.n) foreach (j; 0 .. m.n)
		m[i, j] = expected[i, j] && (x == size_t.max || i == x) && (y == size_t.max || j == y);
	return m;
}

private struct Relations {
	size_t edge, edgeT, node;
	size_t left, right, doubly, sg, odd, even, unreached, viaTrait;
}

private Relations declare(ref ecrs.datalog.Program p, size_t root) {
	Relations r;
	r.edge = ecrs.registry.componentId!(Edge, edgeUnique)();
	r.edgeT = ecrs.registry.componentId!(Edge, traitUnique)();
	r.node = ecrs.registry.componentId!Node();
	r.left = ecrs.datalog.derive(p, "hammer.left", 1);
	r.right = ecrs.datalog.derive(p, "hammer.right", 1);
	r.doubly = ecrs.datalog.derive(p, "hammer.doubly", 1);
	r.sg = ecrs.datalog.derive(p, "hammer.sg", 1);
	r.odd = ecrs.datalog.derive(p, "hammer.odd", 1);
	r.even = ecrs.datalog.derive(p, "hammer.even", 1);
	r.unreached = ecrs.datalog.derive(p, "hammer.unreached", 0);
	r.viaTrait = ecrs.datalog.derive(p, "hammer.viaTrait", 1);

	mixin(ecrs.datalog.createVariables!("x", "y", "z", "a", "b"));
	ecrs.datalog.Status[16] s;
	size_t k = 0;
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.left, x, y), ecrs.datalog.atom(r.edge, x, y));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.left, x, z), ecrs.datalog.atom(r.left, x, y), ecrs.datalog.atom(r.edge, y, z));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.right, x, y), ecrs.datalog.atom(r.edge, x, y));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.right, x, z), ecrs.datalog.atom(r.edge, x, y), ecrs.datalog.atom(r.right, y, z));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.doubly, x, y), ecrs.datalog.atom(r.edge, x, y));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.doubly, x, z), ecrs.datalog.atom(r.doubly, x, y), ecrs.datalog.atom(r.doubly, y, z));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.sg, x, y), ecrs.datalog.atom(r.edge, z, x), ecrs.datalog.atom(r.edge, z, y));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.sg, x, y), ecrs.datalog.atom(r.edge, a, x), ecrs.datalog.atom(r.sg, a, b), ecrs.datalog.atom(r.edge, b, y));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.odd, x, y), ecrs.datalog.atom(r.edge, x, y));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.even, x, y), ecrs.datalog.atom(r.odd, x, z), ecrs.datalog.atom(r.edge, z, y));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.odd, x, y), ecrs.datalog.atom(r.even, x, z), ecrs.datalog.atom(r.edge, z, y));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.unreached, x), ecrs.datalog.atom(r.node, x), ecrs.datalog.negate(ecrs.datalog.atom(r.left, ecrs.datalog.constant(cast(ecrs.registry.EntityId) root), x)));
	s[k++] = ecrs.datalog.addRule(p, ecrs.datalog.atom(r.viaTrait, x, y), ecrs.datalog.atom(r.edgeT, x, y));
	foreach (status; s[0 .. k]) assert(status == ecrs.datalog.Status.ok);
	return r;
}

// Checks every derived relation, and the trait relation from each binding pattern, against the references.
private void check(ref ecrs.datalog.Program p, ref Case c, ref Relations r, uint traits, bc.threadpool.ThreadPool* pool, ref Rng rng, ulong seed) @trusted {
	void expect(Matrix got, Matrix want, const(char)* what) {
		scope(exit) { release(got); release(want); }
		if (!equal(got, want)) {
			fprintf(stderr, "hammer: seed %llu, n %zu, traits %u: %s disagrees\n", seed, c.n, traits, what);
			assert(false);
		}
	}

	auto closure = transitive(c.adj);
	scope(exit) release(closure);
	Matrix copy() { auto m = matrix(c.n); memcpy(m.cells, closure.cells, c.n * c.n); return m; }

	// Unbound, then each binding pattern: a bound target reads the derived relation's own index, which evaluation extended round by round.
	void expectAll(size_t relation, Matrix want, const(char)* what) {
		scope(exit) release(want);
		immutable i = rng.below(c.n), j = rng.below(c.n);
		expect(answers(p, c, relation, pool), restrict(want, size_t.max, size_t.max), what);
		expect(answers(p, c, relation, pool, c.nodes[i]), restrict(want, i, size_t.max), what);
		expect(answers(p, c, relation, pool, ecrs.registry.invalidEntity, c.nodes[j]), restrict(want, size_t.max, j), what);
		expect(answers(p, c, relation, pool, c.nodes[i], c.nodes[j]), restrict(want, i, j), what);
	}
	expectAll(r.left, copy(), "left-linear closure");
	expectAll(r.right, copy(), "right-linear closure");
	expectAll(r.doubly, copy(), "doubly recursive closure");
	expectAll(r.sg, sameGeneration(c.adj), "same generation");
	expectAll(r.odd, parity(c.adj, false), "odd paths");
	expectAll(r.even, parity(c.adj, true), "even paths");

	auto unreached = matrix(c.n);
	ecrs.datalog.Atom[1] q = [ecrs.datalog.atom(r.unreached, ecrs.datalog.variable(0))];
	assert(ecrs.datalog.query(p, c.ctx, q[], (b) { unreached[c.indexOf[b[0]], 0] = true; return true; }, pool) == ecrs.datalog.Status.ok);
	auto wantUnreached = matrix(c.n);
	foreach (i; 0 .. c.n) wantUnreached[i, 0] = !closure[0, i];
	expect(unreached, wantUnreached, "negation");

	auto traited = withTraits(c.adj, traits);
	scope(exit) release(traited);
	expect(answers(p, c, r.viaTrait, pool), restrict(traited, size_t.max, size_t.max), "trait closure (derived copy)");
	expect(answers(p, c, r.edgeT, pool), restrict(traited, size_t.max, size_t.max), "trait closure (unbound)");
	immutable i = rng.below(c.n), j = rng.below(c.n);
	expect(answers(p, c, r.edgeT, pool, c.nodes[i]), restrict(traited, i, size_t.max), "trait closure (owner bound)");
	expect(answers(p, c, r.edgeT, pool, ecrs.registry.invalidEntity, c.nodes[j]), restrict(traited, size_t.max, j), "trait closure (target bound)");
	expect(answers(p, c, r.edgeT, pool, c.nodes[i], c.nodes[j]), restrict(traited, i, j), "trait closure (both bound)");
}

// Renumbers every entity but 0 by a random permutation.
private void shuffle(ref Case c, ref Rng rng) @trusted {
	immutable slots = fp.dynarray.length(c.ctx.indexTable);
	auto order = cast(size_t*) fp.pointer.allocFunction(null, slots * size_t.sizeof);
	assert(order !is null);
	scope(exit) cast(void) fp.pointer.allocFunction(order, 0);
	foreach (k; 0 .. slots) order[k] = k;
	foreach_reverse (k; 2 .. slots) {
		immutable other = 1 + rng.below(k);
		immutable t = order[k]; order[k] = order[other]; order[other] = t;
	}
	assert(ecrs.context.reorderEntities(c.ctx, order[0 .. slots]));
	// order[new] = old, so each node's new id is the k with order[k] == it.
	foreach (i; 0 .. c.n)
		foreach (k; 0 .. slots)
			if (order[k] == c.nodes[i]) { c.nodes[i] = cast(ecrs.registry.EntityId) k; break; }
	rebuildIndex(c);
}

unittest {
	enum cases = 300;
	auto three = bc.threadpool.create(3);
	scope(exit) bc.threadpool.free(three);
	auto one = bc.threadpool.create(1);
	scope(exit) bc.threadpool.free(one);
	bc.threadpool.ThreadPool*[3] pools = [null, one, three];
	scope(exit) ecrs.registry.setRelationTraits(ecrs.registry.componentId!(Edge, traitUnique)(), 0);

	foreach (seed; 1 .. cases + 1) {
		auto rng = Rng(seed * 0x9E3779B97F4A7C15UL);
		auto c = makeCase(rng);
		scope(exit) release(c);
		ecrs.datalog.Program p;
		scope(exit) ecrs.datalog.free(p);
		assert(ecrs.datalog.attach(c.ctx, p)); // the negation rule names node 0 as a constant
		scope(exit) assert(ecrs.datalog.detach(c.ctx, p));
		auto r = declare(p, c.nodes[0]);

		immutable traits = rng.below(8);
		ecrs.registry.setRelationTraits(r.edgeT, traits);
		auto pool = pools[seed % 3];
		check(p, c, r, traits, pool, rng, seed);

		// Mutate: drop and add a few edges, then compare again.
		foreach (k; 0 .. 1 + rng.below(4)) {
			immutable i = rng.below(c.n), j = rng.below(c.n);
			setEdge(c, i, j, !c.adj[i, j]);
		}
		check(p, c, r, traits, pools[(seed + 1) % 3], rng, seed);

		// Renumber: rule constants, derived facts and indexes must follow.
		shuffle(c, rng);
		check(p, c, r, traits, pools[(seed + 2) % 3], rng, seed);
	}
}
