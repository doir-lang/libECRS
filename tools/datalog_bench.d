/// Throughput of `ecrs.datalog` on classic workloads. Each prints the best of several runs, every run starting from a fresh `Program`, so paying for the full recomputation.
///
/// Build with `dub build --config=datalog-bench --build=release`, to `bin/datalog-bench`. Arguments: a size scale, then an optional substring that selects the "workload pool" lines to run.
module datalog_bench;

import core.stdc.stdio : printf;
import core.stdc.stdlib : abort, atoi;
import core.stdc.string : strstr;
import core.sys.posix.time : clock_gettime, timespec, CLOCK_MONOTONIC;

static import bc.threadpool;
static import ecrs.context;
static import ecrs.datalog;
static import ecrs.registry;
static import ecrs.relation;
static import fp.dynarray;

@nogc nothrow:


// Unlike `assert`, which a release build drops along with the call it checks.
private void require(bool ok) {
	if (ok) return;
	cast(void) printf("datalog-bench: a call failed\n");
	abort();
}

private double now() @trusted {
	timespec t;
	clock_gettime(CLOCK_MONOTONIC, &t);
	return t.tv_sec + t.tv_nsec * 1e-9;
}

private alias Edge = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);
private enum chainUnique = 201, dagUnique = 202, treeUnique = 203, traitUnique = 204;
private struct Node {}

private struct Graph {
	ecrs.context.Context ctx;
	ecrs.registry.EntityId* nodes;
	size_t edges;
}

private Graph graph(size_t n) @trusted {
	Graph g;
	g.ctx = ecrs.context.create();
	foreach (i; 0 .. n) {
		immutable e = ecrs.context.addEntity(g.ctx);
		require(e != ecrs.registry.invalidEntity && fp.dynarray.pushBack(g.nodes, e));
		require(ecrs.context.addComponent!Node(g.ctx, e) !is null);
	}
	return g;
}
private void link(size_t unique)(ref Graph g, size_t from, size_t to) @trusted {
	require(fp.dynarray.pushBack(ecrs.context.getOrAddComponent!(Edge, unique)(g.ctx, g.nodes[from]).related, g.nodes[to]));
	++g.edges;
}
private void release(ref Graph g) @trusted {
	fp.dynarray.free(g.nodes);
	ecrs.context.free(g.ctx);
}

private size_t count(ref ecrs.datalog.Program p, ref ecrs.context.Context ctx, size_t relation, size_t arity) @trusted {
	size_t n = 0;
	ecrs.datalog.Atom[1] q;
	q[0] = arity == 1 ? ecrs.datalog.atom(relation, ecrs.datalog.variable(0)) : ecrs.datalog.atom(relation, ecrs.datalog.variable(0), ecrs.datalog.variable(1));
	require(ecrs.datalog.query(p, ctx, q[], (b) { ++n; return true; }) == ecrs.datalog.Status.ok);
	return n;
}

private enum repeats = 3;
private __gshared const(char)* filter = null;

// Runs `body`, which builds a program, evaluates it and returns the fact count, `repeats` times, and prints the best time.
private void measure(const(char)* name, const(char)* pool, scope size_t delegate() @nogc nothrow body) @trusted {
	import core.stdc.stdio : snprintf;
	char[96] label;
	cast(void) snprintf(label.ptr, label.length, "%s %s", name, pool);
	if (filter !is null && strstr(label.ptr, filter) is null) return;
	double best = double.max;
	size_t facts;
	foreach (r; 0 .. repeats) {
		immutable start = now();
		facts = body();
		immutable t = now() - start;
		if (t < best) best = t;
	}
	cast(void) printf("%-34s %-8s %10zu facts %9.3f ms %8.2f Mfacts/s\n", name, pool, facts, best * 1e3, facts / best * 1e-6);
}

extern (C) int main(int argc, char** argv) @trusted {
	immutable scale = argc > 1 ? atoi(argv[1]) : 1;
	filter = argc > 2 ? argv[2] : null;
	size_t[5] poolSizes = [0, 1, 2, 4, 8];
	bc.threadpool.ThreadPool*[5] pools;
	foreach (i, w; poolSizes) {
		pools[i] = w == 0 ? null : bc.threadpool.create(w);
		require(w == 0 || pools[i] !is null);
	}
	scope(exit) foreach (p; pools) if (p !is null) bc.threadpool.free(p);
	const(char)*[5] poolNames = ["serial", "pool1", "pool2", "pool4", "pool8"];
	mixin(ecrs.datalog.createVariables!("x", "y", "z", "a", "b"));

	cast(void) printf("%-34s %-8s %16s %12s %17s\n", "workload".ptr, "pool".ptr, "derived".ptr, "best".ptr, "throughput".ptr);

	// Chain of n: the closure is n(n-1)/2 facts over n rounds of one new fact per source, the worst case for round count.
	{
		immutable n = 600 * scale;
		auto g = graph(n);
		scope(exit) release(g);
		foreach (i; 0 .. n - 1) link!chainUnique(g, i, i + 1);
		immutable edge = ecrs.registry.componentId!(Edge, chainUnique)();
		foreach (k, pool; pools) {
			measure("chain closure, left-linear", poolNames[k], () {
				ecrs.datalog.Program p;
				scope(exit) ecrs.datalog.free(p);
				immutable path = ecrs.datalog.derive(p, "bench.chainLeft", 1);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(path, x, y), ecrs.datalog.atom(edge, x, y)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(path, x, z), ecrs.datalog.atom(path, x, y), ecrs.datalog.atom(edge, y, z)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.evaluate(p, g.ctx, pool) == ecrs.datalog.Status.ok);
				return count(p, g.ctx, path, 2);
			});
		}
		foreach (k, pool; pools) {
			measure("chain closure, doubly recursive", poolNames[k], () {
				ecrs.datalog.Program p;
				scope(exit) ecrs.datalog.free(p);
				immutable path = ecrs.datalog.derive(p, "bench.chainDoubly", 1);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(path, x, y), ecrs.datalog.atom(edge, x, y)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(path, x, z), ecrs.datalog.atom(path, x, y), ecrs.datalog.atom(path, y, z)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.evaluate(p, g.ctx, pool) == ecrs.datalog.Status.ok);
				return count(p, g.ctx, path, 2);
			});
		}
	}

	// Sparse random DAG: few rounds, wide deltas, many index probes.
	{
		immutable n = 4000 * scale;
		auto g = graph(n);
		scope(exit) release(g);
		uint seed = 7;
		foreach (i; 0 .. n - 1)
			foreach (k; 0 .. 2) {
				seed = seed * 1103515245 + 12345;
				immutable span = 1 + (seed >> 8) % 40;
				if (i + span < n) link!dagUnique(g, i, i + span);
			}
		immutable edge = ecrs.registry.componentId!(Edge, dagUnique)();
		foreach (k, pool; pools) {
			measure("random DAG closure, right-linear", poolNames[k], () {
				ecrs.datalog.Program p;
				scope(exit) ecrs.datalog.free(p);
				immutable reach = ecrs.datalog.derive(p, "bench.dagReach", 1);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(reach, x, y), ecrs.datalog.atom(edge, x, y)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(reach, x, z), ecrs.datalog.atom(edge, x, y), ecrs.datalog.atom(reach, y, z)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.evaluate(p, g.ctx, pool) == ecrs.datalog.Status.ok);
				return count(p, g.ctx, reach, 2);
			});
		}

		// The same closure read through a trait: no fixpoint, a BFS per source.
		immutable traitEdge = ecrs.registry.componentId!(Edge, traitUnique)();
		foreach (i; 0 .. n)
			if (ecrs.context.hasComponent!(Edge, dagUnique)(g.ctx, g.nodes[i]))
				foreach (t; fp.dynarray.slice(ecrs.context.getComponent!(Edge, dagUnique)(g.ctx, g.nodes[i]).related))
					require(fp.dynarray.pushBack(ecrs.context.getOrAddComponent!(Edge, traitUnique)(g.ctx, g.nodes[i]).related, t));
		ecrs.registry.setRelationTraits(traitEdge, ecrs.registry.RelationTrait.transitive);
		scope(exit) ecrs.registry.setRelationTraits(traitEdge, 0);
		measure("random DAG closure, trait query", "serial", () {
			ecrs.datalog.Program p;
			scope(exit) ecrs.datalog.free(p);
			return count(p, g.ctx, traitEdge, 2);
		});
		foreach (k, pool; pools) {
			measure("random DAG closure, trait derived", poolNames[k], () {
				ecrs.datalog.Program p;
				scope(exit) ecrs.datalog.free(p);
				immutable copy = ecrs.datalog.derive(p, "bench.dagTrait", 1);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(copy, x, y), ecrs.datalog.atom(traitEdge, x, y)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.evaluate(p, g.ctx, pool) == ecrs.datalog.Status.ok);
				return count(p, g.ctx, copy, 2);
			});
		}

		// Negation over the closure: a second stratum.
		immutable node = ecrs.registry.componentId!Node();
		foreach (k, pool; pools) {
			measure("DAG closure + negated stratum", poolNames[k], () {
				ecrs.datalog.Program p;
				scope(exit) ecrs.datalog.free(p);
				immutable reach = ecrs.datalog.derive(p, "bench.dagReach2", 1);
				immutable unreached = ecrs.datalog.derive(p, "bench.dagUnreached", 0);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(reach, x, y), ecrs.datalog.atom(edge, x, y)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(reach, x, z), ecrs.datalog.atom(edge, x, y), ecrs.datalog.atom(reach, y, z)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(unreached, x), ecrs.datalog.atom(node, x), ecrs.datalog.negate(ecrs.datalog.atom(reach, ecrs.datalog.constant(g.nodes[0]), x))) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.evaluate(p, g.ctx, pool) == ecrs.datalog.Status.ok);
				return count(p, g.ctx, unreached, 1);
			});
		}

		// An up-to-date evaluate is a generation check per input.
		if (filter is null || strstr("up-to-date evaluate serial", filter) !is null) {
			ecrs.datalog.Program p;
			scope(exit) ecrs.datalog.free(p);
			immutable reach = ecrs.datalog.derive(p, "bench.dagReach3", 1);
			require(ecrs.datalog.addRule(p, ecrs.datalog.atom(reach, x, y), ecrs.datalog.atom(edge, x, y)) == ecrs.datalog.Status.ok);
			require(ecrs.datalog.addRule(p, ecrs.datalog.atom(reach, x, z), ecrs.datalog.atom(edge, x, y), ecrs.datalog.atom(reach, y, z)) == ecrs.datalog.Status.ok);
			require(ecrs.datalog.evaluate(p, g.ctx) == ecrs.datalog.Status.ok);
			enum calls = 1_000_000;
			immutable start = now();
			foreach (i; 0 .. calls) require(ecrs.datalog.evaluate(p, g.ctx) == ecrs.datalog.Status.ok);
			cast(void) printf("%-34s %-8s %10d calls %9.3f ms %8.1f ns/call\n", "up-to-date evaluate".ptr, "serial".ptr,
				calls, (now() - start) * 1e3, (now() - start) / calls * 1e9);
		}
	}

	// Same generation on a binary tree: joins through two base indexes and a derived relation, in wide rounds.
	{
		immutable depth = 8 + (scale > 1 ? 1 : 0);
		immutable n = (1 << (depth + 1)) - 1;
		auto g = graph(n);
		scope(exit) release(g);
		foreach (i; 1 .. n) link!treeUnique(g, (i - 1) / 2, i);
		immutable edge = ecrs.registry.componentId!(Edge, treeUnique)();
		foreach (k, pool; pools) {
			measure("same generation, binary tree", poolNames[k], () {
				ecrs.datalog.Program p;
				scope(exit) ecrs.datalog.free(p);
				immutable sg = ecrs.datalog.derive(p, "bench.sg", 1);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(sg, x, y), ecrs.datalog.atom(edge, z, x), ecrs.datalog.atom(edge, z, y)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.addRule(p, ecrs.datalog.atom(sg, x, y), ecrs.datalog.atom(edge, a, x), ecrs.datalog.atom(sg, a, b), ecrs.datalog.atom(edge, b, y)) == ecrs.datalog.Status.ok);
				require(ecrs.datalog.evaluate(p, g.ctx, pool) == ecrs.datalog.Status.ok);
				return count(p, g.ctx, sg, 2);
			});
		}
	}
	return 0;
}
