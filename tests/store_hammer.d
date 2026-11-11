/// Model test for `ecrs.context`: a random walk of entity and component changes, transactions kept and rolled back, renumberings and compactions, some under an allocator that refuses, each step checked against a plain array model that names entities by handles no renumbering changes.
module store_hammer;


static import ecrs.context;
static import ecrs.registry;
static import ecrs.relation;
static import fp.algorithms;
static import fp.dynarray;
static import fp.io;
static import fp.pointer;
static import fp.testing;

@nogc nothrow:


private struct Value { int value; }
private alias Link = ecrs.relation.Relation!1;

private enum size_t handles = 40;
private enum size_t noHandle = fp.pointer.notFound;

// What the store should hold for one handle: its entity's current id, and its components.
private struct Expected {
	bool live;
	ecrs.registry.EntityId id;
	bool hasValue;
	int value;
	size_t link = noHandle; // the handle its `Link` points at
}

private struct Walk {
	ecrs.context.Context context;
	Expected[handles] expected;
	Expected[handles] atBegin; // the model when the open transaction began
	fp.algorithms.Random random;
	ulong seed;
	size_t step;
	size_t refusals;
}

private void fail(ref Walk w, const(char)[] what) {
	cast(void) fp.io.print(fp.io.Console.error, "store_hammer: seed ", w.seed, ", step ", w.step, ": ", what, "\n");
	assert(false, "store_hammer: the store disagrees with its model");
}

// The store holds exactly what the model expects, and its own views agree.
private void check(ref Walk w) @trusted {
	size_t live = 0;
	foreach (ref e; w.expected) {
		if (!e.live) continue;
		++live;
		if (ecrs.context.hasComponent!Value(w.context, e.id) != e.hasValue) fail(w, "a value is present or absent wrongly");
		if (e.hasValue && ecrs.context.getComponent!Value(w.context, e.id).value != e.value) fail(w, "a value differs");
		if (ecrs.context.hasComponent!Link(w.context, e.id) != (e.link != noHandle)) fail(w, "a link is present or absent wrongly");
		if (e.link != noHandle && ecrs.context.getComponent!Link(w.context, e.id).related[0] != w.expected[e.link].id) fail(w, "a link names the wrong entity");
	}
	size_t counted = 0;
	foreach (entity; ecrs.context.entities(w.context)) counted += entity != ecrs.registry.invalidEntity;
	if (counted != live) fail(w, "the live entities differ in number");
	if (!ecrs.context.inTransaction(w.context) && !ecrs.context.validate(w.context)) fail(w, "the store's owners and index lists disagree");
}

private size_t pickHandle(ref Walk w, bool live) {
	immutable start = fp.algorithms.randomBelow(w.random, handles);
	foreach (i; 0 .. handles)
		if (w.expected[(start + i) % handles].live == live) return (start + i) % handles;
	return noHandle;
}

// Removes `h`'s link in store and model.
// False, changing nothing, if the store refused.
private bool unlink(ref Walk w, size_t h) {
	if (!ecrs.context.removeComponent!Link(w.context, w.expected[h].id)) return false;
	w.expected[h].link = noHandle;
	return true;
}

// Removes entity `h` once nothing links to it.
// False if the store refused any part; what was done, the model records.
private bool remove(ref Walk w, size_t h) {
	foreach (other; 0 .. handles)
		if (w.expected[other].live && w.expected[other].link == h && !unlink(w, other)) return false;
	if (!ecrs.context.removeEntity(w.context, w.expected[h].id)) return false;
	w.expected[h] = Expected.init;
	return true;
}

// Renumbers by a random permutation that keeps entity 0. False, changing nothing, if the store refused.
private bool reorder(ref Walk w) @trusted {
	immutable n = fp.dynarray.length(w.context.indexTable);
	if (n < 3) return true;
	auto order = cast(size_t*) fp.pointer.allocator(null, n * size_t.sizeof);
	if (order is null) return false;
	scope(exit) cast(void) fp.pointer.allocator(order, 0);
	foreach (i; 0 .. n) order[i] = i;
	foreach_reverse (i; 2 .. n) {
		immutable j = 1 + fp.algorithms.randomBelow(w.random, i);
		immutable t = order[i];
		order[i] = order[j];
		order[j] = t;
	}
	if (!ecrs.context.reorderEntities(w.context, order[0 .. n])) return false;
	foreach (ref e; w.expected) {
		if (!e.live) continue;
		foreach (i; 0 .. n)
			if (order[i] == e.id) {
				e.id = cast(ecrs.registry.EntityId) i;
				break;
			}
	}
	return true;
}

// Compacts the store.
// False, changing nothing, if the store refused.
private bool compact(ref Walk w) {
	ecrs.registry.EntityId[handles] before;
	foreach (h, ref e; w.expected) before[h] = e.id;
	if (!ecrs.context.compact(w.context)) return false;
	// Live entities keep their order, so an entity's new id is one more than the live ids below its old one.
	foreach (h, ref e; w.expected) {
		if (!e.live) continue;
		ecrs.registry.EntityId below = 0;
		foreach (other; 0 .. handles) below += w.expected[other].live && before[other] < before[h];
		e.id = below + 1;
	}
	return true;
}

// One random change to store and model.
// False if the store refused it, having changed neither beyond what the model recorded.
private bool change(ref Walk w) @trusted {
	immutable inTransaction = ecrs.context.inTransaction(w.context);
	switch (fp.algorithms.randomBelow(w.random, 12)) {
		case 0: case 1: {
			immutable h = pickHandle(w, false);
			if (h == noHandle) return true;
			immutable id = ecrs.context.addEntity(w.context);
			if (id == ecrs.registry.invalidEntity) return false;
			w.expected[h] = Expected(true, id);
			return true;
		}
		case 2: {
			immutable h = pickHandle(w, true);
			return h == noHandle || remove(w, h);
		}
		case 3: case 4: {
			immutable h = pickHandle(w, true);
			if (h == noHandle) return true;
			immutable value = cast(int) fp.algorithms.randomBelow(w.random, 1000);
			if (!ecrs.context.setComponent!Value(w.context, w.expected[h].id, Value(value))) return false;
			w.expected[h].hasValue = true;
			w.expected[h].value = value;
			return true;
		}
		case 5: {
			immutable h = pickHandle(w, true);
			if (h == noHandle || !w.expected[h].hasValue) return true;
			if (!ecrs.context.removeComponent!Value(w.context, w.expected[h].id)) return false;
			w.expected[h].hasValue = false;
			return true;
		}
		case 6: case 7: {
			immutable h = pickHandle(w, true), to = pickHandle(w, true);
			if (h == noHandle) return true;
			Link link;
			link.related[0] = w.expected[to].id;
			if (!ecrs.context.setComponent!Link(w.context, w.expected[h].id, link)) return false;
			w.expected[h].link = to;
			return true;
		}
		case 8: {
			immutable h = pickHandle(w, true);
			return h == noHandle || w.expected[h].link == noHandle || unlink(w, h);
		}
		case 9:
			if (inTransaction) {
				if (fp.algorithms.randomChance(w.random, 1, 2)) ecrs.context.commitTransaction(w.context);
				else {
					ecrs.context.rollbackTransaction(w.context);
					w.expected = w.atBegin;
				}
			} else {
				w.atBegin = w.expected;
				ecrs.context.beginTransaction(w.context);
			}
			return true;
		case 10: return inTransaction || reorder(w);
		default: return inTransaction || compact(w);
	}
}

unittest { // every seed's walk agrees with its model after each step, refused or not
	enum seeds = 60, steps = 400;
	size_t refusals = 0;
	foreach (seed; 1 .. seeds + 1) {
		Walk w;
		w.context = ecrs.context.create();
		scope(exit) ecrs.context.free(w.context);
		w.random = fp.algorithms.createRandom(seed);
		w.seed = seed;
		foreach (step; 0 .. steps) {
			w.step = step;
			immutable rationed = fp.algorithms.randomChance(w.random, 1, 4);
			fp.pointer.Allocator previous;
			if (rationed) previous = fp.testing.limitAllocations(fp.algorithms.randomBelow(w.random, 3));
			immutable done = change(w);
			if (rationed) fp.testing.restoreAllocator(previous);
			if (!done && !rationed) fail(w, "a change failed though nothing refused it");
			refusals += !done;
			check(w);
		}
		if (ecrs.context.inTransaction(w.context)) ecrs.context.rollbackTransaction(w.context);
	}
	assert(refusals > seeds);
}
