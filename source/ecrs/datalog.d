/// A Datalog query layer over the store, whose relations are components: a component is the relation `C(owner, columns...)` its `ecrs.registry.RelationShape` describes, so the store stays the only home of facts, derived ones included. A `Program` holds rules, evaluates them bottom-up, stratified and semi-naive, and writes what they derive back into components it owns.
///
/// Provenance: a rule's head must be a relation the program declared with `derive`, and nothing else may write those. Base relations are any other components, written by ordinary code. `evaluate` recomputes the derived relations from scratch, and only when a relation the rules mention has a new `ecrs.context.generation`.
///
/// `invalidEntity` in a relation slot means no target: tuples holding it are not facts. Within one rule, it also marks an unbound variable.
///
/// Binary relations may carry `ecrs.registry.RelationTrait`s, read as closures at join time. Given a thread pool, `evaluate` splits each round's joins across it; inserting the results stays on the calling thread.
module ecrs.datalog;

import core.stdc.string : memcpy;

static import bc.spinlock;
static import bc.threadpool;
static import ecrs.context;
static import ecrs.registry;
static import ecrs.relation;
static import ecrs.storage;
static import fp.dynarray;
static import fp.pointer;
static import std.algorithm.sorting;

public import ecrs.registry : EntityId, invalidEntity;

@nogc nothrow:


/// The most arguments an atom may have, its owning entity included.
enum size_t maxArity = 8;

/// How a `Program` operation ended.
enum Status {
	ok, /// It succeeded.
	invalid, /// A rule or query was malformed: an arity mismatch, a head not derived, or an unsafe variable.
	unstratifiable, /// The rules recurse through negation.
	outOfMemory, /// An allocation failed.
}

// Slice assignment needs druntime under -betterC.
private void copy(T)(T[] to, const(T)[] from) @trusted {
	assert(to.length == from.length);
	if (from.length) memcpy(to.ptr, from.ptr, from.length * T.sizeof);
}

// `fp.dynarray.concatenate` reports appending nothing to a null dynarray as a failure.
private bool append(T)(ref T* to, const(T)[] from) {
	return from.length == 0 || fp.dynarray.concatenate(to, from);
}

private bool contains(const(size_t)* list, size_t value) @trusted {
	foreach (v; fp.dynarray.slice(list)) if (v == value) return true;
	return false;
}


/// The term naming variable `id`; variables of one rule are numbered from 0.
///
/// Examples:
/// ---
/// auto x = variable(0);
/// assert(x.isVar && x.varId == 0);
/// ---
ecrs.relation.Term variable(size_t id) {
	ecrs.relation.Term t;
	t.isVar = true;
	t.varId = id;
	return t;
}

/// Code for `mixin` that declares a `variable` for each of `names`, numbered from 0 in order, so a rule's variables can be declared without numbering them by hand.
///
/// Examples:
/// ---
/// mixin(createVariables!("x", "y"));
/// assert(x.varId == 0 && y.varId == 1);
/// ---
template createVariables(names...) {
	static assert(names.length > 0, "createVariables needs at least one name");
	enum string createVariables = "auto " ~ variableDeclarations!(0, names) ~ ";";
}

private template variableDeclarations(int id, names...) {
	static if (names.length == 0) enum string variableDeclarations = "";
	else enum string variableDeclarations = (id ? ", " : "") ~ names[0] ~ " = ecrs.datalog.variable(" ~ id.stringof ~ ")" ~ variableDeclarations!(id + 1, names[1 .. $]);
}

/// The term naming entity `e`.
///
/// Examples:
/// ---
/// auto c = constant(3);
/// assert(!c.isVar && c.constant == 3);
/// ---
ecrs.relation.Term constant(EntityId e) { return ecrs.relation.Term(e); }

/// `relation(args...)`, possibly negated, as `atom` and `negate` build it. The first argument is the owning entity.
struct Atom {
	size_t relation = fp.pointer.notFound; /// The relation's component id.
	bool negated = false; /// Whether the atom holds when the tuple is absent.
	size_t arity = 0; /// How many of `args` are used.
	ecrs.relation.Term[maxArity] args; /// The arguments: variables or constants.
}

/// The atom `relation(args...)`, whose arguments are `variable`s or `constant`s, the owning entity first.
///
/// Examples:
/// ---
/// auto a = atom(5, variable(0), constant(2));
/// assert(a.relation == 5 && a.arity == 2 && !a.negated);
/// ---
Atom atom(size_t relation, const(ecrs.relation.Term)[] args...) {
	assert(args.length >= 1 && args.length <= maxArity);
	Atom a;
	a.relation = relation;
	a.arity = args.length;
	foreach (i, t; args) a.args[i] = t;
	return a;
}

/// `a`, negated: it holds where `a`'s tuple is absent.
///
/// Examples:
/// ---
/// assert(negate(atom(5, variable(0))).negated);
/// ---
Atom negate(Atom a) {
	a.negated = true;
	return a;
}

private struct Rule {
	Atom head;
	Atom* body; // dynarray
	size_t varCount;
}

// (key, owner) pairs, sorted and unique. The owner's tuples are rescanned for the rest, so inserting into a derived list never invalidates an entry.
private struct IndexEntry { EntityId key, owner; }

private struct Index {
	size_t relation, column, generation;
	IndexEntry* entries; // dynarray
}

/// A Datalog program: rules over component relations, the relations it derives, and the caches `evaluate` keeps. It is plain data, released only by `free`, and must not move while `attach`ed.
struct Program {
	private Rule* rules = null;
	private size_t* derived = null;
	private size_t* inputs = null; // every relation a rule mentions
	private size_t* snapshot = null; // their generations after the last evaluate
	private Index* indexes = null;
	private bc.spinlock.SpinLock indexLock; // parallel joins build indexes lazily
	private size_t traitsSeen = 0; // `traitsEpoch` at the last evaluate
	private bool evaluated = false;
}

private void dropIndexes(ref Program self) @trusted {
	foreach (ref index; fp.dynarray.slice(self.indexes)) fp.dynarray.free(index.entries);
	if (self.indexes !is null) fp.dynarray.clear(self.indexes);
}

/// Frees everything `self` owns, leaving it as `Program.init`; the facts it derived stay in the store. `detach` it first if it is attached.
///
/// Examples:
/// ---
/// Program p;
/// assert(derive(p, "example.free", 0) != fp.pointer.notFound);
/// free(p);
/// ---
void free(ref Program self) @trusted {
	foreach (ref r; fp.dynarray.slice(self.rules)) fp.dynarray.free(r.body);
	fp.dynarray.free(self.rules);
	fp.dynarray.free(self.derived);
	fp.dynarray.free(self.inputs);
	fp.dynarray.free(self.snapshot);
	dropIndexes(self);
	fp.dynarray.free(self.indexes);
	self = Program.init;
}


private bool shapeMatches(const ref Atom a) {
	return a.relation != fp.pointer.notFound && a.arity == 1 + ecrs.registry.lookupRelationShape(a.relation).columns;
}

private bool positivelyBound(const(Atom)[] body, size_t var) {
	foreach (ref a; body)
		if (!a.negated)
			foreach (t; a.args[0 .. a.arity])
				if (t.isVar && t.varId == var) return true;
	return false;
}

// Checks arities and safety, every variable of a negated atom appearing in a positive one, and counts the variables.
private bool validBody(const(Atom)[] body, out size_t varCount) {
	foreach (ref a; body) {
		if (!shapeMatches(a)) return false;
		foreach (t; a.args[0 .. a.arity])
			if (t.isVar && t.varId + 1 > varCount) varCount = t.varId + 1;
	}
	foreach (ref a; body) {
		if (!a.negated) continue;
		foreach (t; a.args[0 .. a.arity])
			if (t.isVar && !positivelyBound(body, t.varId)) return false;
	}
	return true;
}

/// Declares a relation `self` derives, named `name`, with `columns` entity columns after the owner, registering its component on first use: a dynamic `ecrs.relation.Relation` holding `columns` ids per tuple, or a tag when `columns` is 0.
///
/// Returns its component id, or `fp.pointer.notFound`, leaving `self` as it was, if `name` is a component of another shape or allocation fails.
///
/// Examples:
/// ---
/// Program p;
/// scope(exit) free(p);
/// immutable ancestor = derive(p, "example.ancestor", 1);
/// assert(ancestor != fp.pointer.notFound);
/// assert(derive(p, "example.ancestor", 1) == ancestor);
/// assert(derive(p, "example.ancestor", 2) == fp.pointer.notFound);
/// ---
size_t derive(ref Program self, const(char)[] name, size_t columns) @trusted {
	assert(columns < maxArity);
	immutable shape = columns == 0 ? ecrs.registry.RelationShape.init : ecrs.registry.RelationShape(columns, true);

	auto terminated = cast(char*) fp.pointer.allocFunction(null, name.length + 1);
	if (terminated is null) return fp.pointer.notFound;
	scope(exit) cast(void) fp.pointer.allocFunction(terminated, 0);
	copy(terminated[0 .. name.length], name);
	terminated[name.length] = '\0';

	size_t id = ecrs.registry.lookupId(terminated);
	if (id == fp.pointer.notFound) {
		alias List = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);
		auto hooks = columns == 0 ? ecrs.registry.Hooks.init : ecrs.registry.hooksFor!List();
		hooks.shape = shape;
		id = ecrs.registry.registerType(name, ecrs.registry.nextId(), columns == 0 ? 1 : List.sizeof, hooks);
		if (id == fp.pointer.notFound) return fp.pointer.notFound;
	} else {
		immutable existing = ecrs.registry.lookupRelationShape(id);
		if (existing.columns != shape.columns || existing.dynamic != shape.dynamic) return fp.pointer.notFound;
	}

	if (!contains(self.derived, id) && !fp.dynarray.pushBack(self.derived, id)) return fp.pointer.notFound;
	self.evaluated = false;
	return id;
}

/// Adds the rule `head :- body`: `head` holds for every binding of its variables under which each atom of `body` does.
///
/// Returns `Status.invalid` if an atom's arity does not match its relation's shape, `head` is negated or not a relation `self` derives, or a variable of `head` or of a negated atom appears in no positive atom of `body`; `Status.outOfMemory` if allocation fails. Either way `self` is left as it was.
///
/// Examples:
/// ---
/// alias Parent = ecrs.relation.Relation!1;
/// immutable parent = ecrs.registry.componentId!Parent();
/// Program p;
/// scope(exit) free(p);
/// immutable ancestor = derive(p, "example.ancestor", 1);
/// mixin(createVariables!("x", "y", "z"));
/// assert(addRule(p, atom(ancestor, x, y), atom(parent, x, y)) == Status.ok);
/// assert(addRule(p, atom(ancestor, x, z), atom(parent, x, y), atom(ancestor, y, z)) == Status.ok);
/// assert(addRule(p, atom(ancestor, x, z), atom(parent, x, y)) == Status.invalid);
/// ---
Status addRule(ref Program self, Atom head, const(Atom)[] body...) @trusted {
	size_t varCount;
	if (head.negated || !shapeMatches(head) || !contains(self.derived, head.relation)) return Status.invalid;
	if (!validBody(body, varCount)) return Status.invalid;
	foreach (t; head.args[0 .. head.arity])
		if (t.isVar && !positivelyBound(body, t.varId)) return Status.invalid;

	Rule rule = Rule(head, null, varCount);
	if (!append(rule.body, body)) return Status.outOfMemory;
	immutable inputCount = fp.dynarray.length(self.inputs);
	bool note(size_t relation) {
		if (contains(self.inputs, relation)) return true;
		if (!fp.dynarray.pushBack(self.inputs, relation)) return false;
		if (fp.dynarray.pushBack(self.snapshot, size_t(0))) return true;
		cast(void) fp.dynarray.popBack(self.inputs);
		return false;
	}
	bool noted = note(head.relation);
	foreach (ref a; body) noted = noted && note(a.relation);
	if (!noted || !fp.dynarray.pushBack(self.rules, rule)) {
		fp.dynarray.free(rule.body);
		immutable added = fp.dynarray.length(self.inputs) - inputCount;
		if (added > 0) {
			cast(void) fp.dynarray.popBackCount(self.inputs, added);
			cast(void) fp.dynarray.popBackCount(self.snapshot, added);
		}
		return Status.outOfMemory;
	}
	self.evaluated = false;
	return Status.ok;
}


/// Relabels the entity constants in `self`'s rules, `remap[old]` being the id `old` becomes, and forces the next `evaluate` to recompute. `attach` makes every renumbering of a context call it. It cannot fail.
///
/// Examples:
/// ---
/// alias Parent = ecrs.relation.Relation!1;
/// Program p;
/// scope(exit) free(p);
/// immutable ofTwo = derive(p, "example.childOfTwo", 0);
/// assert(addRule(p, atom(ofTwo, variable(0)), atom(ecrs.registry.componentId!Parent(), variable(0), constant(2))) == Status.ok);
/// immutable EntityId[3] remap = [0, 2, 1];
/// remapEntities(p, remap[]);
/// ---
void remapEntities(ref Program self, const(EntityId)[] remap) @trusted {
	void fix(ref Atom a) {
		foreach (ref t; a.args[0 .. a.arity])
			if (!t.isVar && t.constant < remap.length) t.constant = remap[t.constant];
	}
	foreach (ref r; fp.dynarray.slice(self.rules)) {
		fix(r.head);
		foreach (ref a; fp.dynarray.slice(r.body)) fix(a);
	}
	// Derived lists are sorted by id, so the old order no longer holds.
	dropIndexes(self);
	self.evaluated = false;
}

private void remapHook(void* program, const(EntityId)[] remap) {
	remapEntities(*cast(Program*) program, remap);
}

/// Registers `self` as a holder of entity ids, so renumbering `ctx` relabels its rule constants. `self` must not move until `detach`.
///
/// Returns false if allocation fails, registering nothing.
///
/// Examples:
/// ---
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// Program p;
/// scope(exit) free(p);
/// assert(attach(ctx, p));
/// assert(detach(ctx, p));
/// ---
bool attach(ref ecrs.context.Context ctx, ref Program self) {
	return ecrs.context.addRemapHook(ctx, &remapHook, &self);
}

/// Undoes `attach`, returning false if `self` is not attached to `ctx`.
///
/// Examples:
/// ---
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// Program p;
/// assert(!detach(ctx, p));
/// ---
bool detach(ref ecrs.context.Context ctx, ref Program self) {
	return ecrs.context.removeRemapHook(ctx, &remapHook, &self);
}


private alias TupleFn = void delegate(const(EntityId)[]) @nogc nothrow;

// Calls `fn` with each tuple `e` owns in `relation`, owner first.
private void forEachTuple(const ref ecrs.context.Context ctx, size_t relation, ecrs.registry.RelationShape shape, EntityId e, scope TupleFn fn) @trusted {
	if (!ecrs.context.hasComponent(ctx, e, relation)) return;
	EntityId[maxArity] tuple;
	tuple[0] = e;
	immutable arity = 1 + shape.columns;
	auto p = ecrs.context.getComponent(ctx, e, relation);
	if (!shape.dynamic) {
		copy(tuple[1 .. arity], (cast(const(EntityId)*) p)[0 .. shape.columns]);
		fn(tuple[0 .. arity]);
		return;
	}
	auto list = *cast(const(EntityId*)*) p;
	immutable n = fp.dynarray.length(list);
	for (size_t i = 0; i + shape.columns <= n; i += shape.columns) {
		copy(tuple[1 .. arity], list[i .. i + shape.columns]);
		fn(tuple[0 .. arity]);
	}
}

// Ditto, but only tuples whose first column is `first`, found by binary search in a derived relation's sorted list.
private void forEachTupleStarting(const ref ecrs.context.Context ctx, size_t relation, ecrs.registry.RelationShape shape, EntityId e, EntityId first, scope TupleFn fn) @trusted {
	if (!shape.dynamic) return forEachTuple(ctx, relation, shape, e, fn);
	if (!ecrs.context.hasComponent(ctx, e, relation)) return;
	auto list = *cast(const(EntityId*)*) ecrs.context.getComponent(ctx, e, relation);
	immutable k = shape.columns;
	immutable groups = fp.dynarray.length(list) / k;
	size_t lo = 0, hi = groups;
	while (lo < hi) {
		immutable mid = (lo + hi) / 2;
		if (list[mid * k] < first) lo = mid + 1;
		else hi = mid;
	}
	EntityId[maxArity] tuple;
	tuple[0] = e;
	for (; lo < groups && list[lo * k] == first; ++lo) {
		copy(tuple[1 .. 1 + k], list[lo * k .. lo * k + k]);
		fn(tuple[0 .. 1 + k]);
	}
}

private bool holds(const ref ecrs.context.Context ctx, size_t relation, ecrs.registry.RelationShape shape, const(EntityId)[] tuple) {
	bool found = false;
	forEachTuple(ctx, relation, shape, tuple[0], (t) {
		if (t == tuple) found = true;
	});
	return found;
}

private bool lessTuple(const(EntityId)[] a, const(EntityId)[] b) {
	foreach (i; 0 .. a.length)
		if (a[i] != b[i]) return a[i] < b[i];
	return false;
}

private enum size_t radixThreshold = 256;
private enum size_t radixDigitBits = 12;

// LSD radix sort of `keys` below `1 << bits`, in as few passes of at most `radixDigitBits` as cover them, skipping digits all keys share. Returns `keys` or `buffer`, whichever holds the result.
private ulong[] radixSort(ulong[] keys, ulong[] buffer, size_t bits) {
	assert(buffer.length == keys.length && bits <= 64);
	if (bits == 0) return keys;
	immutable passes = (bits + radixDigitBits - 1) / radixDigitBits;
	immutable digit = (bits + passes - 1) / passes;
	immutable size_t mask = (size_t(1) << digit) - 1;
	size_t[1 << radixDigitBits] counts;
	auto from = keys, to = buffer;
	foreach (pass; 0 .. passes) {
		immutable shift = pass * digit;
		counts[0 .. mask + 1] = 0;
		foreach (key; from) ++counts[(key >> shift) & mask];
		if (counts[(from[0] >> shift) & mask] == from.length) continue;
		size_t sum = 0;
		foreach (ref c; counts[0 .. mask + 1]) {
			immutable count = c;
			c = sum;
			sum += count;
		}
		foreach (key; from) to[counts[(key >> shift) & mask]++] = key;
		auto swap = from;
		from = to;
		to = swap;
	}
	return from;
}

// Sorts flat `arity`-wide rows and drops repeats; rows of up to two ids sort as integers packed only as wide as the largest id needs. False if allocation fails, leaving `rows` unsorted.
private bool sortUnique(ref EntityId* rows, size_t arity) @trusted {
	immutable n = fp.dynarray.length(rows) / arity;
	if (n <= 1) return true;
	size_t kept = 0;
	if (arity <= 2) {
		EntityId all = 0;
		foreach (id; rows[0 .. n * arity]) all |= id;
		size_t width = 0;
		while (width < EntityId.sizeof * 8 && (all >> width) != 0) ++width;
		immutable radix = n >= radixThreshold;
		auto storage = cast(ulong*) fp.pointer.allocFunction(null, (radix ? 2 * n : n) * ulong.sizeof);
		if (storage is null) return false;
		scope(exit) cast(void) fp.pointer.allocFunction(storage, 0);
		foreach (i; 0 .. n)
			storage[i] = arity == 1 ? rows[i] : (cast(ulong) rows[2 * i] << width) | rows[2 * i + 1];
		auto keys = storage[0 .. n];
		if (radix) keys = radixSort(keys, storage[n .. 2 * n], arity * width);
		else std.algorithm.sorting.sort(keys);
		immutable ulong low = (1UL << width) - 1;
		foreach (i; 0 .. n) {
			if (i > 0 && keys[i] == keys[i - 1]) continue;
			if (arity == 1) rows[kept] = cast(EntityId) keys[i];
			else { rows[2 * kept] = cast(EntityId)(keys[i] >> width); rows[2 * kept + 1] = cast(EntityId)(keys[i] & low); }
			++kept;
		}
		cast(void) fp.dynarray.popBackCount(rows, (n - kept) * arity);
		return true;
	}

	auto order = cast(size_t*) fp.pointer.allocFunction(null, n * size_t.sizeof);
	if (order is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(order, 0);
	foreach (i; 0 .. n) order[i] = i;
	std.algorithm.sorting.sort!((a, b) => lessTuple(rows[a * arity .. a * arity + arity], rows[b * arity .. b * arity + arity]))(order[0 .. n]);
	EntityId* sorted = null;
	foreach (i; 0 .. n) {
		auto row = rows[order[i] * arity .. order[i] * arity + arity];
		if (kept > 0 && sorted[(kept - 1) * arity .. kept * arity] == row) continue;
		if (!append(sorted, row)) {
			fp.dynarray.free(sorted);
			return false;
		}
		++kept;
	}
	fp.dynarray.free(rows);
	rows = sorted;
	return true;
}

// Merges sorted, unique `rows` into a derived relation from the back, appending the new ones to `delta`. False if allocation fails.
private bool insertFacts(ref ecrs.context.Context ctx, size_t relation, const(EntityId)[] rows, ref EntityId* delta) @trusted {
	immutable shape = ecrs.registry.lookupRelationShape(relation);
	immutable k = shape.columns, arity = 1 + k;
	immutable n = rows.length / arity;
	EntityId* fresh = null; // this owner's new rows, without the owner
	scope(exit) fp.dynarray.free(fresh);

	for (size_t start = 0, end; start < n; start = end) {
		immutable e = rows[start * arity];
		for (end = start + 1; end < n && rows[end * arity] == e; ++end) {}
		if (k == 0) {
			if (ecrs.context.hasComponent(ctx, e, relation)) continue;
			if (ecrs.context.addComponent(ctx, e, relation) is null || !fp.dynarray.pushBack(delta, e)) return false;
			continue;
		}

		auto list = cast(EntityId**) ecrs.context.getOrAddComponent(ctx, e, relation);
		if (list is null) return false;
		immutable existing = fp.dynarray.length(*list) / k;
		if (fresh !is null) fp.dynarray.clear(fresh);
		size_t lo = 0;
		foreach (i; start .. end) {
			auto row = rows[i * arity + 1 .. i * arity + arity];
			// Rows ascend, so each search resumes where the last ended, galloping to bound it; every row before `lo` is less than `row`.
			size_t hi = lo, step = 1;
			while (hi < existing && lessTuple((*list)[hi * k .. hi * k + k], row)) {
				lo = hi + 1;
				hi = lo + step;
				step *= 2;
			}
			if (hi > existing) hi = existing;
			while (lo < hi) {
				immutable mid = (lo + hi) / 2;
				if (lessTuple((*list)[mid * k .. mid * k + k], row)) lo = mid + 1;
				else hi = mid;
			}
			if (lo < existing && (*list)[lo * k .. lo * k + k] == row) continue;
			if (!append(fresh, row) || !append(delta, rows[i * arity .. i * arity + arity])) return false;
		}
		immutable added = fp.dynarray.length(fresh) / k;
		if (added == 0) continue;

		if (fp.dynarray.grow(*list, added * k) is null) return false;
		auto all = *list;
		// Backward merge: `i` walks the old rows, `j` the new, `w` the output.
		size_t i = existing, j = added, w = existing + added;
		while (j > 0) {
			if (i > 0 && lessTuple(fresh[(j - 1) * k .. j * k], all[(i - 1) * k .. i * k])) {
				--i;
				copy(all[(w - 1) * k .. w * k], all[i * k .. i * k + k]);
			} else {
				--j;
				copy(all[(w - 1) * k .. w * k], fresh[j * k .. j * k + k]);
			}
			--w;
		}
	}
	return true;
}


private bool entryLess(IndexEntry a, IndexEntry b) {
	return a.key < b.key || (a.key == b.key && a.owner < b.owner);
}

private void settle(ref IndexEntry* entries) @trusted {
	immutable n = fp.dynarray.length(entries);
	if (n == 0) return;
	std.algorithm.sorting.sort!entryLess(entries[0 .. n]);
	size_t kept = 1;
	foreach (i; 1 .. n)
		if (entries[i] != entries[kept - 1]) entries[kept++] = entries[i];
	cast(void) fp.dynarray.popBackCount(entries, n - kept);
}

// Sets `entries` to `relation`'s index on `column`, rebuilt if stale; the store is fixed during a join, so parallel joins share it.
private bool indexOn(ref Program self, const ref ecrs.context.Context ctx, size_t relation, size_t column, out const(IndexEntry)[] entries) @trusted {
	immutable generation = ecrs.context.generation(ctx, relation);
	Index* find() {
		foreach (ref candidate; fp.dynarray.slice(self.indexes))
			if (candidate.relation == relation && candidate.column == column) return &candidate;
		return null;
	}

	bc.spinlock.readLock(self.indexLock);
	if (auto current = find())
		if (current.generation == generation) {
			entries = fp.dynarray.slice(current.entries);
			bc.spinlock.readUnlock(self.indexLock);
			return true;
		}
	bc.spinlock.readUnlock(self.indexLock);

	bc.spinlock.writeLock(self.indexLock);
	scope(exit) bc.spinlock.writeUnlock(self.indexLock);
	Index* index = find();
	if (index is null) {
		if (!fp.dynarray.pushBack(self.indexes, Index(relation, column, size_t.max, null))) return false;
		index = fp.dynarray.back(self.indexes);
	}

	if (index.generation != generation) {
		index.generation = size_t.max;
		if (index.entries !is null) fp.dynarray.clear(index.entries);
		bool built = true;
		if (auto storage = ecrs.context.getStorage(ctx, relation)) {
			immutable shape = ecrs.registry.lookupRelationShape(relation);
			foreach (o; ecrs.storage.owners(*storage)) {
				if (o == invalidEntity) continue;
				forEachTuple(ctx, relation, shape, o, (t) {
					if (t[column] != invalidEntity) built = built && fp.dynarray.pushBack(index.entries, IndexEntry(t[column], o));
				});
			}
		}
		if (!built) return false;
		settle(index.entries);
		index.generation = generation;
	}
	entries = fp.dynarray.slice(index.entries);
	return true;
}

// Folds facts just inserted into `relation` into the indexes current at generation `before`, so a round pays for its delta, not a rebuild.
private void extendIndexes(ref Program self, const ref ecrs.context.Context ctx, size_t relation, size_t before, const(EntityId)* delta, size_t arity) @trusted {
	immutable after = ecrs.context.generation(ctx, relation);
	immutable n = fp.dynarray.length(delta) / arity;
	foreach (ref index; fp.dynarray.slice(self.indexes)) {
		if (index.relation != relation || index.generation != before) continue;
		bool extended = true;
		foreach (i; 0 .. n) {
			auto t = delta[i * arity .. i * arity + arity];
			if (t[index.column] != invalidEntity)
				extended = extended && fp.dynarray.pushBack(index.entries, IndexEntry(t[index.column], t[0]));
		}
		settle(index.entries);
		// An index that could not grow is merely stale: `indexOn` rebuilds it.
		index.generation = extended ? after : size_t.max;
	}
}

private const(IndexEntry)[] lookup(const(IndexEntry)[] entries, EntityId key) {
	size_t lo = 0, hi = entries.length;
	while (lo < hi) {
		immutable mid = (lo + hi) / 2;
		if (entries[mid].key < key) lo = mid + 1;
		else hi = mid;
	}
	size_t end = lo;
	while (end < entries.length && entries[end].key == key) ++end;
	return entries[lo .. end];
}


/// Receives one solution of a query, its bindings indexed by variable id, and returns whether to go on to the next.
alias Emit = bool delegate(const(EntityId)[] bindings) @nogc nothrow;

private enum size_t cachedIndexes = 8;

private struct CachedIndex {
	size_t relation, column;
	const(IndexEntry)[] entries;
}

// Below this many ids a plan depth remembers the tuples its last key matched; past it, the copy could rival the relation.
private enum size_t memoLimit = 1 << 16;
// A plan depth records its tuples only while at least one call in this many repeats the previous key.
private enum size_t memoRepeatRatio = 8;

// The tuples one plan depth's atom matched for `key`, its arguments' values then, unbound ones `invalidEntity`.
private struct Memo {
	EntityId[maxArity] key;
	EntityId* tuples = null;
	size_t calls = 0, repeats = 0;
	bool valid = false; // `tuples` holds every match for `key`
}

// One rule body being solved, a nested-loop join in `plan` order; `deltaAtom` reads `delta` rather than the store, which is all semi-naive evaluation changes.
private struct Solver {
	ecrs.context.Context* ctx;
	Program* program;
	const(Atom)[] body;
	size_t[] plan;
	size_t deltaAtom = fp.pointer.notFound;
	const(EntityId)[] delta;
	EntityId[] bindings;
	size_t partition = 0, partitions = 1, candidates = 0; // with `partitions` above 1, only every `partitions`-th first-atom candidate is tried
	bool presplit = false; // the first atom's enumerator already kept only this partition
	const(bool)[] sorted; // per body atom: whether its list is sorted, a relation this program derives
	const(ecrs.registry.RelationShape)[] shapes; // per body atom, looked up once, since each lookup takes the registry lock
	CachedIndex[cachedIndexes] indexes; // fetched this join; current until it ends
	size_t indexCount = 0;
	bool* seen = null; // closure scratch, one flag per entity id; all false between uses
	Memo[] memos; // per plan depth; the store is fixed for the join, so a memo stays current until it ends
	size_t seenLength = 0;
	bool stopped = false;
	bool failed = false; // an allocation failed; `stopped` is set too
}

private void fail(ref Solver s) {
	s.failed = true;
	s.stopped = true;
}

// `indexOn`, remembered for the rest of the join; taking the lock on every probe was a fifth of a recursive join's time.
private const(IndexEntry)[] index(ref Solver s, size_t relation, size_t column) @trusted {
	foreach (ref c; s.indexes[0 .. s.indexCount])
		if (c.relation == relation && c.column == column) return c.entries;
	const(IndexEntry)[] entries;
	if (!indexOn(*s.program, *s.ctx, relation, column, entries)) {
		fail(s);
		return null;
	}
	if (s.indexCount < s.indexes.length) s.indexes[s.indexCount++] = CachedIndex(relation, column, entries);
	return entries;
}

private EntityId valueOf(ref Solver s, ecrs.relation.Term t) {
	return t.isVar ? s.bindings[t.varId] : t.constant;
}


private bool[] seenFlags(ref Solver s) @trusted {
	immutable n = fp.dynarray.length(s.ctx.indexTable);
	if (s.seenLength < n) {
		auto grown = cast(bool*) fp.pointer.allocFunction(s.seen, n);
		if (grown is null) {
			fail(s);
			return null;
		}
		s.seen = grown;
		s.seen[s.seenLength .. n] = false;
		s.seenLength = n;
	}
	return s.seen[0 .. n];
}

// Each entity one edge from `e`: targets going forward, owners going back through the column-1 index, both when symmetric. May repeat.
private void forEachNeighbor(ref Solver s, size_t relation, ecrs.registry.RelationShape shape, EntityId e, bool forward, scope void delegate(EntityId) @nogc nothrow fn) @trusted {
	const(ecrs.context.Context)* ctx = s.ctx;
	immutable symmetric = (shape.traits & ecrs.registry.RelationTrait.symmetric) != 0;
	if (forward || symmetric)
		forEachTuple(*ctx, relation, shape, e, (t) { if (t[1] != invalidEntity) fn(t[1]); });
	if (!forward || symmetric)
		foreach (entry; lookup(index(s, relation, 1), e)) fn(entry.owner);
}

// Whether `e` occurs in `relation` at all: the domain `reflexive` ranges over.
private bool inField(ref Solver s, size_t relation, ecrs.registry.RelationShape shape, EntityId e) @trusted {
	bool found = false;
	forEachTuple(*s.ctx, relation, shape, e, (t) { found |= t[1] != invalidEntity; });
	return found || lookup(index(s, relation, 1), e).length > 0;
}

// Everything `start` relates to under the traits, or is related from going backward, without repeats; the scratch flags are clear again on return.
private EntityId* reach(ref Solver s, size_t relation, ecrs.registry.RelationShape shape, EntityId start, bool forward) @trusted {
	auto seen = seenFlags(s);
	EntityId* found = null;
	void visit(EntityId e) {
		if (e < seen.length && !seen[e]) {
			seen[e] = true;
			if (!fp.dynarray.pushBack(found, e)) {
				seen[e] = false;
				fail(s);
			}
		}
	}
	forEachNeighbor(s, relation, shape, start, forward, &visit);
	if (shape.traits & ecrs.registry.RelationTrait.transitive)
		for (size_t i = 0; i < fp.dynarray.length(found); ++i)
			forEachNeighbor(s, relation, shape, found[i], forward, &visit);
	if ((shape.traits & ecrs.registry.RelationTrait.reflexive) && inField(s, relation, shape, start)) visit(start);
	foreach (e; fp.dynarray.slice(found)) seen[e] = false;
	return found;
}

// Calls `fn` with each closure pair agreeing with `a` and `b`, either possibly unbound; with both unbound, walks from every `parts`-th field entity.
private void closure(ref Solver s, size_t relation, ecrs.registry.RelationShape shape, EntityId a, EntityId b, scope TupleFn fn, size_t part = 0, size_t parts = 1) @trusted {
	EntityId[2] pair;
	void walk(EntityId from, bool forward) {
		auto found = reach(s, relation, shape, from, forward);
		scope(exit) fp.dynarray.free(found);
		foreach (e; fp.dynarray.slice(found)) {
			if (s.stopped) return;
			if (forward && b != invalidEntity && e != b) continue;
			pair[0] = forward ? from : e;
			pair[1] = forward ? e : from;
			fn(pair[]);
		}
	}
	if (a != invalidEntity) return walk(a, true);
	if (b != invalidEntity) return walk(b, false);

	EntityId* field = null;
	scope(exit) fp.dynarray.free(field);
	auto seen = seenFlags(s);
	void note(EntityId e) {
		if (e != invalidEntity && e < seen.length && !seen[e]) {
			seen[e] = true;
			if (!fp.dynarray.pushBack(field, e)) {
				seen[e] = false;
				fail(s);
			}
		}
	}
	if (auto storage = ecrs.context.getStorage(*s.ctx, relation))
		foreach (o; ecrs.storage.owners(*storage))
			if (o != invalidEntity)
				forEachTuple(*s.ctx, relation, shape, o, (t) { if (t[1] != invalidEntity) { note(t[0]); note(t[1]); } });
	foreach (e; fp.dynarray.slice(field)) seen[e] = false;
	foreach (i, e; fp.dynarray.slice(field))
		if (i % parts == part) walk(e, true);
}


// Matches an atom whose owner is unbound, through an index or a scan. Outer atoms often rebind the same values, so the last key's tuples are replayed.
private void solveUnowned(ref Solver s, size_t depth, const ref Atom atom, ecrs.registry.RelationShape shape, bool sorted, scope TupleFn match) @trusted {
	const(ecrs.context.Context)* ctx = s.ctx;
	auto memo = &s.memos[depth];
	EntityId[maxArity] key;
	foreach (c; 0 .. atom.arity) key[c] = valueOf(s, atom.args[c]);
	if (memo.calls++ > 0 && memo.key[0 .. atom.arity] == key[0 .. atom.arity]) {
		++memo.repeats;
		if (memo.valid) {
			immutable n = fp.dynarray.length(memo.tuples);
			for (size_t i = 0; i < n && !s.stopped; i += atom.arity) match(memo.tuples[i .. i + atom.arity]);
			return;
		}
	}
	memo.valid = memo.repeats * memoRepeatRatio >= memo.calls;
	memo.key = key;
	if (memo.tuples !is null) fp.dynarray.clear(memo.tuples);
	void record(const(EntityId)[] tuple) {
		if (memo.valid && (fp.dynarray.length(memo.tuples) + tuple.length > memoLimit || !append(memo.tuples, tuple))) memo.valid = false;
		match(tuple);
	}
	scope(exit) memo.valid &= !s.stopped;

	foreach (c; 1 .. atom.arity) {
		if (key[c] == invalidEntity) continue;
		foreach (entry; lookup(index(s, atom.relation, c), key[c]))
			if (sorted && c == 1) forEachTupleStarting(*ctx, atom.relation, shape, entry.owner, key[c], &record);
			else forEachTuple(*ctx, atom.relation, shape, entry.owner, &record);
		return;
	}
	if (auto storage = ecrs.context.getStorage(*ctx, atom.relation))
		foreach (o; ecrs.storage.owners(*storage))
			if (o != invalidEntity)
				forEachTuple(*ctx, atom.relation, shape, o, &record);
}

private void solve(ref Solver s, size_t depth, scope Emit emit) @trusted {
	if (s.stopped) return;
	if (depth == s.plan.length) {
		if (!emit(s.bindings)) s.stopped = true;
		return;
	}
	const atom = &s.body[s.plan[depth]];
	const(ecrs.context.Context)* ctx = s.ctx;
	immutable shape = s.shapes[s.plan[depth]];

	if (atom.negated) {
		EntityId[maxArity] tuple;
		foreach (c; 0 .. atom.arity) tuple[c] = valueOf(s, atom.args[c]);
		bool found = false;
		if (shape.traits) closure(s, atom.relation, shape, tuple[0], tuple[1], (t) { found = true; });
		else found = holds(*ctx, atom.relation, shape, tuple[0 .. atom.arity]);
		if (!found) solve(s, depth + 1, emit);
		return;
	}

	void match(const(EntityId)[] tuple) {
		if (s.stopped) return;
		if (depth == 0 && s.partitions > 1 && !s.presplit && s.candidates++ % s.partitions != s.partition) return;
		size_t[maxArity] boundHere;
		size_t n = 0;
		bool ok = true;
		foreach (c; 0 .. atom.arity) {
			immutable v = tuple[c];
			immutable t = atom.args[c];
			if (v == invalidEntity) { ok = false; break; }
			if (!t.isVar) {
				if (t.constant != v) { ok = false; break; }
			} else if (s.bindings[t.varId] == invalidEntity) {
				s.bindings[t.varId] = v;
				boundHere[n++] = t.varId;
			} else if (s.bindings[t.varId] != v) { ok = false; break; }
		}
		if (ok) solve(s, depth + 1, emit);
		foreach (i; 0 .. n) s.bindings[boundHere[i]] = invalidEntity;
	}

	if (s.plan[depth] == s.deltaAtom) {
		for (size_t i = 0; i + atom.arity <= s.delta.length; i += atom.arity)
			match(s.delta[i .. i + atom.arity]);
		return;
	}

	immutable owner = valueOf(s, atom.args[0]);
	if (shape.traits) {
		immutable target = valueOf(s, atom.args[1]);
		if (depth == 0 && owner == invalidEntity && target == invalidEntity) {
			s.presplit = true;
			scope(exit) s.presplit = false;
			closure(s, atom.relation, shape, owner, target, &match, s.partition, s.partitions);
		} else
			closure(s, atom.relation, shape, owner, target, &match);
		return;
	}
	immutable sorted = s.sorted[s.plan[depth]] && atom.arity > 1;
	immutable first = atom.arity > 1 ? valueOf(s, atom.args[1]) : invalidEntity;
	if (owner != invalidEntity) {
		if (sorted && first != invalidEntity) forEachTupleStarting(*ctx, atom.relation, shape, owner, first, &match);
		else forEachTuple(*ctx, atom.relation, shape, owner, &match);
		return;
	}

	solveUnowned(s, depth, *atom, shape, sorted, &match);
}

// A join order: `first`, then greedily the positive atom with most bound arguments, a bound owner counting most; negations once bound.
private bool makePlan(const(Atom)[] body, size_t first, size_t varCount, ref size_t* plan) @trusted {
	auto bound = cast(bool*) fp.pointer.allocFunction(null, varCount + 1);
	if (bound is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(bound, 0);
	bound[0 .. varCount + 1] = false;
	auto used = cast(bool*) fp.pointer.allocFunction(null, body.length + 1);
	if (used is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(used, 0);
	used[0 .. body.length + 1] = false;

	bool planned = true;
	bool isBound(ecrs.relation.Term t) { return !t.isVar || bound[t.varId]; }
	void take(size_t i) {
		used[i] = true;
		planned = planned && fp.dynarray.pushBack(plan, i);
		foreach (t; body[i].args[0 .. body[i].arity]) if (t.isVar) bound[t.varId] = true;
	}
	void takeReadyNegations() {
		foreach (i, ref a; body) {
			if (used[i] || !a.negated) continue;
			bool ready = true;
			foreach (t; a.args[0 .. a.arity]) ready &= isBound(t);
			if (ready) take(i);
		}
	}

	if (first != fp.pointer.notFound) take(first);
	while (true) {
		takeReadyNegations();
		size_t best = fp.pointer.notFound, bestScore = 0;
		foreach (i, ref a; body) {
			if (used[i] || a.negated) continue;
			size_t score = isBound(a.args[0]) ? 2 * maxArity : 0;
			foreach (t; a.args[1 .. a.arity]) score += isBound(t);
			if (best == fp.pointer.notFound || score > bestScore) { best = i; bestScore = score; }
		}
		if (best == fp.pointer.notFound) break;
		take(best);
	}
	takeReadyNegations();
	assert(!planned || fp.dynarray.length(plan) == body.length);
	return planned;
}

// Solves `body`, calling `emit` with each solution's bindings. False if allocation fails, possibly after some solutions were emitted.
private bool join(ref Program self, ref ecrs.context.Context ctx, const(Atom)[] body, size_t varCount, size_t deltaAtom, const(EntityId)[] delta, scope Emit emit, size_t partition = 0, size_t partitions = 1) @trusted {
	size_t* plan = null;
	scope(exit) fp.dynarray.free(plan);
	if (!makePlan(body, deltaAtom, varCount, plan)) return false;
	auto bindings = cast(EntityId*) fp.pointer.allocFunction(null, (varCount + 1) * EntityId.sizeof);
	if (bindings is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(bindings, 0);
	bindings[0 .. varCount] = invalidEntity;
	auto sorted = cast(bool*) fp.pointer.allocFunction(null, body.length + 1);
	if (sorted is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(sorted, 0);
	foreach (i, ref a; body) sorted[i] = contains(self.derived, a.relation);
	auto shapes = cast(ecrs.registry.RelationShape*) fp.pointer.allocFunction(null, (body.length + 1) * ecrs.registry.RelationShape.sizeof);
	if (shapes is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(shapes, 0);
	foreach (i, ref a; body) shapes[i] = ecrs.registry.lookupRelationShape(a.relation);

	Solver s;
	s.ctx = &ctx;
	s.program = &self;
	s.body = body;
	s.plan = fp.dynarray.slice(plan);
	s.deltaAtom = deltaAtom;
	s.delta = delta;
	s.bindings = bindings[0 .. varCount];
	s.partition = partition;
	s.partitions = partitions;
	s.sorted = sorted[0 .. body.length];
	s.shapes = shapes[0 .. body.length];
	auto memos = cast(Memo*) fp.pointer.allocFunction(null, (body.length + 1) * Memo.sizeof);
	if (memos is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(memos, 0);
	foreach (ref m; memos[0 .. body.length]) m = Memo.init;
	scope(exit) foreach (ref m; memos[0 .. body.length]) fp.dynarray.free(m.tuples);
	s.memos = memos[0 .. body.length];
	scope(exit) cast(void) fp.pointer.allocFunction(s.seen, 0);
	solve(s, 0, emit);
	return !s.failed;
}


private bool upToDate(const ref Program self, const ref ecrs.context.Context ctx) @trusted {
	if (!self.evaluated || self.traitsSeen != ecrs.registry.traitsEpoch()) return false;
	foreach (i, relation; fp.dynarray.slice(self.inputs))
		if (ecrs.context.generation(ctx, relation) != self.snapshot[i]) return false;
	return true;
}

private size_t derivedIndex(const ref Program self, size_t relation) @trusted {
	foreach (i, d; fp.dynarray.slice(self.derived)) if (d == relation) return i;
	return fp.pointer.notFound;
}

// Tarjan over the derived relations, edges running from a rule's head to its body; `order[start[k] .. start[k + 1]]` is component k, dependencies first.
private Status stratify(const ref Program self, ref size_t* order, ref size_t* start) @trusted {
	immutable n = fp.dynarray.length(self.derived);
	auto scratch = cast(size_t*) fp.pointer.allocFunction(null, 3 * (n + 1) * size_t.sizeof);
	if (scratch is null) return Status.outOfMemory;
	scope(exit) cast(void) fp.pointer.allocFunction(scratch, 0);
	auto sccOf = scratch, low = scratch + n + 1, visit = scratch + 2 * (n + 1);
	auto onStack = cast(bool*) fp.pointer.allocFunction(null, n + 1);
	if (onStack is null) return Status.outOfMemory;
	scope(exit) cast(void) fp.pointer.allocFunction(onStack, 0);
	size_t* stack = null;
	scope(exit) fp.dynarray.free(stack);
	foreach (i; 0 .. n) { visit[i] = fp.pointer.notFound; onStack[i] = false; }
	size_t counter = 0, sccCount = 0;
	bool grown = true;

	void connect(size_t v) {
		visit[v] = low[v] = counter++;
		grown = grown && fp.dynarray.pushBack(stack, v);
		if (!grown) return;
		onStack[v] = true;
		foreach (ref r; fp.dynarray.slice(self.rules)) {
			if (derivedIndex(self, r.head.relation) != v) continue;
			foreach (ref a; fp.dynarray.slice(r.body)) {
				immutable w = derivedIndex(self, a.relation);
				if (w == fp.pointer.notFound) continue;
				if (visit[w] == fp.pointer.notFound) {
					connect(w);
					if (!grown) return;
					if (low[w] < low[v]) low[v] = low[w];
				} else if (onStack[w] && visit[w] < low[v])
					low[v] = visit[w];
			}
		}
		if (low[v] != visit[v]) return;
		grown = fp.dynarray.pushBack(start, fp.dynarray.length(order));
		while (grown) {
			immutable w = *fp.dynarray.back(stack);
			cast(void) fp.dynarray.popBack(stack);
			onStack[w] = false;
			sccOf[w] = sccCount;
			grown = fp.dynarray.pushBack(order, w);
			if (w == v) break;
		}
		++sccCount;
	}
	foreach (v; 0 .. n) if (grown && visit[v] == fp.pointer.notFound) connect(v);
	if (!grown || !fp.dynarray.pushBack(start, fp.dynarray.length(order))) return Status.outOfMemory;

	foreach (ref r; fp.dynarray.slice(self.rules))
		foreach (ref a; fp.dynarray.slice(r.body)) {
			immutable w = derivedIndex(self, a.relation);
			if (a.negated && w != fp.pointer.notFound && sccOf[w] == sccOf[derivedIndex(self, r.head.relation)])
				return Status.unstratifiable;
		}
	return Status.ok;
}

// One partition of one rule's join for one round, buffering the head tuples it derives, so tasks share nothing they write.
private struct Task {
	Program* program;
	ecrs.context.Context* ctx;
	const(Rule)* rule;
	size_t deltaAtom;
	const(EntityId)[] delta;
	size_t partition, partitions;
	size_t member; // the head relation's position in the stratum
	EntityId* output = null;
	bool failed = false;
}

private void runTask(void* arg) @trusted {
	auto task = cast(Task*) arg;
	const head = &task.rule.head;
	bool buffered = true;
	// Head tuples reach `output` in batches, sparing each one a dynarray append's checks.
	EntityId[128 * maxArity] pending;
	size_t used = 0;
	immutable joined = join(*task.program, *task.ctx, fp.dynarray.slice(task.rule.body), task.rule.varCount, task.deltaAtom, task.delta, (b) {
		if (used + head.arity > pending.length) {
			buffered = append(task.output, pending[0 .. used]);
			used = 0;
		}
		foreach (c, t; head.args[0 .. head.arity]) pending[used + c] = t.isVar ? b[t.varId] : t.constant;
		used += head.arity;
		return buffered;
	}, task.partition, task.partitions);
	buffered = buffered && append(task.output, pending[0 .. used]);
	task.failed = !joined || !buffered;
}

// Runs `jobs` on `pool`, or inline on this thread if the pool cannot take them.
private void runJobs(bc.threadpool.ThreadPool* pool, bc.threadpool.Job[] jobs) {
	if (bc.threadpool.run(pool, jobs)) return;
	foreach (job; jobs) job.fn(job.arg);
}

// Below this many ids a join or commit is not worth waking the pool: at 512, a 600-round chain closure ran twice as slow.
private enum size_t parallelThreshold = 8192;

// One owner bucket of a parallel commit, so buckets write disjoint entities' lists.
private struct Bucket {
	ecrs.context.Context* ctx;
	size_t relation, arity;
	EntityId* rows = null;
	EntityId* delta = null;
	bool failed = false;
}

private void sortBucket(void* arg) @trusted {
	auto b = cast(Bucket*) arg;
	b.failed = !sortUnique(b.rows, b.arity);
}

private void insertBucket(void* arg) @trusted {
	auto b = cast(Bucket*) arg;
	b.failed = !insertFacts(*b.ctx, b.relation, fp.dynarray.slice(b.rows), b.delta);
}

// `sortUnique` and `insertFacts` across `pool`; owners' lists are created serially between the phases, since only writes to existing components may run concurrently.
private bool insertInParallel(ref ecrs.context.Context ctx, bc.threadpool.ThreadPool* pool, size_t parts, size_t relation, size_t arity, const(Task)* tasks, size_t member, ref EntityId* delta) @trusted {
	auto buckets = fp.dynarray.create!Bucket(parts);
	if (buckets is null) return false;
	scope(exit) {
		foreach (ref b; fp.dynarray.slice(buckets)) { fp.dynarray.free(b.rows); fp.dynarray.free(b.delta); }
		fp.dynarray.free(buckets);
	}
	foreach (ref b; fp.dynarray.slice(buckets)) b = Bucket(&ctx, relation, arity);
	foreach (ref t; fp.dynarray.slice(tasks)) {
		if (t.member != member) continue;
		immutable n = fp.dynarray.length(t.output);
		for (size_t j = 0; j < n; j += arity)
			if (!append(buckets[(t.output[j] * 0x9E3779B1u >> 7) % parts].rows, t.output[j .. j + arity])) return false;
	}

	auto jobs = fp.dynarray.create!(bc.threadpool.Job)(parts);
	if (jobs is null) return false;
	scope(exit) fp.dynarray.free(jobs);
	bool phase(bc.threadpool.JobFunction fn) {
		foreach (k; 0 .. parts) jobs[k] = bc.threadpool.Job(fn, &buckets[k]);
		ecrs.context.enterParallel(ctx);
		runJobs(pool, jobs[0 .. parts]);
		ecrs.context.exitParallel(ctx);
		foreach (ref b; fp.dynarray.slice(buckets)) if (b.failed) return false;
		return true;
	}
	if (!phase(&sortBucket)) return false;
	foreach (ref b; fp.dynarray.slice(buckets))
		for (size_t j = 0; j < fp.dynarray.length(b.rows); j += arity)
			if ((j == 0 || b.rows[j] != b.rows[j - arity]) && ecrs.context.getOrAddComponent(ctx, b.rows[j], relation) is null) return false;
	if (!phase(&insertBucket)) return false;
	foreach (ref b; fp.dynarray.slice(buckets))
		if (!append(delta, fp.dynarray.slice(b.delta))) return false;
	return true;
}

// Semi-naive evaluation of one stratum; each round reads one fixed store, so its joins may run on `pool`. False if allocation fails.
private bool evaluateStratum(ref Program self, ref ecrs.context.Context ctx, const(size_t)[] members, bc.threadpool.ThreadPool* pool) @trusted {
	immutable m = members.length;
	immutable partitions = pool is null ? 1 : bc.threadpool.workerCount(pool);
	auto delta = cast(EntityId**) fp.pointer.allocFunction(null, m * (EntityId*).sizeof);
	if (delta is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(delta, 0);
	foreach (i; 0 .. m) delta[i] = null;
	scope(exit) foreach (i; 0 .. m) fp.dynarray.free(delta[i]);
	Task* tasks = null;
	scope(exit) {
		foreach (ref t; fp.dynarray.slice(tasks)) fp.dynarray.free(t.output);
		fp.dynarray.free(tasks);
	}
	bool failed = false;

	size_t member(size_t relation) {
		immutable d = derivedIndex(self, relation);
		foreach (i, x; members) if (x == d) return i;
		return fp.pointer.notFound;
	}

	bool wide = false; // some task this round is split across the pool
	void schedule(const(Rule)* r, size_t deltaAtom, const(EntityId)[] deltaFacts) {
		immutable split = deltaAtom != fp.pointer.notFound && deltaFacts.length < parallelThreshold ? 1 : partitions;
		wide |= split > 1;
		foreach (p; 0 .. split)
			failed |= !fp.dynarray.pushBack(tasks, Task(&self, &ctx, r, deltaAtom, deltaFacts, p, split, member(r.head.relation)));
	}

	void dispatch() {
		immutable n = fp.dynarray.length(tasks);
		scope(exit) wide = false;
		auto jobs = !wide || n <= 1 ? null : fp.dynarray.create!(bc.threadpool.Job)(n);
		scope(exit) fp.dynarray.free(jobs);
		if (jobs is null) {
			foreach (ref t; fp.dynarray.slice(tasks)) runTask(&t);
		} else {
			foreach (i, ref t; fp.dynarray.slice(tasks)) jobs[i] = bc.threadpool.Job(&runTask, &t);
			ecrs.context.enterParallel(ctx); // a structural change from a join now fails loudly
			runJobs(pool, jobs[0 .. n]);
			ecrs.context.exitParallel(ctx);
		}
		foreach (ref t; fp.dynarray.slice(tasks)) failed |= t.failed;
	}

	bool commit() {
		bool any = false;
		foreach (i; 0 .. m) {
			immutable relation = self.derived[members[i]];
			immutable arity = 1 + ecrs.registry.lookupRelationShape(relation).columns;
			if (delta[i] !is null) fp.dynarray.clear(delta[i]);
			immutable before = ecrs.context.generation(ctx, relation);
			size_t total = 0;
			foreach (ref t; fp.dynarray.slice(tasks))
				if (t.member == i) total += fp.dynarray.length(t.output);
			bool inserted;
			if (partitions > 1 && total >= parallelThreshold && arity > 1)
				inserted = insertInParallel(ctx, pool, partitions, relation, arity, tasks, i, delta[i]);
			else {
				EntityId* rows = null;
				scope(exit) fp.dynarray.free(rows);
				inserted = true;
				foreach (ref t; fp.dynarray.slice(tasks))
					if (t.member == i) inserted = inserted && append(rows, fp.dynarray.slice(t.output));
				inserted = inserted && sortUnique(rows, arity) && insertFacts(ctx, relation, fp.dynarray.slice(rows), delta[i]);
			}
			if (!inserted) {
				failed = true;
				return false;
			}
			extendIndexes(self, ctx, relation, before, delta[i], arity);
			any |= fp.dynarray.length(delta[i]) > 0;
		}
		foreach (ref t; fp.dynarray.slice(tasks)) fp.dynarray.free(t.output);
		if (tasks !is null) fp.dynarray.clear(tasks);
		return any;
	}

	foreach (ref r; fp.dynarray.slice(self.rules))
		if (member(r.head.relation) != fp.pointer.notFound) schedule(&r, fp.pointer.notFound, null);
	if (!failed) dispatch();

	while (!failed && commit()) {
		foreach (ref r; fp.dynarray.slice(self.rules)) {
			if (member(r.head.relation) == fp.pointer.notFound) continue;
			// A closure can pair an old fact with a new one, which no delta shows, so rules reading a grown trait relation rerun fully.
			bool rerun = false;
			foreach (ref a; fp.dynarray.slice(r.body)) {
				immutable k = member(a.relation);
				rerun |= !a.negated && k != fp.pointer.notFound && ecrs.registry.lookupRelationShape(a.relation).traits != 0
					&& fp.dynarray.length(delta[k]) > 0;
			}
			if (rerun) {
				schedule(&r, fp.pointer.notFound, null);
				continue;
			}
			foreach (i, ref a; fp.dynarray.slice(r.body)) {
				immutable k = member(a.relation);
				if (a.negated || k == fp.pointer.notFound || fp.dynarray.length(delta[k]) == 0) continue;
				schedule(&r, i, fp.dynarray.slice(delta[k]));
			}
		}
		if (!failed) dispatch();
	}
	return !failed;
}

/// Brings every relation `self` derives up to date with `ctx`: a no-op if no relation the rules mention, nor any trait, changed since the last call, and otherwise a full recomputation, each round's joins spread over `pool` if one is given. Read results through a `const` context: a mutable access counts as a change, so forces the next call to recompute.
///
/// Returns `Status.unstratifiable`, changing nothing, if the rules recurse through negation, or `Status.outOfMemory` if allocation fails, leaving the derived relations partial until a later call succeeds.
///
/// Examples:
/// ---
/// alias Parent = ecrs.relation.Relation!1;
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// EntityId child = ecrs.context.addEntity(ctx), parent = ecrs.context.addEntity(ctx);
/// ecrs.context.addComponent!Parent(ctx, child).related[0] = parent;
/// Program p;
/// scope(exit) free(p);
/// immutable hasParent = derive(p, "example.hasParent", 0);
/// assert(addRule(p, atom(hasParent, variable(0)), atom(ecrs.registry.componentId!Parent(), variable(0), variable(1))) == Status.ok);
/// assert(evaluate(p, ctx) == Status.ok);
/// assert(ecrs.context.hasComponent(ctx, child, hasParent) && !ecrs.context.hasComponent(ctx, parent, hasParent));
/// ---
Status evaluate(ref Program self, ref ecrs.context.Context ctx, bc.threadpool.ThreadPool* pool = null) @trusted {
	assert(!ecrs.context.inParallel(ctx), "ecrs: Datalog evaluation writes the store; run it outside parallel systems");
	if (upToDate(self, ctx)) return Status.ok;

	size_t* order = null, start = null;
	scope(exit) { fp.dynarray.free(order); fp.dynarray.free(start); }
	if (immutable status = stratify(self, order, start)) return status;

	self.evaluated = false;
	foreach (relation; fp.dynarray.slice(self.derived)) ecrs.context.clearComponent(ctx, relation);
	foreach (k; 0 .. fp.dynarray.length(start) - 1)
		if (!evaluateStratum(self, ctx, order[start[k] .. start[k + 1]], pool)) return Status.outOfMemory;

	foreach (i, relation; fp.dynarray.slice(self.inputs))
		self.snapshot[i] = ecrs.context.generation(ctx, relation);
	self.traitsSeen = ecrs.registry.traitsEpoch();
	self.evaluated = true;
	return Status.ok;
}

/// Evaluates `self`, on `pool` if given, then calls `onMatch` with the bindings, indexed by variable id, of each solution of `body` against `ctx`, until it returns false. A solution may repeat if a base relation lists a tuple twice. `onMatch` runs on the calling thread and must not change the store.
///
/// Returns `Status.invalid` if `body` is malformed, as `addRule` defines it, or what `evaluate` returns if that fails, calling `onMatch` never either way; `Status.outOfMemory` if the join's allocation fails, possibly after some calls.
///
/// Examples:
/// ---
/// alias Parent = ecrs.relation.Relation!1;
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// EntityId child = ecrs.context.addEntity(ctx), parent = ecrs.context.addEntity(ctx);
/// ecrs.context.addComponent!Parent(ctx, child).related[0] = parent;
/// Program p;
/// scope(exit) free(p);
/// EntityId found = invalidEntity;
/// Atom[1] body = [atom(ecrs.registry.componentId!Parent(), constant(child), variable(0))];
/// assert(query(p, ctx, body[], (b) { found = b[0]; return true; }) == Status.ok);
/// assert(found == parent);
/// ---
Status query(ref Program self, ref ecrs.context.Context ctx, const(Atom)[] body, scope Emit onMatch, bc.threadpool.ThreadPool* pool = null) @trusted {
	size_t varCount;
	if (!validBody(body, varCount)) return Status.invalid;
	if (immutable status = evaluate(self, ctx, pool)) return status;
	return join(self, ctx, body, varCount, fp.pointer.notFound, null, onMatch) ? Status.ok : Status.outOfMemory;
}


version(unittest) {
	private alias Parent = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);
	private struct Person {}

	private struct Family {
		ecrs.context.Context ctx;
		EntityId bart, lisa, homer, marge, abraham, jackie;
	}

	private Family makeFamily() {
		Family f;
		f.ctx = ecrs.context.create();
		EntityId*[6] all = [&f.bart, &f.lisa, &f.homer, &f.marge, &f.abraham, &f.jackie];
		foreach (e; all) {
			*e = ecrs.context.addEntity(f.ctx);
			assert(ecrs.context.addComponent!Person(f.ctx, *e) !is null);
		}
		void parents(EntityId child, EntityId[] ps...) {
			foreach (p; ps) assert(fp.dynarray.pushBack(ecrs.context.getOrAddComponent!Parent(f.ctx, child).related, p));
		}
		parents(f.bart, f.homer, f.marge);
		parents(f.lisa, f.homer, f.marge);
		parents(f.homer, f.abraham);
		parents(f.marge, f.jackie);
		return f;
	}

	// The sorted distinct values of variable `var` over the solutions of `body`.
	private EntityId* solutions(ref Program p, ref ecrs.context.Context ctx, size_t var, const(Atom)[] body...) @trusted {
		EntityId* found = null;
		immutable status = query(p, ctx, body, (b) {
			assert(fp.dynarray.pushBack(found, b[var]));
			return true;
		});
		assert(status == Status.ok);
		immutable n = fp.dynarray.length(found);
		if (n == 0) return found;
		std.algorithm.sorting.sort(found[0 .. n]);
		size_t kept = 1;
		foreach (i; 1 .. n) if (found[i] != found[kept - 1]) found[kept++] = found[i];
		cast(void) fp.dynarray.popBackCount(found, n - kept);
		return found;
	}

	private bool sameSet(EntityId* found, const(EntityId)[] expected...) @trusted {
		scope(exit) fp.dynarray.free(found);
		EntityId[16] sorted;
		copy(sorted[0 .. expected.length], expected);
		std.algorithm.sorting.sort(sorted[0 .. expected.length]);
		return fp.dynarray.slice(found) == sorted[0 .. expected.length];
	}

	private size_t count(ref Program p, ref ecrs.context.Context ctx, const(Atom)[] body...) {
		size_t n = 0;
		assert(query(p, ctx, body, (b) { ++n; return true; }) == Status.ok);
		return n;
	}

	// Every fact of a binary relation, packed and sorted, since storage order depends on insertion order, which partitioning changes.
	private ulong* dump(ref Program p, ref ecrs.context.Context ctx, size_t relation, bc.threadpool.ThreadPool* pool) @trusted {
		ulong* out_ = null;
		Atom[1] all = [atom(relation, variable(0), variable(1))];
		assert(query(p, ctx, all[], (b) {
			assert(fp.dynarray.pushBack(out_, (cast(ulong) b[0] << 32) | b[1]));
			return true;
		}, pool) == Status.ok);
		if (out_ !is null) std.algorithm.sorting.sort(fp.dynarray.slice(out_));
		return out_;
	}
}

unittest {
	// Rejections: recursion through negation, unsafe variables, arity mismatches, heads the program does not derive, and a name reused with another shape.
	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);
	Program p;
	scope(exit) free(p);

	immutable person = ecrs.registry.componentId!Person();
	immutable parent = ecrs.registry.componentId!Parent();
	immutable a = p.derive("test.datalog.a", 0);
	immutable b = p.derive("test.datalog.b", 0);
	mixin(createVariables!("x", "y"));

	assert(p.addRule(atom(a, x), atom(person, x), negate(atom(b, x))) == Status.ok);
	assert(p.addRule(atom(b, x), atom(person, x), negate(atom(a, x))) == Status.ok);
	assert(p.evaluate(ctx) == Status.unstratifiable);

	assert(p.addRule(atom(a, y), atom(person, x)) == Status.invalid); // head variable unbound
	assert(p.addRule(atom(a, x), atom(person, x), negate(atom(b, y))) == Status.invalid); // negated variable unbound
	assert(p.addRule(atom(a, x), atom(parent, x)) == Status.invalid); // parent has a column
	assert(p.addRule(atom(person, x), atom(a, x)) == Status.invalid); // base relation as head
	assert(p.addRule(negate(atom(a, x)), atom(person, x)) == Status.invalid);
	assert(p.derive("test.datalog.a", 1) == fp.pointer.notFound);
	assert(p.derive("test.datalog.a", 0) == a);

	// Every allocation addRule makes can fail, leaving the program as it was.
	immutable rules = fp.dynarray.length(p.rules), inputs = fp.dynarray.length(p.inputs);
	immutable c = p.derive("test.datalog.c", 0);
	foreach (n; 0 .. 16) {
		ecrs.registry.failAllocationsAfter(n);
		immutable status = p.addRule(atom(c, x), atom(parent, x, y));
		ecrs.registry.restoreAllocations();
		if (status == Status.ok) break;
		assert(status == Status.outOfMemory);
		assert(fp.dynarray.length(p.rules) == rules && fp.dynarray.length(p.inputs) == inputs);
		assert(fp.dynarray.length(p.snapshot) == inputs);
	}
	assert(fp.dynarray.length(p.rules) == rules + 1);
}

unittest {
	// `sortUnique` agrees with a comparison sort on both sides of `radixThreshold`: narrow ids, ids spanning several bytes, ids needing all 32 bits, and keys all equal.
	enum maxRows = radixThreshold * 8;
	immutable EntityId[4] wide = [0, 1, 1u << 31, invalidEntity];
	foreach (arity; 1 .. 4)
		foreach (n; [radixThreshold - 1, maxRows])
			foreach (kind; 0 .. 4) {
				EntityId* rows = null;
				scope(exit) fp.dynarray.free(rows);
				uint seed = 3;
				foreach (i; 0 .. n * arity) {
					seed = seed * 1103515245 + 12345;
					immutable r = seed >> 8;
					immutable EntityId[4] pick = [7, r % 600, r % 70_000, wide[r % 4]];
					assert(fp.dynarray.pushBack(rows, pick[kind]));
				}
				size_t[maxRows] order;
				foreach (i; 0 .. n) order[i] = i;
				std.algorithm.sorting.sort!((a, b) => lessTuple(rows[a * arity .. a * arity + arity], rows[b * arity .. b * arity + arity]))(order[0 .. n]);
				EntityId[maxRows * 3] expected;
				size_t unique = 0;
				foreach (i; 0 .. n) {
					auto row = rows[order[i] * arity .. order[i] * arity + arity];
					if (unique > 0 && expected[(unique - 1) * arity .. unique * arity] == row) continue;
					copy(expected[unique * arity .. unique * arity + arity], row);
					++unique;
				}

				assert(sortUnique(rows, arity));
				assert(fp.dynarray.slice(rows) == expected[0 .. unique * arity]);
			}
}

unittest {
	// Renumbering reaches the rule constants through `attach`, and derived facts are recomputed under the new ids.
	auto f = makeFamily();
	scope(exit) ecrs.context.free(f.ctx);
	Program p;
	scope(exit) free(p);
	assert(attach(f.ctx, p));

	immutable parent = ecrs.registry.componentId!Parent();
	immutable ofHomer = p.derive("test.datalog.childOfHomer", 0);
	mixin(createVariables!("x"));
	assert(p.addRule(atom(ofHomer, x), atom(parent, x, constant(f.homer))) == Status.ok);
	assert(sameSet(solutions(p, f.ctx, 0, atom(ofHomer, x)), f.bart, f.lisa));

	assert(ecrs.context.swapEntities(f.ctx, f.bart, f.homer));
	assert(sameSet(solutions(p, f.ctx, 0, atom(ofHomer, x)), f.homer, f.lisa));

	assert(detach(f.ctx, p));
	assert(!detach(f.ctx, p));
}

unittest {
	// Transitive closure over a base dynamic relation, queried from either end: a bound owner reads the store directly, a bound target goes through the index.
	auto f = makeFamily();
	scope(exit) ecrs.context.free(f.ctx);
	Program p;
	scope(exit) free(p);

	immutable parent = ecrs.registry.componentId!Parent();
	immutable ancestor = p.derive("test.datalog.ancestor", 1);
	mixin(createVariables!("x", "y", "z"));
	assert(p.addRule(atom(ancestor, x, y), atom(parent, x, y)) == Status.ok);
	assert(p.addRule(atom(ancestor, x, z), atom(parent, x, y), atom(ancestor, y, z)) == Status.ok);

	assert(sameSet(solutions(p, f.ctx, 1, atom(ancestor, constant(f.bart), y)), f.homer, f.marge, f.abraham, f.jackie));
	assert(sameSet(solutions(p, f.ctx, 0, atom(ancestor, x, constant(f.abraham))), f.bart, f.lisa, f.homer));
	assert(sameSet(solutions(p, f.ctx, 0, atom(ancestor, x, constant(f.bart)))));

	// The derived facts are ordinary components.
	assert(ecrs.context.hasComponent(f.ctx, f.bart, ancestor));
	assert(!ecrs.context.hasComponent(f.ctx, f.abraham, ancestor));

	// Incremental: an unchanged store is not re-evaluated; a base change is, and retracts what no longer follows.
	immutable g = ecrs.context.generation(f.ctx, ancestor);
	assert(p.evaluate(f.ctx) == Status.ok);
	assert(ecrs.context.generation(f.ctx, ancestor) == g);

	EntityId adam = ecrs.context.addEntity(f.ctx);
	assert(fp.dynarray.pushBack(ecrs.context.getOrAddComponent!Parent(f.ctx, f.abraham).related, adam));
	assert(sameSet(solutions(p, f.ctx, 1, atom(ancestor, constant(f.lisa), y)), f.homer, f.marge, f.abraham, f.jackie, adam));

	ecrs.context.removeComponent!Parent(f.ctx, f.homer);
	assert(sameSet(solutions(p, f.ctx, 1, atom(ancestor, constant(f.lisa), y)), f.homer, f.marge, f.jackie));

	// Every allocation evaluation makes can fail, reported as such; the next evaluation still derives everything.
	assert(fp.dynarray.pushBack(ecrs.context.getOrAddComponent!Parent(f.ctx, f.homer).related, f.abraham));
	bool evaluated = false;
	foreach (n; 0 .. 1024) {
		ecrs.registry.failAllocationsAfter(n);
		immutable status = p.evaluate(f.ctx);
		ecrs.registry.restoreAllocations();
		if (status == Status.ok) { evaluated = true; break; }
		assert(status == Status.outOfMemory);
	}
	assert(evaluated);
	assert(sameSet(solutions(p, f.ctx, 1, atom(ancestor, constant(f.lisa), y)), f.homer, f.marge, f.abraham, f.jackie, adam));

	// A repeated index key whose tuples outgrow `memoLimit` is looked up afresh each time rather than replayed from a partial memo.
	{
		alias Outer = ecrs.relation.Relation!1;
		auto ctx = ecrs.context.create();
		scope(exit) ecrs.context.free(ctx);
		immutable hub = ecrs.context.addEntity(ctx);
		foreach (i; 0 .. 3) {
			immutable e = ecrs.context.addEntity(ctx);
			assert(e != invalidEntity);
			ecrs.context.addComponent!Outer(ctx, e).related[0] = hub;
		}
		enum owners = memoLimit / 2 + 1;
		foreach (i; 0 .. owners) {
			immutable e = ecrs.context.addEntity(ctx);
			assert(e != invalidEntity && fp.dynarray.pushBack(ecrs.context.getOrAddComponent!Parent(ctx, e).related, hub));
		}
		Program q;
		scope(exit) free(q);
		assert(count(q, ctx, atom(ecrs.registry.componentId!Outer(), x, y), atom(parent, z, y)) == 3 * owners);
	}
}

unittest {
	// Stratified negation over unary relations: a derived tag, and a base tag, `Person`, as the positive guard.
	auto f = makeFamily();
	scope(exit) ecrs.context.free(f.ctx);
	Program p;
	scope(exit) free(p);

	immutable parent = ecrs.registry.componentId!Parent();
	immutable person = ecrs.registry.componentId!Person();
	immutable hasParent = p.derive("test.datalog.hasParent", 0);
	immutable root = p.derive("test.datalog.root", 0);
	mixin(createVariables!("x", "y"));
	assert(p.addRule(atom(hasParent, x), atom(parent, x, y)) == Status.ok);
	assert(p.addRule(atom(root, x), atom(person, x), negate(atom(hasParent, x))) == Status.ok);

	assert(sameSet(solutions(p, f.ctx, 0, atom(root, x)), f.abraham, f.jackie));
	assert(sameSet(solutions(p, f.ctx, 0, atom(person, x), negate(atom(root, x))), f.bart, f.lisa, f.homer, f.marge));
}

unittest {
	// Recursion on both sides over a 40-node chain needs the derived relation's own index, extended each round; plus fixed-arity and 3-ary relations, and empty slots.
	alias Edge = ecrs.relation.Relation!1;
	alias Labelled = ecrs.relation.Relation!2;

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);
	Program p;
	scope(exit) free(p);

	enum n = 40;
	EntityId[n] nodes;
	foreach (i; 0 .. n) nodes[i] = ecrs.context.addEntity(ctx);
	foreach (i; 0 .. n) ecrs.context.addComponent!Edge(ctx, nodes[i]).related[0] = i + 1 < n ? nodes[i + 1] : invalidEntity;
	EntityId label = ecrs.context.addEntity(ctx);
	auto labels = ecrs.context.addComponent!Labelled(ctx, nodes[0]);
	labels.related[0] = nodes[5];
	labels.related[1] = label;

	immutable edge = ecrs.registry.componentId!Edge();
	immutable labelled = ecrs.registry.componentId!Labelled();
	immutable path = p.derive("test.datalog.path", 1);
	immutable tagged = p.derive("test.datalog.tagged", 2);
	mixin(createVariables!("x", "y", "z", "l"));
	assert(p.addRule(atom(path, x, y), atom(edge, x, y)) == Status.ok);
	assert(p.addRule(atom(path, x, z), atom(path, x, y), atom(path, y, z)) == Status.ok);
	assert(p.addRule(atom(tagged, x, z, l), atom(labelled, x, y, l), atom(path, y, z)) == Status.ok);

	assert(count(p, ctx, atom(path, x, y)) == n * (n - 1) / 2);
	assert(count(p, ctx, atom(tagged, constant(nodes[0]), z, constant(label))) == n - 6);

	size_t seen = 0;
	Atom[1] all = [atom(path, x, y)];
	assert(query(p, ctx, all[], (b) { return ++seen < 3; }) == Status.ok); // stops early
	assert(seen == 3);
}

unittest {
	// Transitive and reflexive traits on a base relation, read as closures from either end, with both ends unbound, and under negation.
	alias IsA = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);
	enum unique = 7;
	immutable isA = ecrs.registry.componentId!(IsA, unique)();
	ecrs.registry.setRelationTraits(isA, ecrs.registry.RelationTrait.transitive);
	scope(exit) ecrs.registry.setRelationTraits(isA, 0);

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);
	Program p;
	scope(exit) free(p);

	EntityId animal = ecrs.context.addEntity(ctx), mammal = ecrs.context.addEntity(ctx), cat = ecrs.context.addEntity(ctx),
		dog = ecrs.context.addEntity(ctx), rock = ecrs.context.addEntity(ctx);
	assert(fp.dynarray.pushBack(ecrs.context.addComponent!(IsA, unique)(ctx, mammal).related, animal));
	assert(fp.dynarray.pushBack(ecrs.context.addComponent!(IsA, unique)(ctx, cat).related, mammal));
	assert(fp.dynarray.pushBack(ecrs.context.addComponent!(IsA, unique)(ctx, dog).related, mammal));
	EntityId[5] everything = [animal, mammal, cat, dog, rock];
	foreach (e; everything) assert(ecrs.context.addComponent!Person(ctx, e) !is null);

	immutable person = ecrs.registry.componentId!Person();
	mixin(createVariables!("x", "y"));
	assert(sameSet(solutions(p, ctx, 1, atom(isA, constant(cat), y)), mammal, animal));
	assert(sameSet(solutions(p, ctx, 0, atom(isA, x, constant(animal))), mammal, cat, dog));
	assert(sameSet(solutions(p, ctx, 0, atom(isA, x, y)), mammal, cat, dog)); // every owner
	assert(sameSet(solutions(p, ctx, 0, atom(person, x), negate(atom(isA, x, constant(animal)))), animal, rock));

	// Reflexive adds R(x, x) over the field only: rock never occurs.
	ecrs.registry.setRelationTraits(isA, ecrs.registry.RelationTrait.transitive | ecrs.registry.RelationTrait.reflexive);
	assert(sameSet(solutions(p, ctx, 1, atom(isA, constant(cat), y)), cat, mammal, animal));
	assert(sameSet(solutions(p, ctx, 0, atom(isA, x, x)), animal, mammal, cat, dog));
	assert(sameSet(solutions(p, ctx, 1, atom(isA, constant(rock), y))));
}

unittest {
	// Symmetric: one stored edge answers both ways, and a derived relation over it is re-evaluated when the traits change.
	alias Sibling = ecrs.relation.Relation!1;
	immutable sibling = ecrs.registry.componentId!Sibling();

	auto f = makeFamily();
	scope(exit) ecrs.context.free(f.ctx);
	Program p;
	scope(exit) free(p);
	ecrs.context.addComponent!Sibling(f.ctx, f.bart).related[0] = f.lisa;

	immutable hasSibling = p.derive("test.datalog.hasSibling", 0);
	mixin(createVariables!("x", "y"));
	assert(p.addRule(atom(hasSibling, x), atom(sibling, x, y)) == Status.ok);
	assert(sameSet(solutions(p, f.ctx, 0, atom(hasSibling, x)), f.bart));

	ecrs.registry.setRelationTraits(sibling, ecrs.registry.RelationTrait.symmetric);
	scope(exit) ecrs.registry.setRelationTraits(sibling, 0);
	assert(sameSet(solutions(p, f.ctx, 0, atom(hasSibling, x)), f.bart, f.lisa));
	assert(sameSet(solutions(p, f.ctx, 1, atom(sibling, constant(f.lisa), y)), f.bart));
}

unittest {
	// A transitive derived relation read in its own stratum: 0->4 needs the closure fact 0->3, pairing new 0->2 with old 2->3, which no delta holds.
	alias Edge = ecrs.relation.Relation!1;
	alias Bridge = ecrs.relation.Relation!(1, false);
	enum bridgeUnique = 3;
	static struct Start {}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);
	Program p;
	scope(exit) free(p);

	EntityId[6] n;
	foreach (ref e; n) e = ecrs.context.addEntity(ctx);
	ecrs.context.addComponent!Edge(ctx, n[0]).related[0] = n[1];
	ecrs.context.addComponent!Edge(ctx, n[2]).related[0] = n[3];
	ecrs.context.addComponent!Edge(ctx, n[4]).related[0] = n[5];
	ecrs.context.addComponent!(Bridge, bridgeUnique)(ctx, n[1]).related[0] = n[2];
	ecrs.context.addComponent!(Bridge, bridgeUnique)(ctx, n[3]).related[0] = n[4];
	assert(ecrs.context.addComponent!Start(ctx, n[0]) !is null);

	immutable start = ecrs.registry.componentId!Start();
	immutable edge = ecrs.registry.componentId!Edge();
	immutable bridge = ecrs.registry.componentId!(Bridge, bridgeUnique)();
	immutable conn = p.derive("test.datalog.conn", 1);
	ecrs.registry.setRelationTraits(conn, ecrs.registry.RelationTrait.transitive);
	mixin(createVariables!("x", "y", "z"));
	assert(p.addRule(atom(conn, x, y), atom(edge, x, y)) == Status.ok);
	assert(p.addRule(atom(conn, x, z), atom(start, x), atom(conn, x, y), atom(bridge, y, z)) == Status.ok);

	assert(sameSet(solutions(p, ctx, 1, atom(conn, constant(n[0]), y)), n[1], n[2], n[3], n[4], n[5]));
}

unittest {
	// Parallel evaluation derives exactly what serial evaluation does: reach over a pseudo-random graph with cycles, and a negated stratum, on pools of 1 and 4.
	alias Edge = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);
	enum unique = 11;
	immutable edge = ecrs.registry.componentId!(Edge, unique)();
	immutable person = ecrs.registry.componentId!Person();

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);
	enum n = 400; // wide enough that rounds pass `parallelThreshold`
	EntityId[n] nodes;
	foreach (ref e; nodes) {
		e = ecrs.context.addEntity(ctx);
		assert(ecrs.context.addComponent!Person(ctx, e) !is null);
	}
	uint seed = 12345;
	foreach (i; 0 .. 2 * n) {
		seed = seed * 1103515245 + 12345;
		immutable from = (seed >> 8) % n;
		seed = seed * 1103515245 + 12345;
		immutable to = (seed >> 8) % n;
		assert(fp.dynarray.pushBack(ecrs.context.getOrAddComponent!(Edge, unique)(ctx, nodes[from]).related, nodes[to]));
	}

	ulong*[3] results;
	size_t[3] isolated;
	immutable size_t[3] poolSizes = [0, 1, 4];
	foreach (run, workers; poolSizes) {
		auto pool = workers == 0 ? null : bc.threadpool.create(workers);
		scope(exit) if (pool !is null) bc.threadpool.free(pool);
		Program p;
		scope(exit) free(p);

		mixin(createVariables!("x", "y", "z"));
		immutable reach = p.derive("test.datalog.parallelReach", 1);
		immutable cyclic = p.derive("test.datalog.parallelCyclic", 0);
		immutable acyclic = p.derive("test.datalog.parallelAcyclic", 0);
		assert(p.addRule(atom(reach, x, y), atom(edge, x, y)) == Status.ok);
		assert(p.addRule(atom(reach, x, z), atom(reach, x, y), atom(edge, y, z)) == Status.ok);
		assert(p.addRule(atom(cyclic, x), atom(reach, x, x)) == Status.ok);
		assert(p.addRule(atom(acyclic, x), atom(person, x), negate(atom(cyclic, x))) == Status.ok);
		assert(p.evaluate(ctx, pool) == Status.ok);
		assert(!ecrs.context.inParallel(ctx));

		results[run] = dump(p, ctx, reach, pool);
		Atom[1] q = [atom(acyclic, x)];
		assert(query(p, ctx, q[], (b) { ++isolated[run]; return true; }, pool) == Status.ok);
	}
	scope(exit) foreach (r; results) fp.dynarray.free(r);

	assert(fp.dynarray.length(results[0]) > n); // the graph is not trivial
	assert(fp.dynarray.slice(results[1]) == fp.dynarray.slice(results[0]));
	assert(fp.dynarray.slice(results[2]) == fp.dynarray.slice(results[0]));
	assert(isolated[0] > 0 && isolated[0] < n);
	assert(isolated[1] == isolated[0] && isolated[2] == isolated[0]);
}
