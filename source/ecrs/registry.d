/// The runtime component-type registry: gives every component type a stable numeric id, and keeps name, size and hook tables for callers that only have an id or a name, such as scripting or serialization.
///
/// Thread-safe: lookups share a reader-writer spinlock that registration takes exclusively, and `componentId` publishes its cached id with release/acquire ordering, so racing first uses of a type agree on one id. `free` is the exception.
///
/// `EntityId` lives here rather than in `ecrs.storage` because the hook signatures need it and storage imports this module; a cycle would trip druntime's module-constructor check in the `-cov` build.
module ecrs.registry;

import core.atomic : atomicLoad, atomicOp, atomicStore, MemoryOrder;

static import bc.spinlock;
static import core.stdc.string;
static import fp.dynarray;
static import fp.fnv1a;
static import fp.hashtable;
static import fp.lifecycle;
static import fp.pointer;
static import fp.string;

@nogc nothrow:


/// An entity's id: its index in a `Context`'s entity table.
alias EntityId = uint;

/// The id no entity ever has: every `Context` reserves it as entity 0, and a reference to a freed entity becomes it when the context is compacted.
enum EntityId invalidEntity = 0;

/// Relabels every entity id a type-erased component holds, `remap[old]` being the id `old` becomes.
alias RemapFunction = void function(void* element, const(EntityId)[] remap) @nogc nothrow;

/// The callbacks storage runs on one component type's type-erased elements, recorded when the type registers, so storage created from a runtime id still ends lifetimes, and a holder of entity ids is renumbered by every `ecrs.context.reorderEntities` without the caller naming it. A null hook means the type has none.
/// How `ecrs.datalog` reads a component as a relation: the owning entity, then `columns` entity ids at offset 0 of the element. A fixed relation holds one tuple of them, a dynamic one a dynarray of `columns`-wide tuples; with `columns` 0 the component is a unary predicate, present or not.
struct RelationShape {
	size_t columns = 0; /// Entity columns after the owner.
	bool dynamic = false; /// Whether the ids are a dynarray rather than a fixed array.
	uint traits = 0; /// `RelationTrait` flags, set with `setRelationTraits`.
}

/// How queries read a binary relation, one with `columns` 1, leaving its stored facts unchanged. `transitive` reads its closure, `symmetric` every edge both ways, and `reflexive` adds `R(x, x)` for each `x` in the relation's field, the entities occurring in it, so the answer is the same whatever the query binds.
enum RelationTrait : uint {
	transitive = 1, /// Reads the closure.
	symmetric = 2, /// Reads every edge both ways.
	reflexive = 4, /// Relates each entity in the field to itself.
}

/// The callbacks storage runs on one component type's type-erased elements, recorded when the type registers, so storage created from a runtime id still ends lifetimes, and a holder of entity ids is renumbered by every `ecrs.context.reorderEntities` without the caller naming it. A null hook means the type has none.
struct Hooks {
	fp.lifecycle.FinalizeFunction finalizeFunction = null; /// Ends a component's lifetime, as `fp.lifecycle` defines it, before its slot is discarded.
	RemapFunction remapFunction = null; /// Run on a component by every entity renumbering.
	RelationShape shape; /// How `ecrs.datalog` reads the component.
}

/// Whether `T` implements `static void remapEntities(ref T, const(EntityId)[] remap)`, relabelling every entity id an instance holds, `remap[old]` being the id `old` becomes.
///
/// Examples:
/// ---
/// static struct Link { EntityId target; static void remapEntities(ref Link self, const(EntityId)[] remap) @nogc nothrow { self.target = remap[self.target]; } }
/// static assert(hasRemapEntities!Link && !hasRemapEntities!int);
/// ---
enum hasRemapEntities(T) = __traits(compiles, {
	T t = T.init;
	const(EntityId)[] remap;
	T.remapEntities(t, remap);
});

private void remapThunk(T)(void* p, const(EntityId)[] remap) @trusted { T.remapEntities(*cast(T*) p, remap); }

/// The shape of an `ecrs.relation.Relation` whose slots are entities rather than terms, detected structurally because this module cannot import that one. Every other type reads as a unary predicate.
///
/// Examples:
/// ---
/// static struct Pair { enum bool isDynamic = false, canBeTermValue = false; EntityId[2] related; }
/// static assert(shapeFor!Pair == RelationShape(2, false));
/// static assert(shapeFor!int == RelationShape.init);
/// ---
template shapeFor(T) {
	static if (__traits(compiles, T.isDynamic) && __traits(compiles, T.canBeTermValue) && !T.canBeTermValue) {
		static assert(T.related.offsetof == 0);
		static if (T.isDynamic) enum shapeFor = RelationShape(1, true);
		else enum shapeFor = RelationShape(typeof(T.init.related).length, false);
	} else
		enum shapeFor = RelationShape.init;
}

/// The hooks `T` declares: `fp.lifecycle.finalizeFunction!T`, set unless `T`'s lifetime is its bytes, `remapEntities`, as `hasRemapEntities` detects it, and `shapeFor!T`.
///
/// Examples:
/// ---
/// static struct Owner { int* data; void finalize() @nogc nothrow { data = null; } }
/// assert(hooksFor!Owner().finalizeFunction !is null);
/// assert(hooksFor!int() == Hooks.init);
/// ---
Hooks hooksFor(T)() {
	Hooks hooks;
	hooks.finalizeFunction = fp.lifecycle.finalizeFunction!T();
	static if (hasRemapEntities!T) hooks.remapFunction = &remapThunk!T;
	hooks.shape = shapeFor!T;
	return hooks;
}


// The name comes first, so the hash and equality functions, which see only the key, can read it from the raw entry bytes.
private struct ForwardEntry {
	char* name; // owning: freed when the entry is removed or the table freed
	size_t id;
}
private struct ReverseEntry {
	size_t id;
	char* name; // the matching ForwardEntry's buffer
}
private struct SizeEntry {
	size_t id;
	size_t size;
}

// Marks a `lookupId` key, whose name is the caller's C string: `fp.string.slice` would misread the bytes before one as a fat-pointer header.
private enum size_t probeId = fp.pointer.notFound;

private const(char)[] nameOf(const(ForwardEntry)* e) @trusted {
	return e.id == probeId ? e.name[0 .. core.stdc.string.strlen(e.name)] : fp.string.slice(e.name);
}

private size_t nameHash(inout(ubyte)[] data) @trusted {
	return fp.fnv1a.hash(nameOf(cast(const(ForwardEntry)*) data.ptr));
}
private bool nameEqual(inout(ubyte)[] a, inout(ubyte)[] b) @trusted {
	return nameOf(cast(const(ForwardEntry)*) a.ptr) == nameOf(cast(const(ForwardEntry)*) b.ptr);
}

private size_t idHash(inout(ubyte)[] data) @trusted {
	return fp.fnv1a.hash(data[0 .. size_t.sizeof]);
}
private bool idEqual(inout(ubyte)[] a, inout(ubyte)[] b) @trusted {
	return a[0 .. size_t.sizeof] == b[0 .. size_t.sizeof];
}

private void finalizeForwardEntry(inout(ubyte)[] data) @trusted {
	auto e = cast(ForwardEntry*) data.ptr;
	if (e.name !is null) fp.string.free(e.name);
}


private shared size_t idCounter = 0;
// Bumped by `free` so every id `componentId` cached is registered afresh; starting at 1 means a fresh cache never matches.
private shared size_t epoch = 1;
// A spinlock rather than `bc.mutex`, which `create` allocates and so would itself need a race-free lazy initialization.
private __gshared bc.spinlock.SpinLock registryLock;
// fp.hashtable's inserts may reallocate a table, so these globals, never local copies, must be what every insert is handed.
private __gshared ForwardEntry* forwardMap = null;
private __gshared ReverseEntry* reverseMap = null;
private __gshared SizeEntry* sizeMap = null;
private __gshared Hooks* hooksTable = null; // dynarray indexed by component id

// Lookups treat a table that does not exist yet as empty, so the tables are created on first registration.
private bool ensureTables() @trusted {
	if (forwardMap is null) {
		fp.hashtable.Config config = fp.hashtable.Config(&nameHash, &nameEqual);
		config.finalizeFunction = &finalizeForwardEntry;
		forwardMap = fp.hashtable.create!ForwardEntry(config);
	}
	if (reverseMap is null)
		reverseMap = fp.hashtable.create!ReverseEntry(fp.hashtable.Config(&idHash, &idEqual));
	if (sizeMap is null)
		sizeMap = fp.hashtable.create!SizeEntry(fp.hashtable.Config(&idHash, &idEqual));
	return forwardMap !is null && reverseMap !is null && sizeMap !is null;
}

private bool reserveHooks(size_t componentId) @trusted {
	immutable oldLength = fp.dynarray.length(hooksTable);
	if (oldLength > componentId) return true;
	if (fp.dynarray.growToSize(hooksTable, componentId + 1) is null) return false;
	foreach (i; oldLength .. componentId + 1) hooksTable[i] = Hooks.init;
	return true;
}


/// Reserves a fresh component id for `registerType`. Ids are handed out in order from 0, and `free` starts them again.
///
/// Examples:
/// ---
/// immutable a = nextId();
/// assert(nextId() == a + 1);
/// ---
size_t nextId() {
	return atomicOp!"+="(idCounter, 1) - 1;
}

private size_t registerTypeLocked(const(char)[] name, size_t componentId, size_t typeSize, Hooks hooks) @trusted {
	assert(name.length > 0);
	if (!ensureTables() || !reserveHooks(componentId)) return fp.pointer.notFound;
	char* owned = fp.string.makeDynamic(name);
	if (owned is null) return fp.pointer.notFound;

	assert(fp.hashtable.find(forwardMap, ForwardEntry(owned, 0)) is null, "ecrs: component name registered twice");
	if (fp.hashtable.insertAssumeUnique(forwardMap, ForwardEntry(owned, componentId)) is null) {
		fp.string.free(owned);
		return fp.pointer.notFound;
	}
	// From here on, removing the forward entry frees `owned` too.
	if (fp.hashtable.insertAssumeUnique(reverseMap, ReverseEntry(componentId, owned)) is null) {
		fp.hashtable.remove(forwardMap, ForwardEntry(owned, 0));
		return fp.pointer.notFound;
	}
	if (fp.hashtable.insertAssumeUnique(sizeMap, SizeEntry(componentId, typeSize)) is null) {
		fp.hashtable.remove(reverseMap, ReverseEntry(componentId, null));
		fp.hashtable.remove(forwardMap, ForwardEntry(owned, 0));
		return fp.pointer.notFound;
	}
	hooksTable[componentId] = hooks;
	return componentId;
}

/// Registers the non-empty `name` under `componentId`, usually from `nextId`, as a component of `typeSize` bytes with `hooks`. A name may be registered once; registering it again fails an assert.
///
/// Returns `componentId`, or `fp.pointer.notFound` if allocation fails, leaving every lookup as it was.
///
/// Examples:
/// ---
/// immutable id = registerType("RegisterTypeExample", nextId(), 8);
/// assert(id != fp.pointer.notFound);
/// assert(lookupId("RegisterTypeExample") == id);
/// assert(lookupSize(id) == 8);
/// ---
size_t registerType(const(char)[] name, size_t componentId, size_t typeSize, Hooks hooks = Hooks.init) @trusted {
	bc.spinlock.writeLock(registryLock);
	scope(exit) bc.spinlock.writeUnlock(registryLock);
	return registerTypeLocked(name, componentId, typeSize, hooks);
}

private template decimal(size_t v) {
	static if (v < 10) enum decimal = "0123456789"[v .. v + 1];
	else enum decimal = decimal!(v / 10) ~ decimal!(v % 10);
}

/// The registered name of component `(T, unique)`: `T`'s fully qualified name, so two modules' `Flags` stay distinct, with `#unique` appended for every `unique` but 0. It uses the builtin trait because `std.traits.fullyQualifiedName` does not build under `-betterC`.
///
/// Examples:
/// ---
/// static assert(componentName!int == "int");
/// static assert(componentName!(int, 12) == "int#12");
/// ---
template componentName(T, size_t unique = 0) {
	static if (unique == 0) enum componentName = __traits(fullyQualifiedName, T);
	else enum componentName = __traits(fullyQualifiedName, T) ~ "#" ~ decimal!unique;
}

/// The id of component `(T, unique)`, registering it under `componentName!(T, unique)` with `T`'s size and hooks on first use. A nonzero `unique` registers the same type as another, distinct component.
///
/// Returns `fp.pointer.notFound` if registration fails; the next call tries again.
///
/// Examples:
/// ---
/// static struct Position { float x, y; }
/// immutable id = componentId!Position();
/// assert(id != fp.pointer.notFound);
/// assert(componentId!Position() == id);
/// assert(componentId!(Position, 1)() != id);
/// ---
size_t componentId(T, size_t unique = 0)() @trusted {
	static shared size_t id = fp.pointer.notFound;
	static shared size_t cachedEpoch = 0;
	if (atomicLoad!(MemoryOrder.acq)(cachedEpoch) == atomicLoad!(MemoryOrder.acq)(epoch))
		return atomicLoad!(MemoryOrder.raw)(id);

	bc.spinlock.writeLock(registryLock);
	scope(exit) bc.spinlock.writeUnlock(registryLock);
	immutable current = atomicLoad!(MemoryOrder.raw)(epoch);
	if (atomicLoad!(MemoryOrder.raw)(cachedEpoch) != current) {
		immutable registered = registerTypeLocked(componentName!(T, unique), nextId(), T.sizeof, hooksFor!T());
		if (registered == fp.pointer.notFound) return fp.pointer.notFound;
		atomicStore!(MemoryOrder.raw)(id, registered);
		atomicStore!(MemoryOrder.rel)(cachedEpoch, current);
	}
	return atomicLoad!(MemoryOrder.raw)(id);
}

/// Registers each of `Ts`, as `componentId` would on first use. Returns false if any registration fails; the rest are still attempted.
///
/// Examples:
/// ---
/// static struct Health { int points; }
/// assert(register!(Health, float)());
/// assert(lookupId(componentName!Health.ptr) == componentId!Health());
/// ---
bool register(Ts...)() {
	bool registered = true;
	static foreach (T; Ts)
		registered &= componentId!T() != fp.pointer.notFound;
	return registered;
}


/// The id registered under `name`, or `fp.pointer.notFound` if there is none.
///
/// Examples:
/// ---
/// immutable id = componentId!long();
/// assert(lookupId("long") == id);
/// assert(lookupId("LookupComponentIdMissing") == fp.pointer.notFound);
/// ---
size_t lookupId(const(char)* name) @trusted {
	bc.spinlock.readLock(registryLock);
	scope(exit) bc.spinlock.readUnlock(registryLock);
	if (forwardMap is null) return fp.pointer.notFound;
	auto found = fp.hashtable.find(forwardMap, ForwardEntry(cast(char*) name, probeId));
	return found is null ? fp.pointer.notFound : found.id;
}

/// The size in bytes registered for `componentId`, or `fp.pointer.notFound` for an unknown id.
///
/// Examples:
/// ---
/// assert(lookupSize(componentId!short()) == short.sizeof);
/// assert(lookupSize(fp.pointer.notFound) == fp.pointer.notFound);
/// ---
size_t lookupSize(size_t componentId) @trusted {
	bc.spinlock.readLock(registryLock);
	scope(exit) bc.spinlock.readUnlock(registryLock);
	if (sizeMap is null) return fp.pointer.notFound;
	auto found = fp.hashtable.find(sizeMap, SizeEntry(componentId, 0));
	return found is null ? fp.pointer.notFound : found.size;
}

/// The hooks registered for `componentId`, or `Hooks.init`, no hooks, for an unknown id.
///
/// Examples:
/// ---
/// assert(lookupHooks(componentId!ubyte()) == Hooks.init);
/// assert(lookupHooks(fp.pointer.notFound) == Hooks.init);
/// ---
Hooks lookupHooks(size_t componentId) @trusted {
	bc.spinlock.readLock(registryLock);
	scope(exit) bc.spinlock.readUnlock(registryLock);
	return componentId < fp.dynarray.length(hooksTable) ? hooksTable[componentId] : Hooks.init;
}

/// The relation shape registered for `componentId`, or `RelationShape.init`, a unary predicate, for an unknown id.
///
/// Examples:
/// ---
/// static struct Next { enum bool isDynamic = false, canBeTermValue = false; EntityId[1] related; }
/// assert(lookupRelationShape(componentId!Next()) == RelationShape(1, false));
/// assert(lookupRelationShape(fp.pointer.notFound) == RelationShape.init);
/// ---
RelationShape lookupRelationShape(size_t componentId) {
	return lookupHooks(componentId).shape;
}

private shared size_t traitChanges = 0;

/// Replaces the `RelationTrait` flags of the registered binary relation `componentId`, and advances `traitsEpoch`, since every cached answer over it is now stale. It cannot fail.
///
/// Examples:
/// ---
/// static struct Above { enum bool isDynamic = false, canBeTermValue = false; EntityId[1] related; }
/// immutable id = componentId!Above();
/// setRelationTraits(id, RelationTrait.transitive);
/// assert(lookupRelationShape(id).traits == RelationTrait.transitive);
/// setRelationTraits(id, 0);
/// ---
void setRelationTraits(size_t componentId, uint traits) @trusted {
	bc.spinlock.writeLock(registryLock);
	scope(exit) bc.spinlock.writeUnlock(registryLock);
	assert(componentId < fp.dynarray.length(hooksTable), "ecrs: traits on an unregistered component");
	assert(traits == 0 || hooksTable[componentId].shape.columns == 1, "ecrs: traits need a binary relation");
	hooksTable[componentId].shape.traits = traits;
	atomicOp!"+="(traitChanges, 1);
}

/// A counter every `setRelationTraits` advances.
///
/// Examples:
/// ---
/// static struct Near { enum bool isDynamic = false, canBeTermValue = false; EntityId[1] related; }
/// immutable before = traitsEpoch();
/// setRelationTraits(componentId!Near(), 0);
/// assert(traitsEpoch() == before + 1);
/// ---
size_t traitsEpoch() { return atomicLoad(traitChanges); }

/// The name registered for `componentId`, which lives until `free`, or null for an unknown id.
///
/// Examples:
/// ---
/// assert(fp.string.equal(lookupName(componentId!byte()), "byte"));
/// assert(lookupName(fp.pointer.notFound) is null);
/// ---
const(char)* lookupName(size_t componentId) @trusted {
	bc.spinlock.readLock(registryLock);
	scope(exit) bc.spinlock.readUnlock(registryLock);
	if (reverseMap is null) return null;
	auto found = fp.hashtable.find(reverseMap, ReverseEntry(componentId, null));
	return found is null ? null : found.name;
}


/// Frees every table and name the registry owns and resets it as though no type had registered, so a leak checker run at exit sees nothing outstanding. Every id handed out before is forgotten: `componentId` registers its type afresh on next use, so free every `Context` first, since their storages are indexed by the old ids. It is not safe to call while another thread uses the registry.
///
/// Examples:
/// ---
/// immutable before = componentId!dchar();
/// free();
/// assert(lookupSize(before) == fp.pointer.notFound);
/// assert(componentId!dchar() == 0);
/// ---
void free() @trusted {
	bc.spinlock.writeLock(registryLock);
	scope(exit) bc.spinlock.writeUnlock(registryLock);
	fp.hashtable.free(forwardMap); // frees the names, which reverseMap only aliases
	fp.hashtable.free(reverseMap);
	fp.hashtable.free(sizeMap);
	fp.dynarray.free(hooksTable);
	atomicStore(idCounter, 0);
	atomicOp!"+="(epoch, 1);
}


version(unittest) {
	private struct Twin { int x; }

	private fp.pointer.AllocFunction underlyingAlloc = null;
	private size_t allocationsLeft;

	private void* failingAlloc(void* p, size_t size) {
		if (size != 0) {
			if (allocationsLeft == 0) return null;
			--allocationsLeft;
		}
		return underlyingAlloc(p, size);
	}

	// Makes the calling thread's libfp allocations fail once `n` more have succeeded, until `restoreAllocations`; freeing still works.
	package void failAllocationsAfter(size_t n) @trusted {
		if (underlyingAlloc is null) {
			underlyingAlloc = fp.pointer.allocFunction;
			fp.pointer.allocFunction = &failingAlloc;
		}
		allocationsLeft = n;
	}

	// Undoes `failAllocationsAfter`.
	package void restoreAllocations() @trusted {
		if (underlyingAlloc is null) return;
		fp.pointer.allocFunction = underlyingAlloc;
		underlyingAlloc = null;
	}
}

unittest {
	// componentId records each type's hooks; plain data gets none.
	static struct Owns {
		int* p;
		void finalize() @nogc nothrow { p = null; }
	}
	static struct Refers {
		EntityId target;
		static void remapEntities(ref Refers self, const(EntityId)[] remap) @nogc nothrow {
			if (self.target < remap.length) self.target = remap[self.target];
		}
	}
	static struct Plain { int x; }

	immutable owns = lookupHooks(componentId!Owns());
	assert(owns.finalizeFunction !is null && owns.remapFunction is null);
	Owns o = Owns(cast(int*) 1);
	owns.finalizeFunction(cast(inout(ubyte)[]) (cast(ubyte*) &o)[0 .. Owns.sizeof]);
	assert(o.p is null);

	immutable refers = lookupHooks(componentId!Refers());
	assert(refers.finalizeFunction is null && refers.remapFunction !is null);
	Refers r = Refers(1);
	immutable EntityId[2] remap = [0, 5];
	refers.remapFunction(&r, remap[]);
	assert(r.target == 5);

	immutable plain = lookupHooks(componentId!Plain());
	assert(plain.finalizeFunction is null && plain.remapFunction is null);

	assert(lookupHooks(fp.pointer.notFound) == Hooks.init);
}

unittest {
	// Registration and lookup by name, size and id.
	struct Foo { int x; }
	struct Bar { float y; }

	assert(register!(Foo, Bar, int)());

	immutable fooId = componentId!Foo();
	immutable barId = componentId!Bar();
	immutable intId = componentId!int();
	assert(fooId != barId);
	assert(barId != intId);
	assert(componentId!Foo() == fooId);

	assert(lookupId(componentName!Foo.ptr) == fooId);
	assert(lookupId(componentName!Bar.ptr) == barId);
	assert(lookupId("int") == intId);
	assert(lookupId("nonexistent") == fp.pointer.notFound);
	// A C string preceded by bytes that look like a fat-pointer header, as a `malloc` block can be, is still read to its terminator.
	{
		ubyte[fp.pointer.Header.sizeof + 4] buffer;
		*cast(fp.pointer.Header*) buffer.ptr = fp.pointer.Header(fp.pointer.PointerType.heap, 1);
		buffer[fp.pointer.Header.sizeof .. $] = cast(const(ubyte)[]) "int\0";
		assert(lookupId(cast(char*) buffer.ptr + fp.pointer.Header.sizeof) == intId);
	}

	assert(lookupSize(fooId) == Foo.sizeof);
	assert(lookupSize(barId) == Bar.sizeof);
	assert(lookupSize(fp.pointer.notFound) == fp.pointer.notFound);

	assert(fp.string.equal(cast(char*) lookupName(fooId), cast(char*) componentName!Foo.ptr));

	immutable fooId2 = componentId!(Foo, 1)();
	assert(fooId2 != fooId);
	assert(lookupId((componentName!Foo ~ "#1").ptr) == fooId2);
	static assert(componentName!(Foo, 12) == componentName!Foo ~ "#12");

	// Names are fully qualified, so two types sharing a short name register as two components.
	struct Twin { long y; }
	alias Outer = .Twin;
	static assert(componentName!Outer == "ecrs.registry.Twin");
	static assert(componentName!Twin != componentName!Outer);
	immutable outer = componentId!Outer();
	immutable inner = componentId!Twin();
	assert(outer != inner);
	assert(lookupId(componentName!Outer.ptr) == outer);
	assert(lookupId(componentName!Twin.ptr) == inner);
	assert(lookupSize(inner) == long.sizeof);
}

unittest {
	// Traits ride on the relation's shape, and each change advances the epoch; `Binary` stands in for `ecrs.relation.Relation!1`.
	static struct Binary {
		enum bool isDynamic = false, canBeTermValue = false;
		EntityId[1] related;
	}
	immutable id = componentId!Binary();
	assert(lookupRelationShape(id) == RelationShape(1, false));

	immutable epoch = traitsEpoch();
	setRelationTraits(id, RelationTrait.transitive | RelationTrait.reflexive);
	assert(lookupRelationShape(id).traits == (RelationTrait.transitive | RelationTrait.reflexive));
	assert(traitsEpoch() == epoch + 1);
	setRelationTraits(id, 0);
	assert(lookupRelationShape(id).traits == 0);
}

unittest {
	// Racing first uses of one type agree on a single id, and racing first uses of distinct types get distinct ones.
	static import bc.threadpool;
	static struct Racer { int x; }
	static struct Result { size_t same, distinct; }
	static size_t distinctId(size_t i)() @nogc nothrow {
		static struct Distinct { int x; }
		return componentId!(Distinct, i)();
	}
	static void race(void* arg) @nogc nothrow {
		auto r = cast(Result*) arg;
		r.same = componentId!Racer();
	}
	enum jobs = 16;

	auto pool = bc.threadpool.create(8);
	assert(pool !is null);
	scope(exit) bc.threadpool.free(pool);
	Result[jobs] results;
	bc.threadpool.Job[jobs] work;
	foreach (i; 0 .. jobs) work[i] = bc.threadpool.Job(&race, &results[i]);
	assert(bc.threadpool.run(pool, work[]));
	foreach (ref r; results)
		assert(r.same == results[0].same);
	assert(lookupId(componentName!Racer.ptr) == results[0].same);

	static void raceDistinct(void* arg) @nogc nothrow {
		auto r = cast(Result*) arg;
		static foreach (i; 0 .. jobs)
			if (r.distinct == i) { r.distinct = distinctId!i(); return; }
	}
	foreach (i; 0 .. jobs) {
		results[i].distinct = i;
		work[i] = bc.threadpool.Job(&raceDistinct, &results[i]);
	}
	assert(bc.threadpool.run(pool, work[]));
	foreach (i; 0 .. jobs)
		foreach (j; i + 1 .. jobs)
			assert(results[i].distinct != results[j].distinct);
}

unittest {
	// free tears every table down and restarts ids, and cached ids register afresh.
	static struct Cached { int x; }
	immutable cached = componentId!Cached();
	immutable id = registerType("FreeRegistryTest", nextId(), 8);
	assert(lookupId("FreeRegistryTest") == id);
	assert(lookupSize(id) == 8);

	free();

	assert(lookupId("FreeRegistryTest") == fp.pointer.notFound);
	assert(lookupSize(id) == fp.pointer.notFound);
	assert(lookupName(id) is null);
	assert(lookupName(cached) is null);

	immutable id2 = registerType("FreeRegistryTest", nextId(), 4);
	assert(id2 == 0);
	assert(lookupId("FreeRegistryTest") == id2);
	assert(lookupSize(id2) == 4);
	immutable recached = componentId!Cached();
	assert(recached == 1);
	assert(lookupId(componentName!Cached.ptr) == recached);

	// With the tables gone, every allocation registration makes can fail; each failure leaves no trace.
	free();
	static struct Fragile { int x; }
	bool registered = false;
	foreach (n; 0 .. 64) {
		failAllocationsAfter(n);
		immutable fragile = componentId!Fragile();
		restoreAllocations();
		if (fragile == fp.pointer.notFound) {
			assert(lookupId(componentName!Fragile.ptr) == fp.pointer.notFound);
			continue;
		}
		assert(lookupId(componentName!Fragile.ptr) == fragile);
		assert(lookupSize(fragile) == Fragile.sizeof);
		registered = true;
		break;
	}
	assert(registered);

	// Registering enough names grows the tables, so the sweep also fails each insert in turn, which must roll back the earlier ones.
	static foreach (k; 0 .. 32) {{
		enum name = "Fragile" ~ decimal!k;
		bool grown = false;
		foreach (n; 0 .. 64) {
			failAllocationsAfter(n);
			immutable grownId = registerType(name, nextId(), 4);
			restoreAllocations();
			if (grownId == fp.pointer.notFound) {
				assert(lookupId(name.ptr) == fp.pointer.notFound);
				continue;
			}
			assert(lookupId(name.ptr) == grownId && lookupSize(grownId) == 4);
			assert(fp.string.equal(lookupName(grownId), name));
			grown = true;
			break;
		}
		assert(grown);
	}}
	free();
}
