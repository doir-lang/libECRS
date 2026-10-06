/// Runtime component-type registry: assigns every component type a stable
/// numeric id (per (T, Unique) pair, computed once and cached) and keeps
/// name <-> id <-> size <-> hooks lookup tables for callers that only have a
/// runtime id or name (e.g. scripting/serialization) rather than a
/// compile-time type.
///
/// Thread-safe: lookups share a reader-writer spinlock that registration
/// takes exclusively, and `componentId!T` publishes its cached id with
/// release/acquire ordering, so racing first uses of a type agree on a single
/// id. `freeRegistry` is the exception.
///
/// `EntityId` lives here rather than in `ecrs.storage` because the hook
/// signatures need it and storage imports this module: a cycle would trip
/// druntime's module-constructor check in the `-cov` build.
module ecrs.registry;

import core.atomic : atomicLoad, atomicOp, atomicStore, MemoryOrder;
import core.stdc.string : memcpy;

import fp.pointer : notFound;
import fp.dynarray : growToSize, dynLength = length, dynFreeChar = free;
import fp.fnv1a : fnv1aHash = hash;
import fp.string : stringEqual = equal, stringSlice = slice, makeDynamicSlice;
import fp.hashtable;

import bc.spinlock : SpinLock, readLock, readUnlock, writeLock, writeUnlock;

@nogc nothrow:


alias EntityId = uint;
enum EntityId invalidEntity = 0;

alias FinalizeFunction = void function(void* element) @nogc nothrow;
alias RemapFunction = void function(void* element, const(EntityId)[] remap) @nogc nothrow;

/// Per-type callbacks the store runs on type-erased elements. Recorded at
/// registration, so a component that holds entity ids is renumbered by every
/// `ecrs.context.reorderEntities` without the caller having to name it
/// (`E-Remap`); a holder a caller forgets is the bug this replaces.
struct ComponentHooks {
	FinalizeFunction finalize = null;
	RemapFunction remap = null;
}

/// True if `T` implements `static void finalize(ref T)`: releases resources
/// an instance owns (e.g. a dynamic `Relation`'s dynarray) before its slot is
/// discarded. Storage is flat relocatable bytes with no destructor support,
/// so this is the only place such cleanup can hook in.
enum hasFinalize(T) = __traits(compiles, {
	T t = T.init;
	T.finalize(t);
});

/// True if `T` implements `static void remapEntities(ref T, const(EntityId)[] remap)`:
/// relabels every entity id the value holds, `remap[old]` being the id `old`
/// becomes.
enum hasRemapEntities(T) = __traits(compiles, {
	T t = T.init;
	const(EntityId)[] remap;
	T.remapEntities(t, remap);
});

private template finalizeThunk(T) {
	void finalizeThunk(void* p) @trusted @nogc nothrow { T.finalize(*cast(T*) p); }
}
private template remapThunk(T) {
	void remapThunk(void* p, const(EntityId)[] remap) @trusted @nogc nothrow { T.remapEntities(*cast(T*) p, remap); }
}

template hooksFor(T) {
	ComponentHooks hooksFor() @nogc nothrow {
		ComponentHooks hooks;
		static if (hasFinalize!T) hooks.finalize = &finalizeThunk!T;
		static if (hasRemapEntities!T) hooks.remap = &remapThunk!T;
		return hooks;
	}
}


/// The name is stored as the first field so the custom hash/equal functions
/// below (which only look at the key) can reinterpret the raw entry bytes.
private struct ForwardEntry {
	char* name; // owning: allocated once by registerType, never freed
	size_t id;
}
private struct ReverseEntry {
	size_t id;
	char* name; // non-owning: aliases the same buffer as the matching ForwardEntry
}
private struct SizeEntry {
	size_t id;
	size_t size;
}

private size_t nameHash(inout(ubyte)[] data) @trusted {
	auto e = cast(const(ForwardEntry)*) data.ptr;
	return fnv1aHash(stringSlice(cast(char*) e.name));
}
private bool nameEqual(inout(ubyte)[] a, inout(ubyte)[] b) @trusted {
	auto ea = cast(const(ForwardEntry)*) a.ptr;
	auto eb = cast(const(ForwardEntry)*) b.ptr;
	return stringEqual(cast(char*) ea.name, cast(char*) eb.name);
}

private size_t idHash(inout(ubyte)[] data) @trusted {
	return fnv1aHash(data[0 .. size_t.sizeof]);
}
private bool idEqual(inout(ubyte)[] a, inout(ubyte)[] b) @trusted {
	return a[0 .. size_t.sizeof] == b[0 .. size_t.sizeof];
}


private shared size_t globalComponentId = 0;
// A spinlock rather than `bc.mutex`: that one is heap-allocated by `create`,
// which would itself need a race-free lazy initialization, and registration
// is rare and brief enough that spinning costs nothing.
private __gshared SpinLock registryLock;
private __gshared ForwardEntry* forwardMap = null;
private __gshared ReverseEntry* reverseMap = null;
private __gshared SizeEntry* sizeMap = null;
private __gshared ComponentHooks* hooksTable = null; // dynarray indexed by component id

/// Frees the name buffer an occupied `ForwardEntry` owns - the callback
/// `fp.hashtable.free` invokes per live entry before releasing the table.
private void finalizeForwardEntry(inout(ubyte)[] data) @trusted {
	auto e = cast(ForwardEntry*) data.ptr;
	if (e.name !is null) dynFreeChar(e.name);
}

// NOTE: lazily initialized on first registration, mirroring the C++
// magic-static pattern; callers hold the registry lock exclusively. Lookups,
// which only read, treat a table that does not exist yet as empty.
//
// These operate on the __gshared globals *by reference*, on purpose:
// fp.hashtable's insert functions take `ref T* table` and may reallocate
// and reassign it on growth, so the global itself (not a local copy of it)
// must be passed through every insert/ensure call or the module would be
// left holding a dangling pointer after the first table growth.
private void ensureForwardMap() @trusted {
	if (forwardMap is null) {
		Config config = Config(&nameHash, &nameEqual);
		config.finalizeFunction = &finalizeForwardEntry;
		forwardMap = fp.hashtable.create!ForwardEntry(config);
	}
}
private void ensureReverseMap() @trusted {
	if (reverseMap is null)
		reverseMap = fp.hashtable.create!ReverseEntry(Config(&idHash, &idEqual));
}
private void ensureSizeMap() @trusted {
	if (sizeMap is null)
		sizeMap = fp.hashtable.create!SizeEntry(Config(&idHash, &idEqual));
}

size_t nextComponentId() {
	return atomicOp!"+="(globalComponentId, 1) - 1;
}

/// Registers `name` under `componentId`. A name may be registered once; a
/// second registration is a collision and fails an assert.
size_t registerType(const(char)[] name, size_t componentId, size_t typeSize, ComponentHooks hooks = ComponentHooks.init) @trusted {
	writeLock(registryLock);
	scope(exit) writeUnlock(registryLock);
	return registerTypeLocked(name, componentId, typeSize, hooks);
}

private size_t registerTypeLocked(const(char)[] name, size_t componentId, size_t typeSize, ComponentHooks hooks) @trusted {
	char* owned = makeDynamicSlice(name);

	ensureForwardMap();
	assert(fp.hashtable.find(forwardMap, ForwardEntry(owned, 0)) is null, "ecrs: component name registered twice");
	fp.hashtable.insertAssumeUnique(forwardMap, ForwardEntry(owned, componentId));

	ensureReverseMap();
	fp.hashtable.insertAssumeUnique(reverseMap, ReverseEntry(componentId, owned));

	ensureSizeMap();
	fp.hashtable.insertAssumeUnique(sizeMap, SizeEntry(componentId, typeSize));

	immutable oldLength = dynLength(hooksTable);
	if (oldLength <= componentId) {
		growToSize(hooksTable, componentId + 1);
		foreach (i; oldLength .. componentId + 1) hooksTable[i] = ComponentHooks.init;
	}
	hooksTable[componentId] = hooks;

	return componentId;
}

private template decimal(size_t v) {
	static if (v < 10) enum decimal = "0123456789"[v .. v + 1];
	else enum decimal = decimal!(v / 10) ~ decimal!(v % 10);
}

/// The registered name of component `(T, Unique)`: `T`'s fully qualified
/// name, so two modules' `Flags` stay distinct, with `#Unique` appended for
/// every `Unique` but 0. Stands in for the C++ version's
/// `abi::__cxa_demangle`; D exposes it at compile time, no RTTI needed:
/// the builtin trait, not `std.traits.fullyQualifiedName`, which does not
/// build under `-betterC`.
template componentName(T, size_t Unique = 0) {
	static if (Unique == 0) enum componentName = __traits(fullyQualifiedName, T);
	else enum componentName = __traits(fullyQualifiedName, T) ~ "#" ~ decimal!Unique;
}

template componentId(T, size_t Unique = 0) {
	size_t componentId() @trusted {
		static shared size_t id = notFound;
		immutable cached = atomicLoad!(MemoryOrder.acq)(id);
		if (cached != notFound) return cached;

		writeLock(registryLock);
		scope(exit) writeUnlock(registryLock);
		if (atomicLoad!(MemoryOrder.raw)(id) == notFound)
			atomicStore!(MemoryOrder.rel)(id, registerTypeLocked(componentName!(T, Unique), nextComponentId(), T.sizeof, hooksFor!T()));
		return atomicLoad!(MemoryOrder.raw)(id);
	}
}

template registerComponents(Ts...) {
	void registerComponents() {
		static foreach (T; Ts)
			cast(void) componentId!T();
	}
}

size_t lookupComponentId(const(char)* name) @trusted {
	readLock(registryLock);
	scope(exit) readUnlock(registryLock);
	if (forwardMap is null) return notFound;
	auto found = fp.hashtable.find(forwardMap, ForwardEntry(cast(char*) name, 0));
	return found is null ? notFound : found.id;
}

size_t lookupComponentSize(size_t componentId) @trusted {
	readLock(registryLock);
	scope(exit) readUnlock(registryLock);
	if (sizeMap is null) return notFound;
	auto found = fp.hashtable.find(sizeMap, SizeEntry(componentId, 0));
	return found is null ? notFound : found.size;
}

/// `ComponentHooks.init` (no hooks) for an unknown id.
ComponentHooks lookupComponentHooks(size_t componentId) @trusted {
	readLock(registryLock);
	scope(exit) readUnlock(registryLock);
	return componentId < dynLength(hooksTable) ? hooksTable[componentId] : ComponentHooks.init;
}

/// The returned name lives until `freeRegistry`.
const(char)* lookupComponentName(size_t componentId) @trusted {
	readLock(registryLock);
	scope(exit) readUnlock(registryLock);
	if (reverseMap is null) return null;
	auto found = fp.hashtable.find(reverseMap, ReverseEntry(componentId, null));
	return found is null ? null : found.name;
}

/// Frees every table and cloned name owned by the registry and resets it to
/// its just-loaded state (as if no type had ever been registered).
///
/// NOTE: `componentId!T()` caches each type's id in its own `__gshared`
/// outside these tables, so previously-obtained ids are left dangling by
/// this reset - it's meant for end-of-process cleanup (e.g. so a leak
/// checker sees nothing outstanding), not for reuse while old ids are still
/// in play. Nor is it safe to call while another thread uses the registry.
void freeRegistry() @trusted {
	writeLock(registryLock);
	scope(exit) writeUnlock(registryLock);
	fp.hashtable.free(forwardMap); // also frees each entry's cloned name (finalizeForwardEntry)
	fp.hashtable.free(reverseMap); // names here just alias the forwardMap ones - nothing to own
	fp.hashtable.free(sizeMap);
	dynFreeChar(hooksTable);
	atomicStore(globalComponentId, 0);
}


unittest {
	struct Foo { int x; }
	struct Bar { float y; }

	registerComponents!(Foo, Bar, int)();

	immutable fooId = componentId!Foo();
	immutable barId = componentId!Bar();
	immutable intId = componentId!int();
	assert(fooId != barId);
	assert(barId != intId);

	// Repeated calls for the same type must be stable.
	assert(componentId!Foo() == fooId);

	assert(lookupComponentId(componentName!Foo.ptr) == fooId);
	assert(lookupComponentId(componentName!Bar.ptr) == barId);
	assert(lookupComponentId("int") == intId);
	assert(lookupComponentId("nonexistent") == notFound);

	assert(lookupComponentSize(fooId) == Foo.sizeof);
	assert(lookupComponentSize(barId) == Bar.sizeof);
	assert(lookupComponentSize(notFound) == notFound);

	assert(stringEqual(cast(char*) lookupComponentName(fooId), cast(char*) componentName!Foo.ptr));

	// Unique lets the same type be registered as multiple distinct components,
	// each under a name of its own.
	immutable fooId2 = componentId!(Foo, 1)();
	assert(fooId2 != fooId);
	assert(lookupComponentId((componentName!Foo ~ "#1").ptr) == fooId2);
	static assert(componentName!(Foo, 12) == componentName!Foo ~ "#12");
}

private struct Twin { int x; }

unittest {
	// Names are fully qualified, so two types sharing a short name register as
	// two components. Under `T.stringof` both were "Twin".
	struct Twin { long y; }
	alias Outer = .Twin;
	static assert(componentName!Outer == "ecrs.registry.Twin");
	static assert(componentName!Twin != componentName!Outer);

	immutable outer = componentId!Outer();
	immutable inner = componentId!Twin();
	assert(outer != inner);
	assert(lookupComponentId(componentName!Outer.ptr) == outer);
	assert(lookupComponentId(componentName!Twin.ptr) == inner);
	assert(lookupComponentSize(inner) == long.sizeof);
}

unittest {
	// Racing first uses of one type agree on a single id, and racing first
	// uses of distinct types get distinct ones.
	import bc.threadpool : create, free, run, Job;

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

	auto pool = create(8);
	scope(exit) free(pool);
	Result[jobs] results;
	Job[jobs] work;
	foreach (i; 0 .. jobs) work[i] = Job(&race, &results[i]);
	run(pool, work[]);
	foreach (ref r; results)
		assert(r.same == results[0].same);
	assert(lookupComponentId(componentName!Racer.ptr) == results[0].same);

	static void raceDistinct(void* arg) @nogc nothrow {
		auto r = cast(Result*) arg;
		static foreach (i; 0 .. jobs)
			if (r.distinct == i) { r.distinct = distinctId!i(); return; }
	}
	foreach (i; 0 .. jobs) {
		results[i].distinct = i;
		work[i] = Job(&raceDistinct, &results[i]);
	}
	run(pool, work[]);
	foreach (i; 0 .. jobs)
		foreach (j; i + 1 .. jobs)
			assert(results[i].distinct != results[j].distinct);
}

unittest {
	// componentId!T records T's hooks; plain data gets none.
	struct Owns {
		int* p;
		static void finalize(ref Owns) @nogc nothrow {}
	}
	struct Refers {
		EntityId target;
		static void remapEntities(ref Refers self, const(EntityId)[] remap) @nogc nothrow {
			if (self.target < remap.length) self.target = remap[self.target];
		}
	}
	struct Plain { int x; }

	immutable owns = lookupComponentHooks(componentId!Owns());
	assert(owns.finalize !is null && owns.remap is null);

	immutable refers = lookupComponentHooks(componentId!Refers());
	assert(refers.finalize is null && refers.remap !is null);
	Refers r = Refers(1);
	immutable EntityId[2] remap = [0, 5];
	refers.remap(&r, remap[]);
	assert(r.target == 5);

	immutable plain = lookupComponentHooks(componentId!Plain());
	assert(plain.finalize is null && plain.remap is null);

	assert(lookupComponentHooks(notFound) == ComponentHooks.init);
}

unittest {
	// freeRegistry() tears every table down and resets id assignment - drive
	// it through registerType()/lookup*() directly (rather than
	// componentId!T()) so this doesn't leave other unittests' cached
	// componentId!T() ids dangling.
	immutable id = registerType("FreeRegistryTest", nextComponentId(), 8);
	assert(lookupComponentId("FreeRegistryTest") == id);
	assert(lookupComponentSize(id) == 8);
	assert(stringEqual(cast(char*) lookupComponentName(id), cast(char*) "FreeRegistryTest".ptr));

	freeRegistry();

	assert(lookupComponentId("FreeRegistryTest") == notFound);
	assert(lookupComponentSize(id) == notFound);
	assert(lookupComponentName(id) is null);

	// The registry must still be usable afterwards, starting fresh from id 0.
	immutable id2 = registerType("FreeRegistryTest", nextComponentId(), 4);
	assert(id2 == 0);
	assert(lookupComponentId("FreeRegistryTest") == id2);
	assert(lookupComponentSize(id2) == 4);

	freeRegistry();
}
