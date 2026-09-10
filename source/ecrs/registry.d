/// Runtime component-type registry: assigns every component type a stable
/// numeric id (per (T, Unique) pair, computed once and cached) and keeps
/// name <-> id <-> size lookup tables for callers that only have a runtime
/// name (e.g. scripting/serialization) rather than a compile-time type.
module ecrs.registry;

import core.stdc.string : memcpy;

import fp.pointer : notFound;
import fp.dynarray : growToSize, dynFreeChar = free;
import fp.fnv1a : fnv1aHash = hash;
import fp.string : stringEqual = equal, stringSlice = slice, makeDynamicSlice;
import fp.hashtable;

@nogc nothrow:


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


private __gshared size_t globalComponentId = 0;
private __gshared ForwardEntry* forwardMap = null;
private __gshared ReverseEntry* reverseMap = null;
private __gshared SizeEntry* sizeMap = null;

/// Frees the name buffer an occupied `ForwardEntry` owns - the callback
/// `fp.hashtable.free` invokes per live entry before releasing the table.
private void finalizeForwardEntry(inout(ubyte)[] data) @trusted {
	auto e = cast(ForwardEntry*) data.ptr;
	if (e.name !is null) dynFreeChar(e.name);
}

// NOTE: lazily initialized on first use, mirroring the C++ magic-static
// pattern. Not thread-safe against a racing first call from two threads -
// callers that register components from multiple threads must arrange
// their own synchronization around the first registration.
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
	return globalComponentId++;
}

size_t registerType(const(char)[] name, size_t componentId, size_t typeSize) @trusted {
	char* owned = makeDynamicSlice(name);

	ensureForwardMap();
	fp.hashtable.insertAssumeUnique(forwardMap, ForwardEntry(owned, componentId));

	ensureReverseMap();
	fp.hashtable.insertAssumeUnique(reverseMap, ReverseEntry(componentId, owned));

	ensureSizeMap();
	fp.hashtable.insertAssumeUnique(sizeMap, SizeEntry(componentId, typeSize));

	return componentId;
}

/// `T.stringof` doubles as the demangled type name the C++ version got via
/// `abi::__cxa_demangle` - D exposes it directly at compile time, no RTTI needed.
template componentId(T, size_t Unique = 0) {
	size_t componentId() @trusted {
		__gshared size_t id = notFound;
		if (id == notFound)
			id = registerType(T.stringof, nextComponentId(), T.sizeof);
		return id;
	}
}

template registerComponents(Ts...) {
	void registerComponents() {
		static foreach (T; Ts)
			cast(void) componentId!T();
	}
}

size_t lookupComponentId(const(char)* name) @trusted {
	ensureForwardMap();
	auto found = fp.hashtable.find(forwardMap, ForwardEntry(cast(char*) name, 0));
	return found is null ? notFound : found.id;
}

size_t lookupComponentSize(size_t componentId) @trusted {
	ensureSizeMap();
	auto found = fp.hashtable.find(sizeMap, SizeEntry(componentId, 0));
	return found is null ? notFound : found.size;
}

const(char)* lookupComponentName(size_t componentId) @trusted {
	ensureReverseMap();
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
/// in play.
void freeRegistry() @trusted {
	if (forwardMap !is null) fp.hashtable.free(forwardMap); // also frees each entry's cloned name (finalizeForwardEntry)
	if (reverseMap !is null) fp.hashtable.free(reverseMap); // names here just alias the forwardMap ones - nothing to own
	if (sizeMap !is null) fp.hashtable.free(sizeMap);
	globalComponentId = 0;
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

	assert(lookupComponentId("Foo") == fooId);
	assert(lookupComponentId("Bar") == barId);
	assert(lookupComponentId("int") == intId);
	assert(lookupComponentId("nonexistent") == notFound);

	assert(lookupComponentSize(fooId) == Foo.sizeof);
	assert(lookupComponentSize(barId) == Bar.sizeof);
	assert(lookupComponentSize(notFound) == notFound);

	assert(stringEqual(cast(char*) lookupComponentName(fooId), cast(char*) "Foo".ptr));

	// Unique lets the same type be registered as multiple distinct components.
	immutable fooId2 = componentId!(Foo, 1)();
	assert(fooId2 != fooId);
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
