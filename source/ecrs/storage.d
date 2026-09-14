/// Per-component-type contiguous storage (`ComponentStorage`), plus the
/// small compile-time trait helpers (`WithEntity`, `Tag`) components can opt
/// into. Ported from storage.hpp.
///
/// Styled after `fp.dynarray`/`bc.mutex`: `ComponentStorage` is plain data
/// with no methods of its own, and every operation on it is a free function
/// taking it by `ref` - which also means the module-level `@nogc nothrow:`
/// colon-attribute below actually applies to all of them (it does not
/// propagate into struct member functions in D, which is why the previous
/// method-based version had to spell `@nogc nothrow` out on every method).
module ecrs.storage;

import core.stdc.string : memset;

import fp.pointer : allocFunction, notFound;
import fp.dynarray;

import ecrs.registry : componentId;

@nogc nothrow:


alias EntityId = uint;
enum EntityId invalidEntity = 0;

/// `entityComponentIndices[e]` is a dynarray of size_t, one slot per
/// registered component id; `entityComponentIndices[e][id]` is either
/// `ComponentStorage.invalid` or the index of entity `e`'s component inside
/// that component's `ComponentStorage`. Both levels are fp dynarrays.
alias ComponentIndexList = size_t*;
alias EntityComponentIndices = ComponentIndexList*;

/// Grows an entity's per-component index list so slot `componentIdVal`
/// exists, filling any newly-created slots with `ComponentStorage.invalid`.
void ensureIndexSlot(ref ComponentIndexList indices, size_t componentIdVal) @trusted @nogc nothrow {
	immutable oldLen = fp.dynarray.length(indices);
	if (oldLen <= componentIdVal) {
		fp.dynarray.growToSize(indices, componentIdVal + 1);
		foreach (i; oldLen .. componentIdVal + 1)
			indices[i] = ComponentStorage.invalid;
	}
}

/// Finds which entity (if any) has its `componentId`-th slot pointing at `index`.
EntityId getEntity(inout EntityComponentIndices entityComponentIndices, size_t index, size_t componentIdVal) @trusted @nogc nothrow {
	if (entityComponentIndices is null) return invalidEntity;
	immutable n = fp.dynarray.length(cast(EntityComponentIndices) entityComponentIndices);
	foreach (e; 0 .. n) {
		auto indices = (cast(EntityComponentIndices) entityComponentIndices)[e];
		if (fp.dynarray.length(indices) > componentIdVal && indices[componentIdVal] == index)
			return cast(EntityId) e;
	}
	return invalidEntity;
}
template getEntity(Tcomponent, size_t Unique = 0) {
	EntityId getEntity(inout EntityComponentIndices entityComponentIndices, size_t index) @nogc nothrow {
		return .getEntity(entityComponentIndices, index, componentId!(Tcomponent, Unique)());
	}
}


/// Wraps a component value together with the id of the entity that owns it
/// (useful once a component has been reordered/sorted out of entity order).
struct WithEntity(T) {
	T value;
	EntityId entity = invalidEntity;

	alias value this;

	static void swapEntities(ref WithEntity self, ref EntityComponentIndices entityComponentIndices, EntityId a, EntityId b) @nogc nothrow {
		if (self.entity == a) self.entity = b;
		else if (self.entity == b) self.entity = a;
	}
}

template isWithEntity(T) { enum isWithEntity = false; }
template isWithEntity(T : WithEntity!U, U) { enum isWithEntity = true; }

template RemoveWithEntity(T) { alias RemoveWithEntity = T; }
template RemoveWithEntity(T : WithEntity!U, U) { alias RemoveWithEntity = RemoveWithEntity!U; }

/// True if `T` implements the `static void swapEntities(ref T, ref EntityComponentIndices, EntityId, EntityId)` contract.
enum hasSwapEntities(T) = __traits(compiles, {
	T t = T.init;
	EntityComponentIndices idx;
	T.swapEntities(t, idx, EntityId.init, EntityId.init);
});

/// True if `T` implements the `static void finalize(ref T)` contract: a hook
/// for releasing resources a component instance owns itself (e.g. a dynamic
/// `Relation`'s backing dynarray) before its storage slot is discarded or the
/// whole `ComponentStorage` is freed. Storage is otherwise flat, relocatable
/// bytes with no destructor support (see the note on `ComponentStorage`
/// below), so this is the only place such cleanup can hook in.
enum hasFinalize(T) = __traits(compiles, {
	T t = T.init;
	T.finalize(t);
});

private template finalizeThunk(T) {
	void finalizeThunk(void* p) @trusted @nogc nothrow {
		T.finalize(*cast(T*) p);
	}
}

/// Returns the `ComponentStorage.FinalizeFunction` for `T` if it implements the
/// `finalize` contract above, or `null` otherwise (the common case - most
/// components are plain data and own nothing that needs releasing).
template finalizerFor(T) {
	ComponentStorage.FinalizeFunction finalizerFor() @nogc nothrow {
		static if (hasFinalize!T) return &finalizeThunk!T;
		else return null;
	}
}


/// Opt-in marker for zero-sized "tag" components (no per-entity payload).
struct Tag { enum isTag = true; }

template isTag(T) {
	static if (__traits(hasMember, T, "isTag"))
		enum isTag = T.isTag;
	else
		enum isTag = false;
}

template tagValue(T) if (isTag!T) {
	ref T tagValue() @nogc nothrow {
		__gshared T value;
		return value;
	}
}


alias LessFunction = bool function(const(void)* a, const(void)* b) @nogc nothrow;
alias LessWithEntityFunction = bool function(const(void)* a, EntityId ea, const(void)* b, EntityId eb) @nogc nothrow;

template sortByValueLess(T) {
	bool sortByValueLess(const(void)* a, const(void)* b) @trusted @nogc nothrow {
		return *cast(const(T)*) a < *cast(const(T)*) b;
	}
}
private bool monotonicLess(const(void)* a, EntityId ea, const(void)* b, EntityId eb) @trusted @nogc nothrow {
	return ea < eb;
}



/// Contiguous, type-erased backing storage for one component type: a
/// malloc-backed byte dynarray sliced into `elementSize`-sized chunks.
///
/// Deliberately plain data (no constructor, no methods, no disabled postblit,
/// no destructor): `Context` keeps these inside an `fp.dynarray`, which
/// relocates elements via raw `memcpy` on growth rather than via D copy/move
/// semantics, so a C++-style non-copyable/RAII discipline wouldn't actually
/// hold here. Ownership is managed explicitly instead - `free(Context)` is
/// the only code that should ever call `free()` on one of these.
struct ComponentStorage {
	enum size_t invalid = size_t.max;
	enum size_t defaultReservedElementCount = 64;

	alias FinalizeFunction = void function(void* element) @nogc nothrow;

	size_t elementSize = invalid;
	private ubyte* raw = null;
	private FinalizeFunction finalizeFunction = null;
}

ComponentStorage create(size_t elementSize, size_t reservedElementCount = ComponentStorage.defaultReservedElementCount, ComponentStorage.FinalizeFunction finalizeFunction = null) @trusted @nogc nothrow {
	ComponentStorage self;
	self.elementSize = elementSize;
	self.finalizeFunction = finalizeFunction;
	fp.dynarray.reserve(self.raw, reservedElementCount * elementSize);
	return self;
}

size_t size(const ref ComponentStorage self) @trusted @nogc nothrow {
	return self.raw is null || self.elementSize == ComponentStorage.invalid || self.elementSize == 0
		? 0 : fp.dynarray.length(cast(ubyte*) self.raw) / self.elementSize;
}
bool empty(const ref ComponentStorage self) @nogc nothrow { return size(self) == 0; }

/// Runs `self`'s finalizer (if any) on element `i`, then zero-fills its
/// bytes. The zero-fill matters: it makes a later, redundant finalization of
/// the same slot (e.g. `free()` revisiting a slot already finalized by
/// `remove()`/`removeComponent(Context)`) a safe no-op rather than a
/// double-free, since a zeroed `Relation.related` reads back null.
void finalizeElement(ref ComponentStorage self, size_t i) @trusted @nogc nothrow {
	if (self.finalizeFunction is null) return;
	void* p = get(self, i);
	self.finalizeFunction(p);
	memset(p, 0, self.elementSize);
}

void free(ref ComponentStorage self) @trusted @nogc nothrow {
	if (self.raw !is null) {
		if (self.finalizeFunction !is null)
			foreach (i; 0 .. size(self))
				finalizeElement(self, i);
		fp.dynarray.free(self.raw);
	}
	self.elementSize = ComponentStorage.invalid;
}

T* data(T)(ref ComponentStorage self) @trusted @nogc nothrow {
	assert(T.sizeof == self.elementSize);
	return cast(T*) self.raw;
}
const(T)* data(T)(const ref ComponentStorage self) @trusted @nogc nothrow {
	assert(T.sizeof == self.elementSize);
	return cast(const(T)*) self.raw;
}

void* get(ref ComponentStorage self, size_t i) @trusted @nogc nothrow { assert(i < size(self)); return self.raw + i * self.elementSize; }
const(void)* get(const ref ComponentStorage self, size_t i) @trusted @nogc nothrow { assert(i < size(self)); return self.raw + i * self.elementSize; }
ref T get(T)(ref ComponentStorage self, size_t i) @trusted @nogc nothrow { assert(i < size(self)); return data!T(self)[i]; }
ref const(T) get(T)(const ref ComponentStorage self, size_t i) @trusted @nogc nothrow { assert(i < size(self)); return data!T(self)[i]; }

/// Grows storage by `count` zero-filled, type-erased elements.
void allocate(ref ComponentStorage self, size_t count = 1) @trusted @nogc nothrow {
	immutable oldBytes = self.raw is null ? 0 : fp.dynarray.length(self.raw);
	fp.dynarray.grow(self.raw, self.elementSize * count);
	memset(self.raw + oldBytes, 0, self.elementSize * count);
}
/// Grows storage by `count` elements, each set to `T.init` (D's equivalent
/// of the C++ version's placement-new default construction).
void allocate(T)(ref ComponentStorage self, size_t count = 1) @trusted @nogc nothrow {
	assert(T.sizeof == self.elementSize);
	immutable oldCount = size(self);
	fp.dynarray.grow(self.raw, self.elementSize * count);
	T* d = data!T(self);
	foreach (i; 0 .. count)
		d[oldCount + i] = T.init;
}

void* getOrAllocate(ref ComponentStorage self, size_t e) @trusted @nogc nothrow {
	immutable sz = size(self);
	if (sz <= e) allocate(self, e - sz + 1);
	return get(self, e);
}
ref T getOrAllocate(T)(ref ComponentStorage self, size_t e) @trusted @nogc nothrow {
	immutable sz = size(self);
	if (sz <= e) allocate!T(self, e - sz + 1);
	return get!T(self, e);
}

private void swapBytes(ref ComponentStorage self, size_t a, size_t b) @trusted @nogc nothrow {
	assert(a < size(self));
	assert(b < size(self));
	fp.dynarray.swapRange!ubyte(self.raw, a * self.elementSize, b * self.elementSize, self.elementSize);
}

/// Swaps two component slots and keeps `entityComponentIndices` in sync.
/// If `swapIfOneElementless`, one side may be an untracked slot (no owning
/// entity) - used when moving the last element into a freshly freed gap.
bool swap(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, size_t a, size_t b, bool swapIfOneElementless = false) @trusted @nogc nothrow {
	immutable eA = getEntity(entityComponentIndices, a, componentIdVal);
	immutable eB = getEntity(entityComponentIndices, b, componentIdVal);
	if (swapIfOneElementless) {
		if (eA == invalidEntity && eB == invalidEntity) return false;
	} else if (eA == invalidEntity || eB == invalidEntity) return false;

	swapBytes(self, a, b);

	if (swapIfOneElementless && eA == invalidEntity) {
		ensureIndexSlot(entityComponentIndices[eB], componentIdVal);
		entityComponentIndices[eB][componentIdVal] = a;
	} else if (swapIfOneElementless && eB == invalidEntity) {
		ensureIndexSlot(entityComponentIndices[eA], componentIdVal);
		entityComponentIndices[eA][componentIdVal] = b;
	} else {
		immutable tmp = entityComponentIndices[eA][componentIdVal];
		entityComponentIndices[eA][componentIdVal] = entityComponentIndices[eB][componentIdVal];
		entityComponentIndices[eB][componentIdVal] = tmp;
	}
	return true;
}
template swap(Tcomponent, size_t Unique = 0) {
	bool swap(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices, size_t a, size_t b, bool swapIfOneElementless = false) @nogc nothrow {
		return .swap(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, a, b, swapIfOneElementless);
	}
}

/// Removes entity `e`'s component by swapping the last element into its
/// place and popping the back (does not preserve storage order).
bool remove(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, EntityId e) @trusted @nogc nothrow {
	immutable sz = size(self);
	if (sz == 0 || entityComponentIndices is null || e >= fp.dynarray.length(entityComponentIndices))
		return false;

	auto indices = entityComponentIndices[e];
	if (fp.dynarray.length(indices) <= componentIdVal) return false;

	EntityId owner = invalidEntity;
	bool found = false;
	immutable n = fp.dynarray.length(entityComponentIndices);
	foreach (i; 0 .. n)
		if (fp.dynarray.length(entityComponentIndices[i]) > componentIdVal
			&& entityComponentIndices[i][componentIdVal] == sz - 1
		) { owner = cast(EntityId) i; found = true; break; }
	if (!found) return false;

	swapBytes(self, indices[componentIdVal], sz - 1);
	ensureIndexSlot(entityComponentIndices[owner], componentIdVal);

	immutable tmp = indices[componentIdVal];
	indices[componentIdVal] = entityComponentIndices[owner][componentIdVal];
	entityComponentIndices[owner][componentIdVal] = tmp;

	// After the swap, slot `sz - 1` (about to be popped) holds the
	// removed element's original bytes - finalize it before it's gone.
	finalizeElement(self, sz - 1);
	fp.dynarray.popBackCount(self.raw, self.elementSize);
	indices[componentIdVal] = ComponentStorage.invalid;
	return true;
}
template remove(Tcomponent, size_t Unique = 0) {
	bool remove(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices, EntityId e) @nogc nothrow {
		return .remove(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, e);
	}
}

/// Applies a permutation: `order[i]` is the new position of the element
/// currently at index `i`.
void reorder(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, const(size_t)[] order) @trusted @nogc nothrow {
	immutable n = size(self);
	assert(order.length == n);
	if (n <= 1) return;

	size_t* swaps = cast(size_t*) allocFunction(null, n * size_t.sizeof);
	scope(exit) allocFunction(swaps, 0);
	foreach (i; 0 .. n) swaps[order[i]] = i;

	foreach (i; 0 .. n)
		while (swaps[i] != i) {
			swap(self, componentIdVal, entityComponentIndices, swaps[i], i, false);
			immutable t = swaps[swaps[i]]; swaps[swaps[i]] = swaps[i]; swaps[i] = t;
		}
}
template reorder(Tcomponent, size_t Unique = 0) {
	void reorder(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices, const(size_t)[] order) @nogc nothrow {
		.reorder(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, order);
	}
}

/// Sorts by `less(elementPtr(a), elementPtr(b))`, ignoring entity identity.
void sort(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, LessFunction less) @trusted @nogc nothrow {
	import std.algorithm.sorting : stdSort = sort;

	immutable n = size(self);
	if (n <= 1) return;
	size_t* order = cast(size_t*) allocFunction(null, n * size_t.sizeof);
	scope(exit) allocFunction(order, 0);
	foreach (i; 0 .. n) order[i] = i;

	bool cmp(size_t a, size_t b) @trusted @nogc nothrow { return less(get(self, a), get(self, b)); }
	stdSort!cmp(order[0 .. n]);
	reorder(self, componentIdVal, entityComponentIndices, order[0 .. n]);
}
/// Sorts by `less(elementPtr(a), entityOf(a), elementPtr(b), entityOf(b))`.
void sort(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, LessWithEntityFunction less) @trusted @nogc nothrow {
	import std.algorithm.sorting : stdSort = sort;

	immutable n = size(self);
	if (n <= 1) return;
	size_t* order = cast(size_t*) allocFunction(null, n * size_t.sizeof);
	scope(exit) allocFunction(order, 0);
	EntityId* entities = cast(EntityId*) allocFunction(null, n * EntityId.sizeof);
	scope(exit) allocFunction(entities, 0);
	foreach (i; 0 .. n) {
		order[i] = i;
		entities[i] = getEntity(entityComponentIndices, i, componentIdVal);
	}

	bool cmp(size_t a, size_t b) @trusted @nogc nothrow { return less(get(self, a), entities[a], get(self, b), entities[b]); }
	stdSort!cmp(order[0 .. n]);
	reorder(self, componentIdVal, entityComponentIndices, order[0 .. n]);
}
template sortByValue(Tcomponent, size_t Unique = 0) {
	void sortByValue(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices) @nogc nothrow {
		sort(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, &sortByValueLess!Tcomponent);
	}
}
void sortMonotonic(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices) @nogc nothrow {
	sort(self, componentIdVal, entityComponentIndices, &monotonicLess);
}
template sortMonotonic(Tcomponent, size_t Unique = 0) {
	void sortMonotonic(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices) @nogc nothrow {
		sort(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, &.monotonicLess);
	}
}


unittest {
	struct Vec2 { float x = 0, y = 0; }

	// NOTE: componentId!Vec2() is a process-wide id assigned on first use, not
	// necessarily 0 - other modules' unittests may have already registered
	// other types, so the index lists below are sized/filled via
	// ensureIndexSlot() rather than assuming a fixed slot count.
	immutable id = componentId!Vec2();

	ComponentStorage storage = create(Vec2.sizeof);
	scope(exit) free(storage);

	assert(storage.empty());
	storage.allocate!Vec2(3);
	assert(storage.size() == 3);

	storage.get!Vec2(0) = Vec2(1, 1);
	storage.get!Vec2(1) = Vec2(2, 2);
	storage.get!Vec2(2) = Vec2(3, 3);

	// Entity id 0 is reserved as `invalidEntity`, so real entities start at 1
	// - `indices[0]` is left as an empty (unused) placeholder.
	EntityComponentIndices indices = null;
	fp.dynarray.growToSize(indices, 4);
	indices[0] = null;
	foreach (e; 1 .. 4) {
		ComponentIndexList list = null;
		ensureIndexSlot(list, id);
		list[id] = e - 1;
		indices[e] = list;
	}
	scope(exit) {
		foreach (e; 1 .. fp.dynarray.length(indices))
			fp.dynarray.free(indices[e]);
		fp.dynarray.free(indices);
	}

	assert(getEntity(indices, 1, id) == 2);

	storage.remove(id, indices, 2);
	assert(storage.size() == 2);
	// Entity 3's component slid into slot 1.
	assert(getEntity(indices, 1, id) == 3);
	assert(storage.get!Vec2(1) == Vec2(3, 3));
}

unittest {
	// See the note in the previous unittest: componentId!int() is a
	// process-wide id, not necessarily 0.
	immutable id = componentId!int();

	ComponentStorage storage = create(int.sizeof);
	scope(exit) free(storage);

	storage.allocate!int(4);
	storage.get!int(0) = 3;
	storage.get!int(1) = 1;
	storage.get!int(2) = 4;
	storage.get!int(3) = 2;

	// Entity id 0 is reserved as `invalidEntity`, so real entities start at 1
	// - `indices[0]` is left as an empty (unused) placeholder.
	EntityComponentIndices indices = null;
	fp.dynarray.growToSize(indices, 5);
	indices[0] = null;
	foreach (e; 1 .. 5) {
		ComponentIndexList list = null;
		ensureIndexSlot(list, id);
		list[id] = e - 1;
		indices[e] = list;
	}
	scope(exit) {
		foreach (e; 1 .. fp.dynarray.length(indices))
			fp.dynarray.free(indices[e]);
		fp.dynarray.free(indices);
	}

	// entity 1..4 originally owned values 3, 1, 4, 2 respectively (slots e - 1).
	int[5] originalValueOfEntity = [0, 3, 1, 4, 2];

	storage.sortByValue!int(indices);
	assert(storage.get!int(0) == 1);
	assert(storage.get!int(1) == 2);
	assert(storage.get!int(2) == 3);
	assert(storage.get!int(3) == 4);
	// Values moved; the index table must still point each entity at its own
	// (unchanged) value, just at a new slot.
	foreach (e; 1 .. 5)
		assert(*cast(int*) storage.get(indices[e][id]) == originalValueOfEntity[e]);
}

unittest {
	// getEntity(): the not-found path (no entity's index list points at the
	// queried slot).
	EntityComponentIndices emptyIndices = null;
	assert(getEntity(emptyIndices, 0, 0) == invalidEntity);

	immutable id = componentId!float();

	EntityComponentIndices indices = null;
	fp.dynarray.growToSize(indices, 2);
	indices[0] = null;
	ComponentIndexList list = null;
	ensureIndexSlot(list, id);
	list[id] = 0;
	indices[1] = list;
	scope(exit) {
		fp.dynarray.free(indices[1]);
		fp.dynarray.free(indices);
	}
	assert(getEntity(indices, 99, id) == invalidEntity); // nothing points at slot 99
}

unittest {
	// The type-erased (non-template) get/allocate/getOrAllocate overloads,
	// plus the const get() overload.
	immutable id = componentId!double();

	ComponentStorage storage = create(double.sizeof);
	scope(exit) free(storage);

	// remove() on still-empty storage: size() == 0 short-circuits to false.
	EntityComponentIndices noIndices = null;
	assert(!storage.remove(id, noIndices, 0));

	storage.allocate(2); // zero-filled, type-erased
	assert(storage.size() == 2);
	assert(*cast(const(double)*) storage.get(0) == 0);

	auto slot = storage.getOrAllocate(3); // grows past the current size
	assert(storage.size() == 4);
	assert(slot !is null);

	const(ComponentStorage)* constStorage = &storage;
	assert((*constStorage).get(0) !is null); // free-function get() needs an explicit deref through the pointer - it doesn't UFCS off a pointer receiver
}

unittest {
	// swap() with swapIfOneElementless: both untracked -> false; one side
	// untracked on either side -> succeeds and claims the untracked slot.
	immutable id = componentId!short();

	ComponentStorage storage = create(short.sizeof);
	scope(exit) free(storage);
	storage.allocate!short(4);

	EntityComponentIndices indices = null;
	fp.dynarray.growToSize(indices, 3);
	foreach (i; 0 .. 3) indices[i] = null;
	scope(exit) {
		foreach (i; 0 .. fp.dynarray.length(indices))
			if (indices[i] !is null) fp.dynarray.free(indices[i]);
		fp.dynarray.free(indices);
	}

	// Entity 1 tracks slot 0; entity 2 tracks slot 1. Slots 2 and 3 are
	// untracked (no entity's index list points at them).
	ComponentIndexList l1 = null;
	ensureIndexSlot(l1, id);
	l1[id] = 0;
	indices[1] = l1;
	ComponentIndexList l2 = null;
	ensureIndexSlot(l2, id);
	l2[id] = 1;
	indices[2] = l2;

	assert(!storage.swap(id, indices, 2, 3, true)); // both untracked

	assert(storage.swap(id, indices, 0, 2, true)); // a tracked (entity 1), b untracked
	assert(indices[1][id] == 2);

	assert(storage.swap(id, indices, 3, 1, true)); // a untracked, b tracked (entity 2)
	assert(indices[2][id] == 3);
}

unittest {
	// sortMonotonic() (runtime componentId overload) exercises the
	// LessWithEntityFunction overload of sort() and the private monotonicLess().
	immutable id = componentId!short();

	ComponentStorage storage = create(short.sizeof);
	scope(exit) free(storage);

	storage.allocate!short(3);
	storage.get!short(0) = 30;
	storage.get!short(1) = 10;
	storage.get!short(2) = 20;

	EntityComponentIndices indices = null;
	fp.dynarray.growToSize(indices, 4);
	indices[0] = null;
	// Entities 3, 1, 2 own slots 0, 1, 2 respectively - deliberately out of
	// entity-id order, so sortMonotonic() has visible work to do.
	immutable size_t[3] owningEntity = [3, 1, 2];
	foreach (slot; 0 .. 3) {
		ComponentIndexList list = null;
		ensureIndexSlot(list, id);
		list[id] = slot;
		indices[owningEntity[slot]] = list;
	}
	scope(exit) {
		foreach (e; 1 .. fp.dynarray.length(indices))
			fp.dynarray.free(indices[e]);
		fp.dynarray.free(indices);
	}

	storage.sortMonotonic(id, indices);

	assert(getEntity(indices, 0, id) == 1);
	assert(getEntity(indices, 1, id) == 2);
	assert(getEntity(indices, 2, id) == 3);
	assert(storage.get!short(0) == 10); // entity 1's value
	assert(storage.get!short(1) == 20); // entity 2's value
	assert(storage.get!short(2) == 30); // entity 3's value
}
