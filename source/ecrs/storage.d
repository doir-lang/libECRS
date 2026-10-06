/// Per-component-type storage (`ComponentStorage`), plus the small
/// compile-time trait helpers (`Tag`) components can opt into. Ported from
/// storage.hpp.
///
/// Element bytes live in an `fp.pagedarray`, so a component's address never
/// changes while it exists: a query may hold a `ref` to one while nested
/// queries add more. Each slot also records its owning entity, so slot ->
/// entity is O(1). Removal leaves a hole for the next add to reuse rather than
/// moving another component into the gap; only `reorder` and the sorts move
/// components, and they also trim trailing holes.
///
/// Styled after `fp.dynarray`/`bc.mutex`: `ComponentStorage` is plain data
/// with no methods of its own, and every operation on it is a free function
/// taking it by `ref` - which also puts them all under the module-level
/// `@nogc nothrow:` below, since that does not reach into a struct body.
module ecrs.storage;

import core.stdc.string : memset;

import fp.pointer : allocFunction;
static import fp.dynarray;
static import fp.pagedarray;

public import ecrs.registry : EntityId, invalidEntity, FinalizeFunction, RemapFunction, hasFinalize, hasRemapEntities;
import ecrs.registry : componentId;

@nogc nothrow:


/// `entityComponentIndices[e]` is a dynarray of size_t, one slot per
/// registered component id; `entityComponentIndices[e][id]` is either
/// `ComponentStorage.invalid` or the index of entity `e`'s component inside
/// that component's `ComponentStorage`. Both levels are fp dynarrays.
alias ComponentIndexList = size_t*;
alias EntityComponentIndices = ComponentIndexList*;

/// Grows an entity's per-component index list so slot `componentIdVal`
/// exists, filling any newly-created slots with `ComponentStorage.invalid`.
void ensureIndexSlot(ref ComponentIndexList indices, size_t componentIdVal) @trusted {
	immutable oldLen = fp.dynarray.length(indices);
	if (oldLen <= componentIdVal) {
		fp.dynarray.growToSize(indices, componentIdVal + 1);
		foreach (i; oldLen .. componentIdVal + 1)
			indices[i] = ComponentStorage.invalid;
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
private bool monotonicLess(const(void)* a, EntityId ea, const(void)* b, EntityId eb) @trusted {
	return ea < eb;
}


/// Type-erased backing storage for one component type.
///
/// Deliberately plain data (no constructor, no methods, no disabled postblit,
/// no destructor): `Context` keeps these inside an `fp.dynarray`, which
/// relocates elements via raw `memcpy` on growth rather than via D copy/move
/// semantics. Relocating this struct never moves the components themselves,
/// which sit in pages it points to. `free(Context)` is the only code that
/// should ever call `free()` on one of these.
struct ComponentStorage {
	enum size_t invalid = size_t.max;

	size_t elementSize = invalid;
	private fp.pagedarray.PagedArray elements;
	private EntityId* slotOwners = null; // parallel to `elements`; invalidEntity marks a hole
	private size_t* holes = null; // hole slots, reused before `elements` grows
	private FinalizeFunction finalizeFunction = null;
	private RemapFunction remapFunction = null;
}

ComponentStorage create(size_t elementSize, FinalizeFunction finalizeFunction = null, RemapFunction remapFunction = null) {
	ComponentStorage self;
	self.elementSize = elementSize;
	self.elements = fp.pagedarray.create(elementSize);
	self.finalizeFunction = finalizeFunction;
	self.remapFunction = remapFunction;
	return self;
}

void free(ref ComponentStorage self) @trusted {
	foreach (slot; 0 .. size(self))
		if (self.slotOwners[slot] != invalidEntity)
			finalizeElement(self, slot);
	fp.pagedarray.free(self.elements);
	fp.dynarray.free(self.slotOwners);
	fp.dynarray.free(self.holes);
	self.elementSize = ComponentStorage.invalid;
}

/// Slots in use, holes included; valid indices are `0 .. size`.
size_t size(const ref ComponentStorage self) @trusted {
	return fp.dynarray.length(cast(EntityId*) self.slotOwners);
}
/// Slots holding a component.
size_t liveCount(const ref ComponentStorage self) @trusted {
	return size(self) - fp.dynarray.length(cast(size_t*) self.holes);
}
bool empty(const ref ComponentStorage self) { return liveCount(self) == 0; }

/// Each slot's owner, `invalidEntity` for a hole: the dense list of entities
/// that have this component.
const(EntityId)[] owners(const ref ComponentStorage self) @trusted {
	return self.slotOwners[0 .. size(self)];
}
EntityId getEntity(const ref ComponentStorage self, size_t slot) @trusted {
	assert(slot < size(self));
	return self.slotOwners[slot];
}

void* get(ref ComponentStorage self, size_t i) { return fp.pagedarray.get(self.elements, i); }
const(void)* get(const ref ComponentStorage self, size_t i) { return fp.pagedarray.get(self.elements, i); }
ref T get(T)(ref ComponentStorage self, size_t i) @trusted {
	assert(T.sizeof == self.elementSize);
	return *cast(T*) get(self, i);
}
ref const(T) get(T)(const ref ComponentStorage self, size_t i) @trusted {
	assert(T.sizeof == self.elementSize);
	return *cast(const(T)*) get(self, i);
}

/// Runs `self`'s finalizer (if any) on slot `i`, then zero-fills it, so a
/// hole never holds a stale value that looks live.
private void finalizeElement(ref ComponentStorage self, size_t i) @trusted {
	void* p = get(self, i);
	if (self.finalizeFunction !is null) self.finalizeFunction(p);
	memset(p, 0, self.elementSize);
}

/// Gives entity `e` a zero-filled slot, reusing a hole if there is one, and
/// records it in `e`'s index list. `e` must not already have this component.
void* add(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, EntityId e) @trusted {
	assert(e != invalidEntity);
	size_t slot;
	if (fp.dynarray.length(self.holes) > 0) {
		slot = *fp.dynarray.back(self.holes);
		fp.dynarray.popBack(self.holes);
	} else {
		slot = size(self);
		fp.pagedarray.grow(self.elements, 1);
		fp.dynarray.pushBack(self.slotOwners, invalidEntity);
	}
	self.slotOwners[slot] = e;
	ensureIndexSlot(entityComponentIndices[e], componentIdVal);
	assert(entityComponentIndices[e][componentIdVal] == ComponentStorage.invalid);
	entityComponentIndices[e][componentIdVal] = slot;

	void* p = get(self, slot);
	memset(p, 0, self.elementSize);
	return p;
}
/// Ditto, with the slot set to `Tcomponent.init`.
template add(Tcomponent, size_t Unique = 0) {
	ref Tcomponent add(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices, EntityId e) @trusted @nogc nothrow {
		auto p = cast(Tcomponent*) .add(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, e);
		*p = Tcomponent.init;
		return *p;
	}
}

/// Finalizes and releases entity `e`'s component. No other component moves:
/// the last slot is popped, any other becomes a hole.
bool remove(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, EntityId e) @trusted {
	if (entityComponentIndices is null || e >= fp.dynarray.length(entityComponentIndices)) return false;
	auto indices = entityComponentIndices[e];
	if (fp.dynarray.length(indices) <= componentIdVal || indices[componentIdVal] == ComponentStorage.invalid)
		return false;

	immutable slot = indices[componentIdVal];
	finalizeElement(self, slot);
	indices[componentIdVal] = ComponentStorage.invalid;
	if (slot + 1 == size(self)) {
		fp.dynarray.popBack(self.slotOwners);
		fp.pagedarray.popBack(self.elements);
	} else {
		self.slotOwners[slot] = invalidEntity;
		fp.dynarray.pushBack(self.holes, slot);
	}
	return true;
}
template remove(Tcomponent, size_t Unique = 0) {
	bool remove(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices, EntityId e) @nogc nothrow {
		return .remove(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, e);
	}
}

/// Swaps two slots' contents and owners, keeping both owners' index entries
/// pointing at their components. Leaves `holes` stale; callers rebuild it.
private void swapSlots(ref ComponentStorage self, size_t componentIdVal, EntityComponentIndices entityComponentIndices, size_t a, size_t b) @trusted {
	if (a == b) return;
	fp.pagedarray.swap(self.elements, a, b);
	immutable ownerA = self.slotOwners[a];
	self.slotOwners[a] = self.slotOwners[b];
	self.slotOwners[b] = ownerA;
	if (self.slotOwners[a] != invalidEntity) entityComponentIndices[self.slotOwners[a]][componentIdVal] = a;
	if (self.slotOwners[b] != invalidEntity) entityComponentIndices[self.slotOwners[b]][componentIdVal] = b;
}

/// Drops trailing holes and rebuilds the hole list from `slotOwners`.
private void settleHoles(ref ComponentStorage self) @trusted {
	while (size(self) > 0 && *fp.dynarray.back(self.slotOwners) == invalidEntity) {
		fp.dynarray.popBack(self.slotOwners);
		fp.pagedarray.popBack(self.elements);
	}
	fp.dynarray.clear(self.holes);
	foreach (slot; 0 .. size(self))
		if (self.slotOwners[slot] == invalidEntity)
			fp.dynarray.pushBack(self.holes, slot);
}

/// Walks the cycles of the permutation `order` (`order[i]` is the index of
/// whatever ends up *at* `i`, not where `i` goes - see `buildRemap`), handing
/// each transposition it needs to `swapPair`. Shared with
/// `ecrs.context.reorderEntities`, which permutes the entity table with the
/// same algorithm over a different swap.
package void applyPermutation(const(size_t)[] order, scope void delegate(size_t, size_t) @nogc nothrow swapPair) @trusted {
	immutable n = order.length;
	if (n <= 1) return;

	size_t* swaps = cast(size_t*) allocFunction(null, n * size_t.sizeof);
	scope(exit) allocFunction(swaps, 0);
	foreach (i; 0 .. n) swaps[order[i]] = i;

	foreach (i; 0 .. n)
		while (swaps[i] != i) {
			swapPair(swaps[i], i);
			immutable t = swaps[swaps[i]]; swaps[swaps[i]] = swaps[i]; swaps[i] = t;
		}
}

/// Inverts `order` into the relabelling `applyPermutation(order, ...)` performs:
/// `remap[old]` is the index `old` ends up at. Release it with
/// `allocFunction(remap, 0)`.
package EntityId* buildRemap(const(size_t)[] order) @trusted {
	auto remap = cast(EntityId*) allocFunction(null, order.length * EntityId.sizeof);
	foreach (i; 0 .. order.length) remap[order[i]] = cast(EntityId) i;
	return remap;
}

/// Applies a permutation of slots: `order[i]` is the slot whose component ends
/// up at `i`. Moves components, so it invalidates pointers into this storage.
void reorder(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, const(size_t)[] order) @trusted {
	assert(order.length == size(self));
	auto indices = entityComponentIndices;
	applyPermutation(order, (a, b) {
		swapSlots(self, componentIdVal, indices, a, b);
	});
	settleHoles(self);
}
template reorder(Tcomponent, size_t Unique = 0) {
	void reorder(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices, const(size_t)[] order) @nogc nothrow {
		.reorder(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, order);
	}
}

private void sortSlots(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices,
		scope bool delegate(size_t, size_t) @nogc nothrow liveLess) @trusted {
	import std.algorithm.sorting : stdSort = sort;

	immutable n = size(self);
	size_t* order = cast(size_t*) allocFunction(null, n * size_t.sizeof);
	scope(exit) allocFunction(order, 0);
	foreach (i; 0 .. n) order[i] = i;

	// Holes sort last, so `settleHoles` trims every one of them.
	bool cmp(size_t a, size_t b) @nogc nothrow {
		immutable holeA = self.slotOwners[a] == invalidEntity, holeB = self.slotOwners[b] == invalidEntity;
		if (holeA || holeB) return !holeA && holeB;
		return liveLess(a, b);
	}
	stdSort!cmp(order[0 .. n]);
	reorder(self, componentIdVal, entityComponentIndices, order[0 .. n]);
}

/// Sorts by `less(elementPtr(a), elementPtr(b))`, ignoring entity identity.
void sort(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, LessFunction less) @trusted {
	sortSlots(self, componentIdVal, entityComponentIndices, (a, b) => less(get(self, a), get(self, b)));
}
/// Sorts by `less(elementPtr(a), entityOf(a), elementPtr(b), entityOf(b))`.
void sort(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices, LessWithEntityFunction less) @trusted {
	sortSlots(self, componentIdVal, entityComponentIndices,
		(a, b) => less(get(self, a), self.slotOwners[a], get(self, b), self.slotOwners[b]));
}
template sortByValue(Tcomponent, size_t Unique = 0) {
	void sortByValue(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices) @nogc nothrow {
		sort(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, &sortByValueLess!Tcomponent);
	}
}
void sortMonotonic(ref ComponentStorage self, size_t componentIdVal, ref EntityComponentIndices entityComponentIndices) {
	sort(self, componentIdVal, entityComponentIndices, &monotonicLess);
}
template sortMonotonic(Tcomponent, size_t Unique = 0) {
	void sortMonotonic(ref ComponentStorage self, ref EntityComponentIndices entityComponentIndices) @nogc nothrow {
		sort(self, componentId!(Tcomponent, Unique)(), entityComponentIndices, &.monotonicLess);
	}
}

/// The storage half of an entity renumbering: relabels every slot's owner and
/// every entity id the components hold. Only `ecrs.context.reorderEntities`
/// calls this, because it alone also moves the index lists to match.
package void relabel(ref ComponentStorage self, const(EntityId)[] remap) @trusted {
	foreach (slot; 0 .. size(self)) {
		auto owner = &self.slotOwners[slot];
		if (*owner == invalidEntity) continue;
		if (*owner < remap.length) *owner = remap[*owner];
		if (self.remapFunction !is null) self.remapFunction(get(self, slot), remap);
	}
}


version(unittest) {
	/// An index table for entities `0 .. n`, each with an empty index list.
	private EntityComponentIndices makeIndices(size_t n) @trusted {
		EntityComponentIndices indices = null;
		fp.dynarray.growToSize(indices, n);
		foreach (e; 0 .. n) indices[e] = null;
		return indices;
	}
	private void freeIndices(ref EntityComponentIndices indices) @trusted {
		foreach (e; 0 .. fp.dynarray.length(indices))
			fp.dynarray.free(indices[e]);
		fp.dynarray.free(indices);
	}
	private bool ownersAre(const ref ComponentStorage storage, const(EntityId)[] expected...) {
		return storage.owners() == expected;
	}
}

unittest {
	// add/remove: owners are O(1) to read back, the last slot pops, any other
	// becomes a hole, and the next add fills the hole before growing.
	struct Vec2 { float x = 0, y = 0; }
	immutable id = componentId!Vec2();

	ComponentStorage storage = create(Vec2.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(5);
	scope(exit) freeIndices(indices);

	assert(storage.empty());
	foreach (e; 1 .. 5)
		storage.add!Vec2(indices, cast(EntityId) e) = Vec2(e, e);
	assert(storage.size() == 4 && storage.liveCount() == 4);
	assert(storage.getEntity(1) == 2);
	assert(ownersAre(storage, 1, 2, 3, 4));

	assert(storage.remove(id, indices, 4)); // last slot: popped
	assert(storage.size() == 3);
	assert(storage.remove(id, indices, 2)); // middle slot: a hole
	assert(storage.size() == 3 && storage.liveCount() == 2);
	assert(ownersAre(storage, 1, invalidEntity, 3));
	assert(*cast(const(Vec2)*) storage.get(1) == Vec2(0, 0)); // holes are zeroed
	assert(!storage.remove(id, indices, 2)); // already gone
	assert(!storage.remove(id, indices, 99)); // no such entity

	storage.add!Vec2(indices, 4) = Vec2(9, 9);
	assert(indices[4][id] == 1); // reused the hole
	assert(storage.size() == 3 && storage.liveCount() == 3);
	assert(storage.get!Vec2(indices[3][id]) == Vec2(3, 3));

	const(ComponentStorage)* constStorage = &storage;
	assert((*constStorage).get!Vec2(indices[4][id]) == Vec2(9, 9));
}

unittest {
	// The point of paging: neither growth nor removal of other components moves
	// a live one.
	immutable id = componentId!int();
	ComponentStorage storage = create(int.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(5001);
	scope(exit) freeIndices(indices);

	int* first = &storage.add!int(indices, 1);
	*first = 42;
	foreach (e; 2 .. 5001)
		storage.add!int(indices, cast(EntityId) e) = e;
	foreach (e; 2 .. 2500)
		storage.remove(id, indices, cast(EntityId) e);
	assert(&storage.get!int(indices[1][id]) is first);
	assert(*first == 42);
	assert(storage.get!int(indices[4000][id]) == 4000);
}

unittest {
	// Sorting moves holes to the end and trims them, and leaves every entity's
	// index pointing at its own value.
	immutable id = componentId!int();
	ComponentStorage storage = create(int.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(6);
	scope(exit) freeIndices(indices);

	immutable int[6] value = [0, 30, 10, 40, 20, 50];
	foreach (e; 1 .. 6)
		storage.add!int(indices, cast(EntityId) e) = value[e];
	storage.remove(id, indices, 3);
	storage.remove(id, indices, 1);
	assert(storage.liveCount() == 3);

	storage.sortByValue!int(indices);
	assert(storage.size() == 3); // holes trimmed
	assert(storage.get!int(0) == 10 && storage.get!int(1) == 20 && storage.get!int(2) == 50);
	assert(ownersAre(storage, 2, 4, 5));
	assert(storage.get!int(indices[4][id]) == 20);

	storage.add!int(indices, 1) = 1; // no holes left, so it appends
	assert(indices[1][id] == 3);
}

unittest {
	// sortMonotonic after a removal. This used to leave storage unsorted: the
	// removed slot had no owner, swap refused to move it, and the permutation's
	// bookkeeping carried on as though it had.
	immutable id = componentId!short();
	ComponentStorage storage = create(short.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(6);
	scope(exit) freeIndices(indices);

	foreach_reverse (e; 1 .. 6)
		storage.add!short(indices, cast(EntityId) e) = cast(short)(e * 10);
	storage.remove(id, indices, 3);

	storage.sortMonotonic(id, indices);
	assert(ownersAre(storage, 1, 2, 4, 5));
	assert(storage.get!short(indices[1][id]) == 10);
	assert(storage.get!short(indices[5][id]) == 50);
}

unittest {
	// reorder() with a hole that ends up in the middle: the hole list is
	// rebuilt, so the next add lands in it.
	immutable id = componentId!int();
	ComponentStorage storage = create(int.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(4);
	scope(exit) freeIndices(indices);

	foreach (e; 1 .. 4)
		storage.add!int(indices, cast(EntityId) e) = e;
	storage.remove(id, indices, 1); // slot 0 is a hole

	immutable size_t[3] order = [1, 0, 2]; // the hole moves to slot 1
	storage.reorder!int(indices, order[]);
	assert(ownersAre(storage, 2, invalidEntity, 3));
	assert(indices[2][id] == 0 && indices[3][id] == 2);

	storage.add!int(indices, 1) = 7;
	assert(indices[1][id] == 1);
}

unittest {
	// Finalizers run exactly once per component: on removal, or at free() for
	// whatever is still live - never again on a hole.
	import ecrs.registry : lookupComponentHooks;
	static struct Owned {
		int value;
		__gshared int finalized;
		static void finalize(ref Owned self) @nogc nothrow { ++finalized; }
	}
	immutable id = componentId!Owned();
	Owned.finalized = 0;

	auto indices = makeIndices(4);
	scope(exit) freeIndices(indices);
	ComponentStorage storage = create(Owned.sizeof, lookupComponentHooks(id).finalize);

	foreach (e; 1 .. 4)
		storage.add!Owned(indices, cast(EntityId) e).value = e;
	storage.remove(id, indices, 1);
	assert(Owned.finalized == 1);
	free(storage);
	assert(Owned.finalized == 3);
}

unittest {
	// relabel(): owners and the ids components hold, through the remap hook;
	// holes untouched.
	import ecrs.registry : lookupComponentHooks;
	static struct Link {
		EntityId target;
		static void remapEntities(ref Link self, const(EntityId)[] remap) @nogc nothrow {
			if (self.target < remap.length) self.target = remap[self.target];
		}
	}
	immutable id = componentId!Link();
	auto indices = makeIndices(4);
	scope(exit) freeIndices(indices);
	ComponentStorage storage = create(Link.sizeof, null, lookupComponentHooks(id).remap);
	scope(exit) free(storage);

	storage.add!Link(indices, 1).target = 2;
	storage.add!Link(indices, 2).target = 3;
	storage.add!Link(indices, 3).target = 1;
	storage.remove(id, indices, 2);

	immutable EntityId[4] remap = [0, 3, 1, 2];
	relabel(storage, remap[]);
	assert(ownersAre(storage, 3, invalidEntity, 2));
	assert(storage.get!Link(0).target == 1);
	assert(storage.get!Link(2).target == 3);
}
