/// Per-component-type storage, `Storage`, and the `Tag` trait components can opt into.
///
/// Element bytes live in an `fp.pagedarray`, so a component's address never changes while it exists: a query may hold a `ref` to one while nested queries add more. Each slot also records its owning entity, so finding a slot's entity is O(1). Removal leaves a hole for the next add to reuse rather than moving another component into the gap; only `reorder` and the sorts move components, and they also trim trailing holes.
///
/// Components follow `fp.lifecycle`: a type with a `finalize()` or destructor has it run once, when the component is removed or its storage freed. Every slot that holds no component is empty, all zero bytes.
module ecrs.storage;

import core.atomic : atomicLoad, atomicOp;
import core.stdc.string : memset;

static import ecrs.registry;
static import fp.dynarray;
static import fp.lifecycle;
static import fp.pagedarray;
static import fp.pointer;
static import std.algorithm.sorting;

public import ecrs.registry : EntityId, invalidEntity;

@nogc nothrow:


/// One entity's index list: a dynarray holding, for each component id, `Storage.invalid` or the slot of the entity's component in that component's storage.
alias IndexList = size_t*;

/// Every entity's index list, as a dynarray indexed by entity id.
alias IndexTable = IndexList*;

/// Opt-in marker for zero-sized tag components, which carry no per-entity payload.
struct Tag { enum isTag = true; }

/// Whether `T` is a tag component, as `Tag` marks one.
///
/// Examples:
/// ---
/// static assert(isTag!Tag && !isTag!int);
/// ---
template isTag(T) {
	static if (__traits(hasMember, T, "isTag"))
		enum isTag = T.isTag;
	else
		enum isTag = false;
}

/// The single shared instance of tag component `T`.
///
/// Examples:
/// ---
/// assert(&tagValue!Tag() is &tagValue!Tag());
/// ---
ref T tagValue(T)() if (isTag!T) {
	__gshared T value;
	return value;
}

/// Orders two type-erased components.
alias LessFunction = bool function(const(void)* a, const(void)* b) @nogc nothrow;

/// Orders two type-erased components, given their owning entities too.
alias LessWithEntityFunction = bool function(const(void)* a, EntityId ea, const(void)* b, EntityId eb) @nogc nothrow;

/// Type-erased backing storage for one component type, operated on by this module's functions.
///
/// It is plain data: `Context` keeps these in an `fp.dynarray`, which relocates them as bytes, and that never moves the components, which sit in pages it points to.
struct Storage {
	/// The `elementSize` of a storage not yet created, and the index-list entry of an absent component.
	enum size_t invalid = size_t.max;

	size_t elementSize = invalid; /// Bytes per component.
	private fp.pagedarray.PagedArray elements;
	private EntityId* slotOwners = null; // parallel to `elements`; invalidEntity marks a hole
	private size_t* holes = null; // holes to reuse before `elements` grows; it may miss some, which the next reorder reclaims
	private size_t live = 0;
	private ecrs.registry.RemapFunction remapFunction = null;
	private size_t changes = 0; // atomic; see `generation`
}


/// The number of slots, holes included; valid slots are `0 .. size`.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// assert(size(storage) == 0);
/// free(storage);
/// ---
size_t size(const ref Storage self) @trusted {
	return fp.dynarray.length(cast(EntityId*) self.slotOwners);
}

/// The number of slots holding a component.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// assert(liveCount(storage) == 0);
/// free(storage);
/// ---
size_t liveCount(const ref Storage self) { return self.live; }

/// Whether no slot holds a component.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// assert(empty(storage));
/// free(storage);
/// ---
bool empty(const ref Storage self) { return self.live == 0; }

/// Each slot's owner, `invalidEntity` for a hole: the entities that have this component.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// assert(owners(storage).length == 0);
/// free(storage);
/// ---
const(EntityId)[] owners(const ref Storage self) @trusted {
	return self.slotOwners[0 .. size(self)];
}

/// The owner of `slot`, which must be below `size`, or `invalidEntity` for a hole.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 2) !is null);
/// indices[1] = null;
/// assert(add(storage, ecrs.registry.componentId!int(), indices, 1) !is null);
/// assert(owner(storage, 0) == 1);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices);
/// ---
EntityId owner(const ref Storage self, size_t slot) @trusted {
	assert(slot < size(self));
	return self.slotOwners[slot];
}

/// A counter that advances on every change to `self`, and on every mutable access, since its caller may write through the pointer; equal generations mean unchanged contents. Atomic, because parallel systems may write distinct entities at once.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 2) !is null);
/// indices[1] = null;
/// immutable before = generation(storage);
/// assert(add!int(storage, indices, 1) !is null);
/// assert(generation(storage) > before);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices);
/// ---
size_t generation(const ref Storage self) @trusted {
	return atomicLoad(*cast(shared(const(size_t))*) &self.changes);
}

private void touch(ref Storage self) @trusted {
	atomicOp!"+="(*cast(shared(size_t)*) &self.changes, 1);
}

/// The component in slot `i`, which must be below `size`; the typed form checks that `T` is the right size.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 2) !is null);
/// indices[1] = null;
/// *add!int(storage, indices, 1) = 5;
/// assert(*cast(int*) ecrs.storage.get(storage, 0) == 5 && ecrs.storage.get!int(storage, 0) == 5);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices);
/// ---
void* get(ref Storage self, size_t i) { touch(self); return fp.pagedarray.get(self.elements, i); }
/// Ditto
const(void)* get(const ref Storage self, size_t i) { return fp.pagedarray.get(self.elements, i); }
/// Ditto
ref T get(T)(ref Storage self, size_t i) @trusted {
	assert(T.sizeof == self.elementSize);
	return *cast(T*) get(self, i);
}
/// Ditto
ref const(T) get(T)(const ref Storage self, size_t i) @trusted {
	assert(T.sizeof == self.elementSize);
	return *cast(const(T)*) get(self, i);
}


/// An empty storage of `elementSize`-byte components, whose lifetimes `finalizeFunction` ends and whose entity ids `remapFunction` relabels, either of which may be null. Allocates nothing until the first `add`, so it cannot fail.
///
/// Examples:
/// ---
/// static struct Owner { int* data; void finalize() @nogc nothrow { data = null; } }
/// Storage storage = create(Owner.sizeof, fp.lifecycle.finalizeFunction!Owner());
/// assert(storage.elementSize == Owner.sizeof);
/// free(storage);
/// ---
Storage create(size_t elementSize, fp.lifecycle.FinalizeFunction finalizeFunction = null, ecrs.registry.RemapFunction remapFunction = null) {
	Storage self;
	self.elementSize = elementSize;
	self.elements = fp.pagedarray.create(elementSize);
	self.elements.finalizeFunction = finalizeFunction;
	self.remapFunction = remapFunction;
	return self;
}

/// Ends every component's lifetime and frees what `self` owns, leaving it as `Storage.init`. Index lists still naming its slots must be freed or reset too.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// free(storage);
/// assert(storage.elementSize == Storage.invalid);
/// ---
void free(ref Storage self) @trusted {
	// Holes are empty, which `fp.lifecycle` requires finalizing to accept.
	fp.pagedarray.free(self.elements);
	fp.dynarray.free(self.slotOwners);
	fp.dynarray.free(self.holes);
	self = Storage.init;
}


private bool ensureIndexSlot(ref IndexList indices, size_t componentId) @trusted {
	immutable oldLength = fp.dynarray.length(indices);
	if (oldLength > componentId) return true;
	if (fp.dynarray.growToSize(indices, componentId + 1) is null) return false;
	foreach (i; oldLength .. componentId + 1)
		indices[i] = Storage.invalid;
	return true;
}

/// Gives entity `e` an empty, zero-filled slot for component `componentId`, reusing a hole if there is one, and records it in `e`'s index list, which `indexTable` must already have. `e` must not have this component yet.
///
/// Returns the slot, or null if allocation fails, leaving `self` as it was; `e`'s index list may have grown, its new entries `Storage.invalid`.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 2) !is null);
/// indices[1] = null;
/// immutable id = ecrs.registry.componentId!int();
/// int* p = cast(int*) add(storage, id, indices, 1);
/// assert(p !is null && *p == 0);
/// assert(indices[1][id] == 0);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices);
/// ---
void* add(ref Storage self, size_t componentId, ref IndexTable indexTable, EntityId e) @trusted {
	assert(e != invalidEntity && e < fp.dynarray.length(indexTable));
	if (!ensureIndexSlot(indexTable[e], componentId)) return null;
	assert(indexTable[e][componentId] == Storage.invalid);

	size_t slot;
	if (fp.dynarray.length(self.holes) > 0) {
		slot = *fp.dynarray.back(self.holes);
		cast(void) fp.dynarray.popBack(self.holes);
	} else {
		if (!fp.dynarray.pushBack(self.slotOwners, invalidEntity)) return null;
		if (fp.pagedarray.grow(self.elements, 1) is null) {
			cast(void) fp.dynarray.popBack(self.slotOwners);
			return null;
		}
		slot = size(self) - 1;
	}
	self.slotOwners[slot] = e;
	indexTable[e][componentId] = slot;
	++self.live;

	void* p = get(self, slot);
	memset(p, 0, self.elementSize);
	return p;
}

/// Ditto, for component `(T, unique)`, with the slot holding `T.init`. Returns null also if `T` cannot be registered.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 2) !is null);
/// indices[1] = null;
/// int* p = add!int(storage, indices, 1);
/// assert(p !is null);
/// *p = 7;
/// assert(ecrs.storage.get!int(storage, 0) == 7);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices);
/// ---
template add(T, size_t unique = 0) {
	T* add(ref Storage self, ref IndexTable indexTable, EntityId e) @trusted {
		immutable id = ecrs.registry.componentId!(T, unique)();
		if (id == fp.pointer.notFound) return null;
		auto p = cast(T*) .add(self, id, indexTable, e);
		if (p is null) return null;
		T value = T.init;
		fp.lifecycle.moveInto(*p, value);
		return p;
	}
}


/// Ends entity `e`'s component `componentId`'s lifetime and releases its slot. No other component moves: the last slot is popped, and any other becomes a hole.
///
/// Returns false, changing nothing, if `e` has no such component; it cannot otherwise fail.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 2) !is null);
/// indices[1] = null;
/// immutable id = ecrs.registry.componentId!int();
/// assert(add(storage, id, indices, 1) !is null);
/// assert(remove(storage, id, indices, 1));
/// assert(!remove(storage, id, indices, 1));
/// assert(empty(storage));
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices);
/// ---
bool remove(ref Storage self, size_t componentId, ref IndexTable indexTable, EntityId e) @trusted {
	if (e >= fp.dynarray.length(indexTable)) return false;
	auto indices = indexTable[e];
	if (fp.dynarray.length(indices) <= componentId || indices[componentId] == Storage.invalid)
		return false;

	immutable slot = indices[componentId];
	indices[componentId] = Storage.invalid;
	--self.live;
	touch(self);
	if (slot + 1 == size(self)) {
		cast(void) fp.dynarray.popBack(self.slotOwners);
		fp.pagedarray.popBack(self.elements);
		return true;
	}

	void* p = get(self, slot);
	if (self.elements.finalizeFunction !is null)
		self.elements.finalizeFunction(cast(inout(ubyte)[]) (cast(ubyte*) p)[0 .. self.elementSize]);
	// Zeroed even without a finalizer, so a hole never holds a stale value that looks live.
	memset(p, 0, self.elementSize);
	self.slotOwners[slot] = invalidEntity;
	// A hole missing from the list just waits for the next reorder to reclaim it.
	cast(void) fp.dynarray.pushBack(self.holes, slot);
	return true;
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 2) !is null);
/// indices[1] = null;
/// assert(add!int(storage, indices, 1) !is null);
/// assert(remove!int(storage, indices, 1));
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices);
/// ---
template remove(T, size_t unique = 0) {
	bool remove(ref Storage self, ref IndexTable indexTable, EntityId e) {
		return .remove(self, ecrs.registry.componentId!(T, unique)(), indexTable, e);
	}
}


/// Walks the cycles of the permutation `order`, handing each transposition it needs to `swapPair`. `order[i]` is the index of whatever ends up at `i`, not where `i` goes.
///
/// Returns false, calling `swapPair` never, if its scratch buffer cannot be allocated.
///
/// Examples:
/// ---
/// int[3] values = [10, 20, 30];
/// immutable size_t[3] order = [2, 0, 1];
/// assert(applyPermutation(order[], (a, b) { immutable t = values[a]; values[a] = values[b]; values[b] = t; }));
/// assert(values == [30, 10, 20]);
/// ---
package bool applyPermutation(const(size_t)[] order, scope void delegate(size_t, size_t) @nogc nothrow swapPair) @trusted {
	immutable n = order.length;
	if (n <= 1) return true;

	auto swaps = cast(size_t*) fp.pointer.allocFunction(null, n * size_t.sizeof);
	if (swaps is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(swaps, 0);
	foreach (i; 0 .. n) swaps[order[i]] = i;

	foreach (i; 0 .. n)
		while (swaps[i] != i) {
			swapPair(swaps[i], i);
			immutable t = swaps[swaps[i]]; swaps[swaps[i]] = swaps[i]; swaps[i] = t;
		}
	return true;
}

/// Inverts `order` into the relabelling `applyPermutation(order, ...)` performs: `remap[old]` is the index `old` ends up at. Release it with `fp.pointer.allocFunction(remap, 0)`.
///
/// Returns null if allocation fails.
///
/// Examples:
/// ---
/// immutable size_t[3] order = [2, 0, 1];
/// EntityId* remap = buildRemap(order[]);
/// assert(remap !is null);
/// assert(remap[0 .. 3] == [1, 2, 0]);
/// cast(void) fp.pointer.allocFunction(remap, 0);
/// ---
package EntityId* buildRemap(const(size_t)[] order) @trusted {
	// One element at least, so an empty order still yields a pointer to free rather than a null that reads as failure.
	immutable n = order.length > 0 ? order.length : 1;
	auto remap = cast(EntityId*) fp.pointer.allocFunction(null, n * EntityId.sizeof);
	if (remap is null) return null;
	foreach (i; 0 .. order.length) remap[order[i]] = cast(EntityId) i;
	return remap;
}

// Keeps both owners' index entries naming their components, but leaves `holes` stale for the caller to rebuild.
private void swapSlots(ref Storage self, size_t componentId, IndexTable indexTable, size_t a, size_t b) @trusted {
	if (a == b) return;
	touch(self);
	fp.pagedarray.swap(self.elements, a, b);
	immutable ownerA = self.slotOwners[a];
	self.slotOwners[a] = self.slotOwners[b];
	self.slotOwners[b] = ownerA;
	if (self.slotOwners[a] != invalidEntity) indexTable[self.slotOwners[a]][componentId] = a;
	if (self.slotOwners[b] != invalidEntity) indexTable[self.slotOwners[b]][componentId] = b;
}

private void settleHoles(ref Storage self) @trusted {
	while (size(self) > 0 && *fp.dynarray.back(self.slotOwners) == invalidEntity) {
		cast(void) fp.dynarray.popBack(self.slotOwners);
		fp.pagedarray.popBack(self.elements);
	}
	fp.dynarray.clear(self.holes);
	foreach (slot; 0 .. size(self))
		if (self.slotOwners[slot] == invalidEntity)
			cast(void) fp.dynarray.pushBack(self.holes, slot); // a hole it misses is only left unreused
}

/// Applies a permutation of slots, `order[i]` being the slot whose component ends up at `i`, and trims trailing holes. It moves components, so it invalidates pointers into `self`.
///
/// Returns false, changing nothing, if allocation fails.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 3) !is null);
/// indices[1] = indices[2] = null;
/// immutable id = ecrs.registry.componentId!int();
/// *add!int(storage, indices, 1) = 1;
/// *add!int(storage, indices, 2) = 2;
/// immutable size_t[2] order = [1, 0];
/// assert(reorder(storage, id, indices, order[]));
/// assert(ecrs.storage.get!int(storage, 0) == 2 && indices[2][id] == 0);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices[2]);
/// fp.dynarray.free(indices);
/// ---
bool reorder(ref Storage self, size_t componentId, ref IndexTable indexTable, const(size_t)[] order) @trusted {
	assert(order.length == size(self));
	auto indices = indexTable;
	if (!applyPermutation(order, (a, b) { swapSlots(self, componentId, indices, a, b); }))
		return false;
	settleHoles(self);
	return true;
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(reorder!int(storage, indices, null));
/// ---
template reorder(T, size_t unique = 0) {
	bool reorder(ref Storage self, ref IndexTable indexTable, const(size_t)[] order) {
		return .reorder(self, ecrs.registry.componentId!(T, unique)(), indexTable, order);
	}
}


/// Compares two type-erased `T`s with `<`.
///
/// Examples:
/// ---
/// int a = 1, b = 2;
/// assert(sortByValueLess!int(&a, &b) && !sortByValueLess!int(&b, &a));
/// ---
bool sortByValueLess(T)(const(void)* a, const(void)* b) @trusted {
	return *cast(const(T)*) a < *cast(const(T)*) b;
}

private bool monotonicLess(const(void)* a, EntityId ea, const(void)* b, EntityId eb) {
	return ea < eb;
}

private bool sortSlots(ref Storage self, size_t componentId, ref IndexTable indexTable,
		scope bool delegate(size_t, size_t) @nogc nothrow liveLess) @trusted {
	immutable n = size(self);
	if (n == 0) return true;
	auto order = cast(size_t*) fp.pointer.allocFunction(null, n * size_t.sizeof);
	if (order is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(order, 0);
	foreach (i; 0 .. n) order[i] = i;

	// Holes sort last, so `settleHoles` trims every one of them.
	bool cmp(size_t a, size_t b) @nogc nothrow {
		immutable holeA = self.slotOwners[a] == invalidEntity, holeB = self.slotOwners[b] == invalidEntity;
		if (holeA || holeB) return !holeA && holeB;
		return liveLess(a, b);
	}
	std.algorithm.sorting.sort!cmp(order[0 .. n]);
	return reorder(self, componentId, indexTable, order[0 .. n]);
}

/// Sorts the components by `less(component(a), component(b))`, ignoring their owners, and trims trailing holes. It moves components, so it invalidates pointers into `self`.
///
/// Returns false, changing nothing, if allocation fails.
///
/// Examples:
/// ---
/// static bool greater(const(void)* a, const(void)* b) @nogc nothrow { return *cast(const(int)*) a > *cast(const(int)*) b; }
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 3) !is null);
/// indices[1] = indices[2] = null;
/// *add!int(storage, indices, 1) = 1;
/// *add!int(storage, indices, 2) = 2;
/// assert(sort(storage, ecrs.registry.componentId!int(), indices, &greater));
/// assert(ecrs.storage.get!int(storage, 0) == 2);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices[2]);
/// fp.dynarray.free(indices);
/// ---
bool sort(ref Storage self, size_t componentId, ref IndexTable indexTable, LessFunction less) @trusted {
	return sortSlots(self, componentId, indexTable, (a, b) => less(get(self, a), get(self, b)));
}

/// Ditto, by `less(component(a), owner(a), component(b), owner(b))`.
///
/// Examples:
/// ---
/// static bool byOwner(const(void)*, EntityId ea, const(void)*, EntityId eb) @nogc nothrow { return ea > eb; }
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(sort(storage, ecrs.registry.componentId!int(), indices, &byOwner));
/// ---
bool sort(ref Storage self, size_t componentId, ref IndexTable indexTable, LessWithEntityFunction less) @trusted {
	return sortSlots(self, componentId, indexTable,
		(a, b) => less(get(self, a), self.slotOwners[a], get(self, b), self.slotOwners[b]));
}

/// Sorts component `(T, unique)`'s storage by value with `<`, as `sort` does.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 3) !is null);
/// indices[1] = indices[2] = null;
/// *add!int(storage, indices, 1) = 2;
/// *add!int(storage, indices, 2) = 1;
/// assert(sortByValue!int(storage, indices));
/// assert(ecrs.storage.get!int(storage, 0) == 1);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices[2]);
/// fp.dynarray.free(indices);
/// ---
template sortByValue(T, size_t unique = 0) {
	bool sortByValue(ref Storage self, ref IndexTable indexTable) {
		return sort(self, ecrs.registry.componentId!(T, unique)(), indexTable, &sortByValueLess!T);
	}
}

/// Sorts the components into owner order, as `sort` does.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 3) !is null);
/// indices[1] = indices[2] = null;
/// immutable id = ecrs.registry.componentId!int();
/// assert(add(storage, id, indices, 2) !is null && add(storage, id, indices, 1) !is null);
/// assert(sortMonotonic(storage, id, indices));
/// assert(owners(storage) == [1, 2]);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices[2]);
/// fp.dynarray.free(indices);
/// ---
bool sortMonotonic(ref Storage self, size_t componentId, ref IndexTable indexTable) {
	return sort(self, componentId, indexTable, &monotonicLess);
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(sortMonotonic!int(storage, indices));
/// ---
template sortMonotonic(T, size_t unique = 0) {
	bool sortMonotonic(ref Storage self, ref IndexTable indexTable) {
		return sort(self, ecrs.registry.componentId!(T, unique)(), indexTable, &.monotonicLess);
	}
}


/// The storage half of an entity renumbering: relabels every slot's owner and, through the remap hook, every entity id the components hold. Only `ecrs.context` calls it, because it alone also moves the index lists to match.
///
/// Examples:
/// ---
/// Storage storage = create(int.sizeof);
/// scope(exit) free(storage);
/// IndexTable indices = null;
/// assert(fp.dynarray.growToSize(indices, 3) !is null);
/// indices[1] = indices[2] = null;
/// assert(add(storage, ecrs.registry.componentId!int(), indices, 1) !is null);
/// immutable EntityId[3] remap = [0, 2, 1];
/// relabel(storage, remap[]);
/// assert(owner(storage, 0) == 2);
/// fp.dynarray.free(indices[1]);
/// fp.dynarray.free(indices);
/// ---
package void relabel(ref Storage self, const(EntityId)[] remap) @trusted {
	touch(self);
	foreach (slot; 0 .. size(self)) {
		auto slotOwner = &self.slotOwners[slot];
		if (*slotOwner == invalidEntity) continue;
		if (*slotOwner < remap.length) *slotOwner = remap[*slotOwner];
		if (self.remapFunction !is null) self.remapFunction(get(self, slot), remap);
	}
}


version(unittest) {
	// An index table for entities `0 .. n`, each with an empty index list.
	private IndexTable makeIndices(size_t n) @trusted {
		IndexTable indices = null;
		assert(fp.dynarray.growToSize(indices, n) !is null);
		foreach (e; 0 .. n) indices[e] = null;
		return indices;
	}
	private void freeIndices(ref IndexTable indices) @trusted {
		foreach (e; 0 .. fp.dynarray.length(indices))
			fp.dynarray.free(indices[e]);
		fp.dynarray.free(indices);
	}
	private bool ownersAre(const ref Storage storage, const(EntityId)[] expected...) {
		return owners(storage) == expected;
	}
}

unittest {
	// generation: every add, remove, mutable access, sort and relabel advances it; const access does not.
	immutable id = ecrs.registry.componentId!long();
	Storage storage = create(long.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(3);
	scope(exit) freeIndices(indices);

	auto g = generation(storage);
	*add!long(storage, indices, 1) = 5;
	*add!long(storage, indices, 2) = 4;
	assert(generation(storage) > g);

	g = generation(storage);
	const(Storage)* constStorage = &storage;
	assert(get!long(*constStorage, 0) == 5);
	assert(generation(storage) == g);
	get!long(storage, 0) = 6;
	assert(generation(storage) > g);

	g = generation(storage);
	assert(sortByValue!long(storage, indices));
	assert(generation(storage) > g);

	g = generation(storage);
	immutable EntityId[3] remap = [0, 2, 1];
	relabel(storage, remap[]);
	assert(generation(storage) > g);

	g = generation(storage);
	assert(remove(storage, id, indices, 1)); // relabel left the index lists alone, so entity 1 still names slot 1, the last
	assert(generation(storage) > g);
}

unittest {
	// add and remove: the last slot pops, any other becomes a hole, and the next add fills the hole before growing.
	struct Vec2 { float x = 0, y = 0; }
	immutable id = ecrs.registry.componentId!Vec2();

	Storage storage = create(Vec2.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(5);
	scope(exit) freeIndices(indices);

	assert(empty(storage));
	foreach (e; 1 .. 5)
		*add!Vec2(storage, indices, cast(EntityId) e) = Vec2(e, e);
	assert(size(storage) == 4 && liveCount(storage) == 4);
	assert(owner(storage, 1) == 2);
	assert(ownersAre(storage, 1, 2, 3, 4));

	assert(remove(storage, id, indices, 4)); // last slot: popped
	assert(size(storage) == 3);
	assert(remove(storage, id, indices, 2)); // middle slot: a hole
	assert(size(storage) == 3 && liveCount(storage) == 2);
	assert(ownersAre(storage, 1, invalidEntity, 3));
	assert(*cast(const(Vec2)*) get(storage, 1) == Vec2(0, 0));
	assert(!remove(storage, id, indices, 2));
	assert(!remove(storage, id, indices, 99));

	*add!Vec2(storage, indices, 4) = Vec2(9, 9);
	assert(indices[4][id] == 1);
	assert(size(storage) == 3 && liveCount(storage) == 3);
	assert(get!Vec2(storage, indices[3][id]) == Vec2(3, 3));

	const(Storage)* constStorage = &storage;
	assert(get!Vec2(*constStorage, indices[4][id]) == Vec2(9, 9));
}

unittest {
	// Neither growth nor removal of other components moves a live one.
	immutable id = ecrs.registry.componentId!int();
	Storage storage = create(int.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(5001);
	scope(exit) freeIndices(indices);

	int* first = add!int(storage, indices, 1);
	*first = 42;
	foreach (e; 2 .. 5001)
		*add!int(storage, indices, cast(EntityId) e) = e;
	foreach (e; 2 .. 2500)
		assert(remove(storage, id, indices, cast(EntityId) e));
	assert(&get!int(storage, indices[1][id]) is first);
	assert(*first == 42);
	assert(get!int(storage, indices[4000][id]) == 4000);
}

unittest {
	// A failed allocation leaves the storage as it was, and an untracked hole still counts as empty.
	immutable id = ecrs.registry.componentId!int();
	Storage storage = create(int.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(4);
	scope(exit) freeIndices(indices);

	foreach (n; 0 .. 16) {
		ecrs.registry.failAllocationsAfter(n);
		immutable added = add(storage, id, indices, 1) !is null;
		ecrs.registry.restoreAllocations();
		if (added) break;
		assert(size(storage) == 0 && liveCount(storage) == 0);
	}
	assert(liveCount(storage) == 1);
	*add!int(storage, indices, 2) = 2;
	*add!int(storage, indices, 3) = 3;

	ecrs.registry.failAllocationsAfter(0);
	assert(remove(storage, id, indices, 1));
	immutable size_t[3] order = [2, 1, 0];
	assert(!reorder(storage, id, indices, order[]));
	ecrs.registry.restoreAllocations();
	assert(liveCount(storage) == 2 && ownersAre(storage, invalidEntity, 2, 3));

	assert(reorder(storage, id, indices, order[]));
	assert(ownersAre(storage, 3, 2));
}

unittest {
	// Sorting moves holes to the end and trims them, and leaves every entity's index naming its own value.
	immutable id = ecrs.registry.componentId!int();
	Storage storage = create(int.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(6);
	scope(exit) freeIndices(indices);

	immutable int[6] value = [0, 30, 10, 40, 20, 50];
	foreach (e; 1 .. 6)
		*add!int(storage, indices, cast(EntityId) e) = value[e];
	assert(remove(storage, id, indices, 3));
	assert(remove(storage, id, indices, 1));
	assert(liveCount(storage) == 3);

	assert(sortByValue!int(storage, indices));
	assert(size(storage) == 3);
	assert(get!int(storage, 0) == 10 && get!int(storage, 1) == 20 && get!int(storage, 2) == 50);
	assert(ownersAre(storage, 2, 4, 5));
	assert(get!int(storage, indices[4][id]) == 20);

	*add!int(storage, indices, 1) = 1;
	assert(indices[1][id] == 3);
}

unittest {
	// sortMonotonic sorts past a hole left by a removal.
	immutable id = ecrs.registry.componentId!short();
	Storage storage = create(short.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(6);
	scope(exit) freeIndices(indices);

	foreach_reverse (e; 1 .. 6)
		*add!short(storage, indices, cast(EntityId) e) = cast(short)(e * 10);
	assert(remove(storage, id, indices, 3));

	assert(sortMonotonic(storage, id, indices));
	assert(ownersAre(storage, 1, 2, 4, 5));
	assert(get!short(storage, indices[1][id]) == 10);
	assert(get!short(storage, indices[5][id]) == 50);
}

unittest {
	// reorder with a hole that ends up in the middle rebuilds the hole list, so the next add lands in it.
	immutable id = ecrs.registry.componentId!int();
	Storage storage = create(int.sizeof);
	scope(exit) free(storage);
	auto indices = makeIndices(4);
	scope(exit) freeIndices(indices);

	foreach (e; 1 .. 4)
		*add!int(storage, indices, cast(EntityId) e) = e;
	assert(remove(storage, id, indices, 1));

	immutable size_t[3] order = [1, 0, 2];
	assert(reorder!int(storage, indices, order[]));
	assert(ownersAre(storage, 2, invalidEntity, 3));
	assert(indices[2][id] == 0 && indices[3][id] == 2);

	*add!int(storage, indices, 1) = 7;
	assert(indices[1][id] == 1);
}

unittest {
	// Lifetimes end exactly once per component: on removal, or at free for whatever is still live, never again on a hole.
	static struct Owned {
		int value;
		__gshared int finalized;
		void finalize() @nogc nothrow {
			if (value != 0) ++finalized;
			value = 0;
		}
	}
	immutable id = ecrs.registry.componentId!Owned();
	Owned.finalized = 0;

	auto indices = makeIndices(4);
	scope(exit) freeIndices(indices);
	Storage storage = create(Owned.sizeof, ecrs.registry.lookupHooks(id).finalizeFunction);

	foreach (e; 1 .. 4)
		add!Owned(storage, indices, cast(EntityId) e).value = e;
	assert(remove(storage, id, indices, 1));
	assert(Owned.finalized == 1);
	assert(remove(storage, id, indices, 3));
	assert(Owned.finalized == 2);
	free(storage);
	assert(Owned.finalized == 3);
}

unittest {
	// relabel rewrites owners and, through the remap hook, the ids components hold; holes are untouched.
	static struct Link {
		EntityId target;
		static void remapEntities(ref Link self, const(EntityId)[] remap) @nogc nothrow {
			if (self.target < remap.length) self.target = remap[self.target];
		}
	}
	immutable id = ecrs.registry.componentId!Link();
	auto indices = makeIndices(4);
	scope(exit) freeIndices(indices);
	Storage storage = create(Link.sizeof, null, ecrs.registry.lookupHooks(id).remapFunction);
	scope(exit) free(storage);

	add!Link(storage, indices, 1).target = 2;
	add!Link(storage, indices, 2).target = 3;
	add!Link(storage, indices, 3).target = 1;
	assert(remove(storage, id, indices, 2));

	immutable EntityId[4] remap = [0, 3, 1, 2];
	relabel(storage, remap[]);
	assert(ownersAre(storage, 3, invalidEntity, 2));
	assert(get!Link(storage, 0).target == 1);
	assert(get!Link(storage, 2).target == 3);
}
