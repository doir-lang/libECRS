/// The entity and component database, `Context`.
///
/// There is deliberately no `Entity` handle wrapping a thread-local current context: callers pass the `Context`, and an `EntityId` where relevant, to every function.
module ecrs.context;

import core.atomic : atomicLoad, atomicOp;

static import ecrs.registry;
static import ecrs.storage;
static import fp.dynarray;
static import fp.pointer;

public import ecrs.registry : EntityId, invalidEntity;

@nogc nothrow:


/// A holder of entity ids outside the store, such as a query memo table, that every renumbering rewrites alongside the components. `remap[old]` is the id `old` becomes.
alias RemapHookFunction = void function(void* userData, const(EntityId)[] remap) @nogc nothrow;

private struct RemapHook {
	RemapHookFunction fn;
	void* userData;
}

/// The entity and component database: one `ecrs.storage.Storage` per component id, and each entity's index list mapping its components to their slots.
///
/// It is plain data, released only by `free`: pair `create` with `scope(exit) free(ctx)`.
///
/// Concurrency: any number of threads may read at once, and may write existing components of distinct entities. Structural changes, meaning adding or removing entities, components, storages or remap hooks, renumbering and sorting, need exclusive access; inside an `ecrs.system` parallel combinator they fail an assert rather than race, whatever the pool size.
struct Context {
	private ecrs.storage.Storage* storages = null;
	ecrs.storage.IndexTable indexTable = null; /// Every entity's index list, freed entities' included.
	size_t* freelist = null; /// Freed entity ids, which `addEntity` hands out again, last freed first.
	private RemapHook* remapHooks = null;
	private size_t parallelDepth = 0; // atomic; nonzero while a parallel system runs
}

/// Whether an `ecrs.system` parallel combinator is running on `self`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// assert(!inParallel(ctx));
/// free(ctx);
/// ---
bool inParallel(const ref Context self) @trusted {
	return atomicLoad(*cast(shared(const(size_t))*) &self.parallelDepth) != 0;
}

/// Marks `self` as inside a parallel combinator until the matching `exitParallel`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// enterParallel(ctx);
/// assert(inParallel(ctx));
/// exitParallel(ctx);
/// assert(!inParallel(ctx));
/// free(ctx);
/// ---
package void enterParallel(ref Context self) @trusted {
	atomicOp!"+="(*cast(shared(size_t)*) &self.parallelDepth, 1);
}

/// Ditto
package void exitParallel(ref Context self) @trusted {
	atomicOp!"-="(*cast(shared(size_t)*) &self.parallelDepth, 1);
}

private enum string structuralChange = "ecrs: structural change inside a parallel system; make it after the pass";


private bool freelistContains(const(size_t)* freelist, size_t value) @trusted {
	foreach (i; 0 .. fp.dynarray.length(freelist))
		if (freelist[i] == value) return true;
	return false;
}

/// A view of the live entities of a `Context`, from `entities`, usable in a `foreach`.
struct EntityRange {
	private const(Context)* context;
	private size_t index;

	/// The range primitives, which `foreach` calls.
	///
	/// Examples:
	/// ---
	/// Context ctx = create();
	/// scope(exit) free(ctx);
	/// EntityRange range = entities(ctx);
	/// assert(!range.empty && range.front == invalidEntity);
	/// range.popFront();
	/// assert(range.empty);
	/// ---
	bool empty() const @trusted @nogc nothrow { return index >= fp.dynarray.length(context.indexTable); }
	/// Ditto
	EntityId front() const @nogc nothrow { return cast(EntityId) index; }
	/// Ditto
	void popFront() @nogc nothrow { ++index; skipFreed(this); }
}

private void skipFreed(ref EntityRange range) @trusted {
	while (!range.empty && freelistContains(range.context.freelist, range.index))
		++range.index;
}

/// Every live entity of `self` in id order, the reserved entity 0 included.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// size_t count = 0;
/// foreach (entity; entities(ctx)) ++count;
/// assert(count == 2);
/// ---
EntityRange entities(const ref Context self) {
	EntityRange range = EntityRange(&self, 0);
	skipFreed(range);
	return range;
}


private ref ecrs.storage.Storage existingStorage(ref Context self, size_t componentId) @trusted {
	assert(fp.dynarray.length(self.storages) > componentId);
	assert(self.storages[componentId].elementSize != ecrs.storage.Storage.invalid);
	return self.storages[componentId];
}
private ref const(ecrs.storage.Storage) existingStorage(const ref Context self, size_t componentId) @trusted {
	assert(fp.dynarray.length(self.storages) > componentId);
	assert(self.storages[componentId].elementSize != ecrs.storage.Storage.invalid);
	return self.storages[componentId];
}

private bool hasStorage(const ref Context self, size_t componentId) @trusted {
	return componentId < fp.dynarray.length(self.storages)
		&& self.storages[componentId].elementSize != ecrs.storage.Storage.invalid;
}

private bool reserveInvalidEntity(ref Context self) @trusted {
	return fp.dynarray.pushBack(self.indexTable, cast(ecrs.storage.IndexList) null);
}


/// A context with the invalid entity, id 0, already reserved. Use it rather than `Context.init`. It cannot fail: if it cannot allocate, the first `addEntity` reserves entity 0 instead.
///
/// Examples:
/// ---
/// Context ctx = create();
/// assert(entityCount(ctx) == 1);
/// free(ctx);
/// ---
Context create() {
	Context c;
	cast(void) reserveInvalidEntity(c);
	return c;
}

/// Ends every component's lifetime and frees everything `self` owns, leaving it as `Context.init`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// free(ctx);
/// assert(entityCount(ctx) == 0);
/// ---
void free(ref Context self) @trusted {
	foreach (i; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[i].elementSize != ecrs.storage.Storage.invalid)
			ecrs.storage.free(self.storages[i]);
	fp.dynarray.free(self.storages);
	foreach (i; 0 .. fp.dynarray.length(self.indexTable))
		fp.dynarray.free(self.indexTable[i]);
	fp.dynarray.free(self.indexTable);
	fp.dynarray.free(self.freelist);
	fp.dynarray.free(self.remapHooks);
	self = Context.init;
}


/// The storage for component `componentId`, created on first use with `elementSize`-byte elements and the hooks its type registered. The pointer is valid until another storage is created.
///
/// Returns null if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// auto storage = getStorage(ctx, ecrs.registry.componentId!int(), int.sizeof);
/// assert(storage !is null && ecrs.storage.empty(*storage));
/// ---
ecrs.storage.Storage* getStorage(ref Context self, size_t componentId, size_t elementSize) @trusted {
	if (hasStorage(self, componentId)) return &self.storages[componentId];
	assert(!inParallel(self), structuralChange);
	assert(elementSize != ecrs.storage.Storage.invalid, "ecrs: component of unknown size");

	immutable count = fp.dynarray.length(self.storages);
	if (componentId >= count) {
		if (fp.dynarray.growToSize(self.storages, componentId + 1) is null) return null;
		foreach (i; count .. componentId + 1) self.storages[i] = ecrs.storage.Storage.init;
	}
	immutable hooks = ecrs.registry.lookupHooks(componentId);
	self.storages[componentId] = ecrs.storage.create(elementSize, hooks.finalizeFunction, hooks.remapFunction);
	return &self.storages[componentId];
}

/// Ditto, for a const context, which cannot create one: returns null if no entity has had the component. `elementSize`, unless `Storage.invalid`, is checked against the storage's.
///
/// Examples:
/// ---
/// const Context ctx = create();
/// assert(getStorage(ctx, ecrs.registry.componentId!int()) is null);
/// ---
const(ecrs.storage.Storage)* getStorage(const ref Context self, size_t componentId, size_t elementSize = ecrs.storage.Storage.invalid) @trusted {
	if (!hasStorage(self, componentId)) return null;
	assert(elementSize == ecrs.storage.Storage.invalid || elementSize == self.storages[componentId].elementSize);
	return &self.storages[componentId];
}

/// Ditto, for component `(T, unique)`. Returns null also if `T` cannot be registered.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// assert(getStorage!int(ctx) !is null);
/// ---
template getStorage(T, size_t unique = 0) {
	ecrs.storage.Storage* getStorage(ref Context self) {
		immutable id = ecrs.registry.componentId!(T, unique)();
		return id == fp.pointer.notFound ? null : .getStorage(self, id, T.sizeof);
	}
}

/// One past the highest component id `self` has room for, so `getStorage` over `0 .. storageCount` visits every storage it has.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// immutable id = ecrs.registry.componentId!int();
/// assert(getStorage(ctx, id, int.sizeof) !is null);
/// assert(storageCount(ctx) > id);
/// ---
size_t storageCount(const ref Context self) @trusted {
	return fp.dynarray.length(self.storages);
}

/// `ecrs.storage.generation` of component `componentId`'s storage, or 0 if no entity has had the component.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// immutable id = ecrs.registry.componentId!int();
/// assert(generation(ctx, id) == 0);
/// assert(addComponent(ctx, addEntity(ctx), id) !is null);
/// assert(generation(ctx, id) > 0);
/// ---
size_t generation(const ref Context self, size_t componentId) {
	auto storage = getStorage(self, componentId);
	return storage is null ? 0 : ecrs.storage.generation(*storage);
}


/// The number of live entities, the reserved entity 0 included.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// cast(void) addEntity(ctx);
/// assert(entityCount(ctx) == 2);
/// ---
size_t entityCount(const ref Context self) @trusted {
	return fp.dynarray.length(self.indexTable) - fp.dynarray.length(self.freelist);
}

/// A new entity with no components, reusing the most recently freed id if there is one.
///
/// Returns `invalidEntity` if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// assert(e == 1);
/// ---
EntityId addEntity(ref Context self) @trusted {
	assert(!inParallel(self), structuralChange);
	if (fp.dynarray.length(self.indexTable) == 0 && !reserveInvalidEntity(self)) return invalidEntity;
	if (fp.dynarray.length(self.freelist) > 0) {
		immutable e = *fp.dynarray.back(self.freelist);
		cast(void) fp.dynarray.popBack(self.freelist);
		return cast(EntityId) e;
	}
	immutable e = cast(EntityId) fp.dynarray.length(self.indexTable);
	if (!fp.dynarray.pushBack(self.indexTable, cast(ecrs.storage.IndexList) null)) return invalidEntity;
	return e;
}

/// Removes the live entity `e`, which must not be `invalidEntity`, ending its components' lifetimes; its id goes on the freelist for `addEntity` to hand out again.
///
/// Returns false if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// assert(removeEntity(ctx, e));
/// assert(entityCount(ctx) == 1);
/// ---
bool removeEntity(ref Context self, EntityId e) @trusted {
	assert(!inParallel(self), structuralChange);
	assert(e != invalidEntity && e < fp.dynarray.length(self.indexTable));
	if (fp.dynarray.reserve(self.freelist, fp.dynarray.length(self.freelist) + 1) is null) return false;

	auto indices = self.indexTable[e];
	foreach (componentId; 0 .. fp.dynarray.length(indices))
		if (indices[componentId] != ecrs.storage.Storage.invalid)
			cast(void) ecrs.storage.remove(self.storages[componentId], componentId, self.indexTable, e);
	fp.dynarray.free(self.indexTable[e]);
	self.indexTable[e] = null;
	cast(void) fp.dynarray.pushBack(self.freelist, cast(size_t) e); // reserved above
	return true;
}


/// Whether entity `e` has component `componentId`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// assert(!hasComponent(ctx, e, ecrs.registry.componentId!int()));
/// ---
bool hasComponent(const ref Context self, EntityId e, size_t componentId) @trusted {
	return e < fp.dynarray.length(self.indexTable)
		&& fp.dynarray.length(self.indexTable[e]) > componentId
		&& self.indexTable[e][componentId] != ecrs.storage.Storage.invalid;
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// assert(addComponent!int(ctx, e) !is null);
/// assert(hasComponent!int(ctx, e));
/// ---
template hasComponent(T, size_t unique = 0) {
	bool hasComponent(const ref Context self, EntityId e) {
		return .hasComponent(self, e, ecrs.registry.componentId!(T, unique)());
	}
}

/// Gives the live entity `e`, which must not have it yet, component `componentId`, zero-filled since there is no type to construct; prefer the typed form when the type is known. `elementSize` defaults to the registered size.
///
/// The component's address is stable until it is removed or a renumbering or sort moves it; adding other components, of any type, never does.
///
/// Returns null if allocation fails, leaving `e` without the component.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// int* p = cast(int*) addComponent(ctx, e, ecrs.registry.componentId!int());
/// assert(p !is null && *p == 0);
/// ---
void* addComponent(ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.invalid) {
	assert(!inParallel(self), structuralChange);
	assert(!hasComponent(self, e, componentId));
	immutable size = elementSize == ecrs.storage.Storage.invalid ? ecrs.registry.lookupSize(componentId) : elementSize;
	auto storage = getStorage(self, componentId, size);
	if (storage is null) return null;
	return ecrs.storage.add(*storage, componentId, self.indexTable, e);
}

/// Ditto, for component `(T, unique)`, which starts as `T.init`. Returns null also if `T` cannot be registered.
///
/// Examples:
/// ---
/// static struct Position { float x = 1, y = 2; }
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// Position* p = addComponent!Position(ctx, e);
/// assert(p !is null && p.y == 2);
/// ---
template addComponent(T, size_t unique = 0) {
	T* addComponent(ref Context self, EntityId e) {
		assert(!inParallel(self), structuralChange);
		assert(!.hasComponent!(T, unique)(self, e));
		auto storage = .getStorage!(T, unique)(self);
		if (storage is null) return null;
		return ecrs.storage.add!(T, unique)(*storage, self.indexTable, e);
	}
}

/// Removes entity `e`'s component `componentId`, which it must have, ending its lifetime.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// immutable id = ecrs.registry.componentId!int();
/// assert(addComponent(ctx, e, id) !is null);
/// removeComponent(ctx, e, id);
/// assert(!hasComponent(ctx, e, id));
/// ---
void removeComponent(ref Context self, EntityId e, size_t componentId) {
	assert(!inParallel(self), structuralChange);
	assert(hasComponent(self, e, componentId));
	cast(void) ecrs.storage.remove(existingStorage(self, componentId), componentId, self.indexTable, e);
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// assert(addComponent!int(ctx, e) !is null);
/// removeComponent!int(ctx, e);
/// assert(!hasComponent!int(ctx, e));
/// ---
template removeComponent(T, size_t unique = 0) {
	void removeComponent(ref Context self, EntityId e) {
		.removeComponent(self, e, ecrs.registry.componentId!(T, unique)());
	}
}
/// Removes component `componentId` from every entity that has it, ending each one's lifetime. It cannot fail.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// immutable id = ecrs.registry.componentId!int();
/// assert(addComponent(ctx, e, id) !is null);
/// clearComponent(ctx, id);
/// assert(!hasComponent(ctx, e, id));
/// ---
void clearComponent(ref Context self, size_t componentId) @trusted {
	assert(!inParallel(self), structuralChange);
	if (!hasStorage(self, componentId)) return;
	auto storage = &self.storages[componentId];
	// Descending, so popping the last slot never skips an owner.
	foreach_reverse (slot; 0 .. ecrs.storage.size(*storage)) {
		immutable slotOwner = ecrs.storage.owner(*storage, slot);
		if (slotOwner != invalidEntity)
			cast(void) ecrs.storage.remove(*storage, componentId, self.indexTable, slotOwner);
	}
}

/// Entity `e`'s component `componentId`, which it must have. `elementSize`, unless `Storage.invalid`, is checked against the storage's.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// immutable id = ecrs.registry.componentId!int();
/// void* added = addComponent(ctx, e, id);
/// assert(getComponent(ctx, e, id) is added);
/// ---
void* getComponent(ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.invalid) @trusted {
	assert(hasComponent(self, e, componentId));
	auto storage = &existingStorage(self, componentId);
	assert(elementSize == ecrs.storage.Storage.invalid || elementSize == storage.elementSize);
	return ecrs.storage.get(*storage, self.indexTable[e][componentId]);
}

/// Ditto
const(void)* getComponent(const ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.invalid) @trusted {
	assert(hasComponent(self, e, componentId));
	auto storage = &existingStorage(self, componentId);
	assert(elementSize == ecrs.storage.Storage.invalid || elementSize == storage.elementSize);
	return ecrs.storage.get(*storage, self.indexTable[e][componentId]);
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// *addComponent!int(ctx, e) = 3;
/// assert(getComponent!int(ctx, e) == 3);
/// ---
template getComponent(T, size_t unique = 0) {
	ref T getComponent(ref Context self, EntityId e) @trusted {
		return *cast(T*) .getComponent(self, e, ecrs.registry.componentId!(T, unique)(), T.sizeof);
	}
	ref const(T) getComponent(const ref Context self, EntityId e) @trusted {
		return *cast(const(T)*) .getComponent(self, e, ecrs.registry.componentId!(T, unique)(), T.sizeof);
	}
}

/// Entity `e`'s component `componentId`, added as `addComponent` would if `e` lacks it.
///
/// Returns null if adding fails, leaving `e` without the component.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// immutable id = ecrs.registry.componentId!int();
/// void* p = getOrAddComponent(ctx, e, id);
/// assert(p !is null && getOrAddComponent(ctx, e, id) is p);
/// ---
void* getOrAddComponent(ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.invalid) {
	if (hasComponent(self, e, componentId)) return getComponent(self, e, componentId, elementSize);
	return addComponent(self, e, componentId, elementSize);
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId e = addEntity(ctx);
/// int* p = getOrAddComponent!int(ctx, e);
/// assert(p !is null && getOrAddComponent!int(ctx, e) is p);
/// ---
template getOrAddComponent(T, size_t unique = 0) {
	T* getOrAddComponent(ref Context self, EntityId e) {
		if (.hasComponent!(T, unique)(self, e)) return &.getComponent!(T, unique)(self, e);
		return .addComponent!(T, unique)(self, e);
	}
}


/// Registers a holder of entity ids outside the store, so every renumbering rewrites it too. `userData` is passed back to `fn` unchanged.
///
/// Returns false if allocation fails, registering nothing.
///
/// Examples:
/// ---
/// static void onRemap(void*, const(EntityId)[]) @nogc nothrow {}
/// Context ctx = create();
/// scope(exit) free(ctx);
/// assert(addRemapHook(ctx, &onRemap, null));
/// ---
bool addRemapHook(ref Context self, RemapHookFunction fn, void* userData) @trusted {
	assert(!inParallel(self), structuralChange);
	return fp.dynarray.pushBack(self.remapHooks, RemapHook(fn, userData));
}

/// Unregisters the hook added with exactly `fn` and `userData`, returning false if there is none.
///
/// Examples:
/// ---
/// static void onRemap(void*, const(EntityId)[]) @nogc nothrow {}
/// Context ctx = create();
/// scope(exit) free(ctx);
/// assert(addRemapHook(ctx, &onRemap, null));
/// assert(removeRemapHook(ctx, &onRemap, null));
/// assert(!removeRemapHook(ctx, &onRemap, null));
/// ---
bool removeRemapHook(ref Context self, RemapHookFunction fn, void* userData) @trusted {
	assert(!inParallel(self), structuralChange);
	foreach (i; 0 .. fp.dynarray.length(self.remapHooks))
		if (self.remapHooks[i].fn is fn && self.remapHooks[i].userData is userData) {
			cast(void) fp.dynarray.removeAt(self.remapHooks, i);
			return true;
		}
	return false;
}


// Renumbers every holder at once: the index lists, storage owners, components with a remap hook, the freelist and external hooks.
private bool renumber(ref Context self, const(size_t)[] order, const(EntityId)[] remap) @trusted {
	assert(!inParallel(self), structuralChange);
	auto table = self.indexTable;
	// The only step that can fail goes first, so a failure leaves every holder untouched.
	if (!ecrs.storage.applyPermutation(order, (a, b) {
		auto t = table[a];
		table[a] = table[b];
		table[b] = t;
	})) return false;

	foreach (id; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[id].elementSize != ecrs.storage.Storage.invalid)
			ecrs.storage.relabel(self.storages[id], remap);
	foreach (i; 0 .. fp.dynarray.length(self.freelist))
		self.freelist[i] = remap[self.freelist[i]];
	foreach (i; 0 .. fp.dynarray.length(self.remapHooks))
		self.remapHooks[i].fn(self.remapHooks[i].userData, remap);
	return true;
}

/// Renumbers entities, `order[i]` being the entity that becomes `i`, over the whole entity table, freed ids included. Entity 0 must stay put, so `invalidEntity` keeps its meaning. Every holder of an entity id is rewritten in the same step: component owners, components whose type has a remap hook, the freelist and remap hooks. No component moves, so their addresses survive.
///
/// Returns false if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId a = addEntity(ctx), b = addEntity(ctx);
/// *addComponent!int(ctx, a) = 10;
/// immutable size_t[3] order = [0, 2, 1];
/// assert(reorderEntities(ctx, order[]));
/// assert(getComponent!int(ctx, b) == 10);
/// ---
bool reorderEntities(ref Context self, const(size_t)[] order) @trusted {
	assert(order.length == fp.dynarray.length(self.indexTable));
	assert(order.length == 0 || order[0] == invalidEntity);
	auto remap = ecrs.storage.buildRemap(order);
	if (remap is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(remap, 0);
	return renumber(self, order, remap[0 .. order.length]);
}

/// Exchanges the ids of entities `a` and `b`, `b` defaulting to the last slot of the entity table, as `reorderEntities` does.
///
/// Returns false if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId a = addEntity(ctx), b = addEntity(ctx);
/// *addComponent!int(ctx, a) = 10;
/// assert(swapEntities(ctx, a, b));
/// assert(getComponent!int(ctx, b) == 10);
/// ---
bool swapEntities(ref Context self, EntityId a, EntityId b = EntityId.max) @trusted {
	immutable n = fp.dynarray.length(self.indexTable);
	immutable resolvedB = b == EntityId.max ? cast(EntityId)(n - 1) : b;
	assert(a < n && resolvedB < n);
	auto order = cast(size_t*) fp.pointer.allocFunction(null, n * size_t.sizeof);
	if (order is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(order, 0);
	foreach (i; 0 .. n) order[i] = i;
	order[a] = resolvedB;
	order[resolvedB] = a;
	return reorderEntities(self, order[0 .. n]);
}

/// Renumbers the live entities to `0 .. entityCount` in their current order and drops the freed ids from the table, emptying the freelist. A reference still naming a freed entity becomes `invalidEntity` rather than an id a later `addEntity` hands out again.
///
/// Returns false if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId a = addEntity(ctx), b = addEntity(ctx);
/// *addComponent!int(ctx, b) = 10;
/// assert(removeEntity(ctx, a));
/// assert(compact(ctx));
/// assert(getComponent!int(ctx, 1) == 10);
/// ---
bool compact(ref Context self) @trusted {
	immutable n = fp.dynarray.length(self.indexTable);
	immutable freedCount = fp.dynarray.length(self.freelist);
	if (freedCount == 0) return true;

	auto freed = cast(bool*) fp.pointer.allocFunction(null, n * bool.sizeof);
	if (freed is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(freed, 0);
	foreach (e; 0 .. n) freed[e] = false;
	foreach (i; 0 .. freedCount) freed[self.freelist[i]] = true;

	auto order = cast(size_t*) fp.pointer.allocFunction(null, n * size_t.sizeof);
	if (order is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(order, 0);
	size_t live = 0, dead = n - freedCount;
	foreach (e; 0 .. n)
		order[freed[e] ? dead++ : live++] = e;
	assert(order[0] == invalidEntity);

	auto remap = ecrs.storage.buildRemap(order[0 .. n]);
	if (remap is null) return false;
	scope(exit) cast(void) fp.pointer.allocFunction(remap, 0);
	foreach (e; 0 .. n)
		if (freed[e]) remap[e] = invalidEntity;

	if (!renumber(self, order[0 .. n], remap[0 .. n])) return false;
	// The tail now holds the freed ids, whose index lists removeEntity released.
	cast(void) fp.dynarray.popBackCount(self.indexTable, freedCount);
	fp.dynarray.clear(self.freelist);
	return true;
}


/// Sorts each of the listed components' storages into entity order. It moves components, so it invalidates pointers into those storages.
///
/// Returns false if allocation fails for any of them; each storage it could not sort is left as it was.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// EntityId a = addEntity(ctx), b = addEntity(ctx);
/// *addComponent!int(ctx, b) = 2;
/// *addComponent!int(ctx, a) = 1;
/// assert(makeMonotonic!(int, short)(ctx));
/// assert(ecrs.storage.owners(*getStorage!int(ctx)) == [a, b]);
/// ---
template makeMonotonic(Ts...) if (Ts.length != 1 || !is(typeof(Ts[0]) : size_t)) {
	bool makeMonotonic(ref Context self) {
		assert(!inParallel(self), structuralChange);
		bool sorted = true;
		static foreach (T; Ts) {{
			auto storage = .getStorage!T(self);
			sorted &= storage !is null && ecrs.storage.sortMonotonic!T(*storage, self.indexTable);
		}}
		return sorted;
	}
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// assert(makeMonotonic!(int, 1)(ctx));
/// ---
template makeMonotonic(T, size_t unique = 0) {
	bool makeMonotonic(ref Context self) {
		assert(!inParallel(self), structuralChange);
		auto storage = .getStorage!(T, unique)(self);
		return storage !is null && ecrs.storage.sortMonotonic!(T, unique)(*storage, self.indexTable);
	}
}

/// Ditto, for component `componentId`; one no entity ever had has nothing to sort. `elementSize`, unless `Storage.invalid`, is checked against the storage's.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// assert(makeMonotonic(ctx, ecrs.registry.componentId!int()));
/// ---
bool makeMonotonic(ref Context self, size_t componentId, size_t elementSize = ecrs.storage.Storage.invalid) @trusted {
	assert(!inParallel(self), structuralChange);
	if (!hasStorage(self, componentId)) return true;
	assert(elementSize == ecrs.storage.Storage.invalid || elementSize == self.storages[componentId].elementSize);
	return ecrs.storage.sortMonotonic(self.storages[componentId], componentId, self.indexTable);
}

/// Sorts every component storage into entity order, as `makeMonotonic` does.
///
/// Returns false if allocation fails for any storage; each one it could not sort is left as it was.
///
/// Examples:
/// ---
/// Context ctx = create();
/// scope(exit) free(ctx);
/// assert(makeAllMonotonic(ctx));
/// ---
bool makeAllMonotonic(ref Context self) @trusted {
	assert(!inParallel(self), structuralChange);
	bool sorted = true;
	foreach (id; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[id].elementSize != ecrs.storage.Storage.invalid)
			sorted &= ecrs.storage.sortMonotonic(self.storages[id], id, self.indexTable);
	return sorted;
}


unittest {
	// Entities: creation, the reserved entity 0, freelist reuse and iteration.
	auto ctx = create();
	scope(exit) free(ctx);
	assert(entityCount(ctx) == 1);

	EntityId a = addEntity(ctx);
	EntityId b = addEntity(ctx);
	size_t count = 0;
	foreach (e; entities(ctx)) ++count;
	assert(count == 3);

	assert(removeEntity(ctx, a));
	count = 0;
	foreach (e; entities(ctx)) {
		assert(e != a);
		++count;
	}
	assert(count == 2 && entityCount(ctx) == 2);
	assert(addEntity(ctx) == a);

	// A context whose creation could not allocate reserves entity 0 on first use.
	Context empty;
	scope(exit) free(empty);
	assert(entityCount(empty) == 0);
	assert(addEntity(empty) == 1);
	assert(entityCount(empty) == 2);
	cast(void) b;
}

unittest {
	// Components through the typed forms.
	struct Vec2 { float x = 0, y = 0; }
	struct Counter { int value; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e1 = addEntity(ctx);
	*addComponent!Vec2(ctx, e1) = Vec2(1, 2);
	EntityId e2 = addEntity(ctx);
	*addComponent!Vec2(ctx, e2) = Vec2(3, 4);
	EntityId e3 = addEntity(ctx);
	*addComponent!Vec2(ctx, e3) = Vec2(5, 6);
	assert(entityCount(ctx) == 4);
	assert(hasComponent!Vec2(ctx, e1));

	assert(removeEntity(ctx, e2));
	assert(entityCount(ctx) == 3);

	size_t seen = 0;
	float xsum = 0;
	foreach (e; entities(ctx))
		if (hasComponent!Vec2(ctx, e)) {
			xsum += getComponent!Vec2(ctx, e).x;
			++seen;
		}
	assert(seen == 2);
	assert(xsum == 1 + 5);

	assert(!hasComponent!Counter(ctx, e1));
	auto c = getOrAddComponent!Counter(ctx, e1);
	c.value = 5;
	assert(getOrAddComponent!Counter(ctx, e1) is c);
	assert(getComponent!Counter(ctx, e1).value == 5);
	removeComponent!Counter(ctx, e1);
	assert(!hasComponent!Counter(ctx, e1));
}

unittest {
	// Components through the runtime-id forms.
	struct Flag { int v; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e = addEntity(ctx);
	immutable id = ecrs.registry.componentId!Flag();

	assert(!hasComponent(ctx, e, id));
	auto p = getOrAddComponent(ctx, e, id);
	(cast(Flag*) p).v = 42;
	assert(hasComponent(ctx, e, id));
	assert(getOrAddComponent(ctx, e, id) is p);
	assert((cast(Flag*) getComponent(ctx, e, id)).v == 42);

	removeComponent(ctx, e, id);
	assert(!hasComponent(ctx, e, id));
	auto p3 = addComponent(ctx, e, id, Flag.sizeof);
	assert((cast(Flag*) p3).v == 0);

	const(Context)* constCtx = &ctx;
	assert(getStorage(*constCtx, id, Flag.sizeof) !is null);
	assert(getStorage(*constCtx, ecrs.registry.componentId!(Flag, 1)()) is null);

	// clearComponent empties one storage, past a hole, and leaves other components alone; generation advances.
	struct Other { int v; }
	immutable other = ecrs.registry.componentId!Other();
	assert(generation(ctx, other) == 0);
	clearComponent(ctx, other); // no storage yet: nothing to clear
	EntityId[4] marked;
	foreach (ref m; marked) {
		m = addEntity(ctx);
		assert(addComponent(ctx, m, id) !is null && addComponent!Other(ctx, m) !is null);
	}
	removeComponent(ctx, marked[1], id);
	immutable g = generation(ctx, id);
	clearComponent(ctx, id);
	assert(generation(ctx, id) > g);
	assert(ecrs.storage.empty(*getStorage(*constCtx, id)));
	foreach (m; marked)
		assert(!hasComponent(ctx, m, id) && hasComponent!Other(ctx, m));
}

unittest {
	// Every allocation failure leaves the context as it was.
	struct Payload { int value; }
	auto ctx = create();
	scope(exit) free(ctx);

	Context unreserved;
	ecrs.registry.failAllocationsAfter(0);
	assert(addEntity(unreserved) == invalidEntity);
	ecrs.registry.restoreAllocations();
	assert(entityCount(unreserved) == 0);

	EntityId e = addEntity(ctx);
	immutable id = ecrs.registry.componentId!Payload();
	foreach (n; 0 .. 16) {
		ecrs.registry.failAllocationsAfter(n);
		auto p = addComponent!Payload(ctx, e);
		ecrs.registry.restoreAllocations();
		if (p !is null) break;
		assert(!hasComponent(ctx, e, id));
	}
	assert(hasComponent(ctx, e, id));

	EntityId other = addEntity(ctx);
	ecrs.registry.failAllocationsAfter(0);
	assert(!removeEntity(ctx, e));
	assert(!swapEntities(ctx, e, other));
	ecrs.registry.restoreAllocations();
	assert(hasComponent(ctx, e, id) && entityCount(ctx) == 3);

	assert(removeEntity(ctx, other));
	ecrs.registry.failAllocationsAfter(0);
	assert(!compact(ctx));
	ecrs.registry.restoreAllocations();
	assert(fp.dynarray.length(ctx.freelist) == 1);
	assert(compact(ctx));
	assert(fp.dynarray.length(ctx.freelist) == 0);

	// The remap allocates first, so the second allocation failing reaches the permutation itself.
	assert(fp.dynarray.length(ctx.indexTable) == 2);
	immutable size_t[2] order = [0, 1];
	ecrs.registry.failAllocationsAfter(1);
	assert(!reorderEntities(ctx, order[]));
	ecrs.registry.restoreAllocations();
	assert(hasComponent(ctx, e, id));
}

unittest {
	// Const access, swapEntities, reorderEntities and makeMonotonic.
	struct Val { int v; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e1 = addEntity(ctx);
	*addComponent!Val(ctx, e1) = Val(30);
	EntityId e2 = addEntity(ctx);
	*addComponent!Val(ctx, e2) = Val(10);
	EntityId e3 = addEntity(ctx);
	*addComponent!Val(ctx, e3) = Val(20);

	const(Context)* constCtx = &ctx;
	assert(getComponent!Val(*constCtx, e1).v == 30);

	assert(swapEntities(ctx, e1, e3));
	assert(getComponent!Val(ctx, e1).v == 20);
	assert(getComponent!Val(ctx, e3).v == 30);
	assert(swapEntities(ctx, e1, e3));

	// With one entity named, the other is the last slot.
	immutable lastId = cast(EntityId)(fp.dynarray.length(ctx.indexTable) - 1);
	assert(lastId == e3);
	assert(swapEntities(ctx, e1));
	assert(getComponent!Val(ctx, lastId).v == 30);
	assert(swapEntities(ctx, e1));

	immutable size_t[4] order = [0, 3, 2, 1];
	assert(reorderEntities(ctx, order[]));
	assert(getComponent!Val(ctx, 1).v == 20);
	assert(getComponent!Val(ctx, 2).v == 10);
	assert(getComponent!Val(ctx, 3).v == 30);

	// A 3-cycle pins down that `order[i]` is the entity ending up at i, not where i goes.
	immutable size_t[4] cycle = [0, 3, 1, 2];
	assert(reorderEntities(ctx, cycle[]));
	assert(getComponent!Val(ctx, 1).v == 30);
	assert(getComponent!Val(ctx, 2).v == 20);
	assert(getComponent!Val(ctx, 3).v == 10);

	assert(ecrs.storage.liveCount(*getStorage(*constCtx, ecrs.registry.componentId!Val(), Val.sizeof)) == 3);

	struct NeverAdded { int v; }
	assert(makeMonotonic(ctx, ecrs.registry.componentId!NeverAdded()));
	assert(makeMonotonic(ctx, ecrs.registry.componentId!Val()));
	assert(makeAllMonotonic(ctx));
	auto storage = getStorage!Val(ctx);
	assert(ecrs.storage.owners(*storage) == [1, 2, 3]);
}

unittest {
	// Lifetimes end once per component, whichever way it goes: removeComponent, removeEntity, or free for what is left.
	static struct Owned {
		int value;
		__gshared int finalized;
		void finalize() @nogc nothrow {
			if (value != 0) ++finalized;
			value = 0;
		}
	}
	Owned.finalized = 0;
	{
		auto ctx = create();
		scope(exit) free(ctx);

		EntityId e1 = addEntity(ctx);
		EntityId e2 = addEntity(ctx);
		EntityId e3 = addEntity(ctx);
		addComponent!Owned(ctx, e1).value = 1;
		addComponent!Owned(ctx, e2).value = 1;
		addComponent!Owned(ctx, e3).value = 1;

		removeComponent!Owned(ctx, e1);
		assert(Owned.finalized == 1);
		assert(removeEntity(ctx, e2));
		assert(Owned.finalized == 2);
	}
	assert(Owned.finalized == 3);
}

unittest {
	// A renumbering reaches every holder without the caller naming any, past a freed entity in the table.
	static import ecrs.relation;
	alias Next = ecrs.relation.Relation!1;
	alias Many = ecrs.relation.Relation!(ecrs.relation.dynamicExtent);
	alias Typed = ecrs.relation.Relation!(1, true);

	static struct Memo {
		EntityId cached;
		static void remap(void* self, const(EntityId)[] remap) @nogc nothrow {
			auto memo = cast(Memo*) self;
			memo.cached = remap[memo.cached];
		}
	}

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e1 = addEntity(ctx);
	EntityId e2 = addEntity(ctx);
	EntityId e3 = addEntity(ctx);
	EntityId gone = addEntity(ctx);
	assert(removeEntity(ctx, gone));

	addComponent!Next(ctx, e1).related[0] = e2;
	addComponent!Next(ctx, e2).related[0] = e3;
	addComponent!Next(ctx, e3).related[0] = invalidEntity;
	assert(fp.dynarray.pushBack(addComponent!Many(ctx, e1).related, e3));
	addComponent!Typed(ctx, e2).related[0] = ecrs.relation.Term(e1);

	Memo memo = Memo(e3);
	assert(addRemapHook(ctx, &Memo.remap, &memo));

	// 1 -> 3, 2 -> 1, 3 -> 2; the freed 4 stays where it is.
	immutable size_t[5] order = [0, 2, 3, 1, 4];
	assert(reorderEntities(ctx, order[]));

	assert(getComponent!Next(ctx, 3).related[0] == 1);
	assert(getComponent!Next(ctx, 1).related[0] == 2);
	assert(getComponent!Next(ctx, 2).related[0] == invalidEntity);
	assert(getComponent!Many(ctx, 3).related[0] == 2);
	assert(getComponent!Typed(ctx, 1).related[0].constant == 3);
	assert(ecrs.storage.owner(*getStorage!Next(ctx), ctx.indexTable[3][ecrs.registry.componentId!Next()]) == 3);
	assert(memo.cached == 2);
	assert(ctx.freelist[0] == 4);

	assert(removeRemapHook(ctx, &Memo.remap, &memo));
	assert(!removeRemapHook(ctx, &Memo.remap, &memo));
	assert(swapEntities(ctx, 1, 2));
	assert(memo.cached == 2);
	assert(getComponent!Next(ctx, 3).related[0] == 2);
}

unittest {
	// compact renumbers live entities densely in order, shrinks the table, empties the freelist and invalidates references to freed entities.
	static import ecrs.relation;
	alias Next = ecrs.relation.Relation!1;
	struct Val { int v; }

	auto ctx = create();
	scope(exit) free(ctx);

	foreach (i; 1 .. 6) {
		EntityId e = addEntity(ctx);
		*addComponent!Val(ctx, e) = Val(i * 10);
	}
	addComponent!Next(ctx, 5).related[0] = 3;
	addComponent!Next(ctx, 1).related[0] = 4;
	assert(removeEntity(ctx, 2));
	assert(removeEntity(ctx, 4));

	assert(compact(ctx));
	assert(fp.dynarray.length(ctx.indexTable) == 4);
	assert(fp.dynarray.length(ctx.freelist) == 0);
	assert(entityCount(ctx) == 4);
	assert(getComponent!Val(ctx, 1).v == 10);
	assert(getComponent!Val(ctx, 2).v == 30);
	assert(getComponent!Val(ctx, 3).v == 50);
	assert(getComponent!Next(ctx, 3).related[0] == 2);
	assert(getComponent!Next(ctx, 1).related[0] == invalidEntity);
	assert(addEntity(ctx) == 4);

	assert(compact(ctx)); // nothing freed: a no-op
	assert(fp.dynarray.length(ctx.indexTable) == 5);
}

unittest {
	// A component's address survives more of its type, new component types relocating the storage table, and other removals.
	struct Payload { int value; }
	struct LateA { int x; }
	struct LateB { long y; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId first = addEntity(ctx);
	Payload* held = addComponent!Payload(ctx, first);
	held.value = 7;

	foreach (i; 0 .. 3000) {
		EntityId e = addEntity(ctx);
		addComponent!Payload(ctx, e).value = i;
		if (i == 1000) assert(addComponent!LateA(ctx, e) !is null);
		if (i == 2000) assert(addComponent!LateB(ctx, e) !is null);
		if (i % 3 == 0) removeComponent!Payload(ctx, e);
	}
	assert(&getComponent!Payload(ctx, first) is held);
	assert(held.value == 7);
}
