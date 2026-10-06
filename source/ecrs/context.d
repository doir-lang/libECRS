/// The entity/component database (`Context`). Ported from context.hpp.
///
/// Styled after `fp.dynarray`/`bc.mutex`/`ecrs.storage`: `Context` is plain
/// data with no methods of its own, and every operation on it is a free
/// function taking it by `ref` - which also puts them all under the
/// module-level `@nogc nothrow:` below, since that does not reach into a
/// struct body. There is deliberately no `Entity` handle wrapping a
/// thread-local "current context" - callers just pass the `Context` (and an
/// `EntityId` where relevant) explicitly to every free function below.
module ecrs.context;

import core.atomic : atomicLoad, atomicOp;

static import fp.dynarray;
import fp.pointer : allocFunction;

import ecrs.registry : componentId, lookupComponentSize, lookupComponentHooks;
import ecrs.storage;

@nogc nothrow:


private bool freelistContains(inout size_t* freelist, size_t value) @trusted {
	if (freelist is null) return false;
	immutable n = fp.dynarray.length(cast(size_t*) freelist);
	foreach (i; 0 .. n)
		if ((cast(size_t*) freelist)[i] == value) return true;
	return false;
}

/// A lazily-populated view over the live (non-freelisted) entities of a
/// `Context`, usable directly in a `foreach`.
struct EntityRange {
	private const(Context)* ctx;
	private size_t index;

	private this(const(Context)* ctx, size_t startIndex) @nogc nothrow {
		this.ctx = ctx;
		index = startIndex;
		skipFreed();
	}

	private void skipFreed() @trusted @nogc nothrow {
		while (index < fp.dynarray.length(ctx.entityComponentIndices) && freelistContains(ctx.freelist, index))
			index++;
	}

	bool empty() const @trusted @nogc nothrow { return index >= fp.dynarray.length(ctx.entityComponentIndices); }
	EntityId front() const @nogc nothrow { return cast(EntityId) index; }
	void popFront() @nogc nothrow { index++; skipFreed(); }
}


/// A holder of entity ids that lives outside the store - a query memo table,
/// a comptime heap of `std.meta.entity` values - rewritten by every
/// renumbering alongside the components. `remap[old]` is the id `old` becomes.
alias RemapHookFunction = void function(void* userData, const(EntityId)[] remap) @nogc nothrow;

private struct RemapHook {
	RemapHookFunction fn;
	void* userData;
}


/// The entity/component database: owns one `ComponentStorage` per
/// registered component id, plus the per-entity index tables mapping entity
/// -> component slot.
///
/// Deliberately plain data (no constructor, no methods, no disabled
/// postblit, no destructor): ownership is managed explicitly via the free
/// functions below - `free(ctx)` is the only thing that should ever release
/// what a `Context` owns. Unlike the C++ version (which needed a separate
/// `fp::auto_free<context>` wrapper for RAII), a genuine D `scope(exit)
/// free(ctx);` at the point of creation covers the same ground.
///
/// Concurrency: any number of threads may read at once, and may write
/// existing components of distinct entities. Structural changes - adding or
/// removing entities, components, storages or remap hooks, renumbering,
/// sorting - need exclusive access. Inside an `ecrs.system` parallel
/// combinator they fail an assert rather than race, whatever the pool size.
struct Context {
	private ComponentStorage* storages = null;
	EntityComponentIndices entityComponentIndices = null;
	size_t* freelist = null;
	private RemapHook* remapHooks = null;
	private size_t parallelDepth = 0; // atomic; nonzero while a parallel system runs
}

/// True while an `ecrs.system` parallel combinator is running on `self`.
bool inParallel(const ref Context self) @trusted {
	return atomicLoad(*cast(shared(const(size_t))*) &self.parallelDepth) != 0;
}
package void enterParallel(ref Context self) @trusted {
	atomicOp!"+="(*cast(shared(size_t)*) &self.parallelDepth, 1);
}
package void exitParallel(ref Context self) @trusted {
	atomicOp!"-="(*cast(shared(size_t)*) &self.parallelDepth, 1);
}

private enum string structuralChange = "ecrs: structural change inside a parallel system; make it after the pass";

/// The storage for `componentIdVal`, which must already exist. Unlike
/// `getStorage` it needs no element size, so it never consults the registry.
private ref ComponentStorage existingStorage(ref Context self, size_t componentIdVal) @trusted {
	assert(fp.dynarray.length(self.storages) > componentIdVal);
	assert(self.storages[componentIdVal].elementSize != ComponentStorage.invalid);
	return self.storages[componentIdVal];
}
private ref const(ComponentStorage) existingStorage(const ref Context self, size_t componentIdVal) @trusted {
	assert(fp.dynarray.length(self.storages) > componentIdVal);
	assert(self.storages[componentIdVal].elementSize != ComponentStorage.invalid);
	return self.storages[componentIdVal];
}

/// Constructs a context with the permanently-reserved invalid entity (id 0)
/// already allocated. Use this instead of `Context.init` directly.
Context create() {
	Context c;
	cast(void) addEntity(c);
	return c;
}

void free(ref Context self) @trusted {
	foreach (i; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[i].elementSize != ComponentStorage.invalid)
			ecrs.storage.free(self.storages[i]);
	fp.dynarray.free(self.storages);
	foreach (i; 0 .. fp.dynarray.length(self.entityComponentIndices))
		fp.dynarray.free(self.entityComponentIndices[i]);
	fp.dynarray.free(self.entityComponentIndices);
	fp.dynarray.free(self.freelist);
	fp.dynarray.free(self.remapHooks);
}

/// The storage for `componentIdVal`, created on first use with the hooks its
/// type registered (`ecrs.registry.ComponentHooks`).
ref ComponentStorage getStorage(ref Context self, size_t componentIdVal, size_t elementSize) @trusted {
	if (fp.dynarray.length(self.storages) <= componentIdVal || self.storages[componentIdVal].elementSize == ComponentStorage.invalid)
		assert(!inParallel(self), structuralChange);
	while (fp.dynarray.length(self.storages) <= componentIdVal)
		fp.dynarray.pushBack(self.storages, ComponentStorage.init);
	if (self.storages[componentIdVal].elementSize == ComponentStorage.invalid) {
		immutable hooks = lookupComponentHooks(componentIdVal);
		self.storages[componentIdVal] = ecrs.storage.create(elementSize, hooks.finalize, hooks.remap);
	}
	return self.storages[componentIdVal];
}
ref const(ComponentStorage) getStorage(const ref Context self, size_t componentIdVal, size_t elementSize) @trusted {
	return existingStorage(self, componentIdVal);
}
template getStorage(Tcomponent, size_t Unique = 0) {
	ref ComponentStorage getStorage(ref Context self) @nogc nothrow {
		return .getStorage(self, componentId!(Tcomponent, Unique)(), Tcomponent.sizeof);
	}
}

size_t entityCount(const ref Context self) @trusted {
	return fp.dynarray.length(self.entityComponentIndices) - fp.dynarray.length(self.freelist);
}

EntityId addEntity(ref Context self) @trusted {
	assert(!inParallel(self), structuralChange);
	if (fp.dynarray.length(self.freelist) > 0) {
		immutable e = *fp.dynarray.back(self.freelist);
		fp.dynarray.popBack(self.freelist);
		return cast(EntityId) e;
	}
	immutable out_ = cast(EntityId) fp.dynarray.length(self.entityComponentIndices);
	fp.dynarray.pushBack(self.entityComponentIndices, cast(ComponentIndexList) null);
	return out_;
}

void removeEntity(ref Context self, EntityId e) @trusted {
	assert(!inParallel(self), structuralChange);
	assert(e < fp.dynarray.length(self.entityComponentIndices));
	auto indices = self.entityComponentIndices[e];
	foreach (componentIdVal; 0 .. fp.dynarray.length(indices))
		if (indices[componentIdVal] != ComponentStorage.invalid)
			ecrs.storage.remove(self.storages[componentIdVal], componentIdVal, self.entityComponentIndices, e);
	fp.dynarray.free(self.entityComponentIndices[e]);
	fp.dynarray.pushBack(self.freelist, cast(size_t) e);
}

bool hasComponent(const ref Context self, EntityId e, size_t componentIdVal) @trusted {
	return self.entityComponentIndices !is null
		&& e < fp.dynarray.length(self.entityComponentIndices)
		&& self.entityComponentIndices[e] !is null
		&& fp.dynarray.length(self.entityComponentIndices[e]) > componentIdVal
		&& self.entityComponentIndices[e][componentIdVal] != ComponentStorage.invalid;
}
template hasComponent(Tcomponent, size_t Unique = 0) {
	bool hasComponent(const ref Context self, EntityId e) @nogc nothrow {
		return .hasComponent(self, e, componentId!(Tcomponent, Unique)());
	}
}

/// Type-erased: the new slot is zero-filled rather than constructed,
/// since there's no compile-time type here to initialize it properly.
/// Prefer the templated overload below whenever `Tcomponent` is known.
///
/// The component's address is stable until it is removed or a reorder/sort
/// (`reorderEntities`, `makeMonotonic`, ...) moves it; adding other
/// components, of any type, never does.
void* addComponent(ref Context self, EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted {
	assert(!inParallel(self), structuralChange);
	assert(!hasComponent(self, e, componentIdVal));
	immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
	return ecrs.storage.add(getStorage(self, componentIdVal, sz), componentIdVal, self.entityComponentIndices, e);
}
template addComponent(Tcomponent, size_t Unique = 0) {
	ref Tcomponent addComponent(ref Context self, EntityId e) @trusted @nogc nothrow {
		assert(!inParallel(self), structuralChange);
		assert(!.hasComponent!(Tcomponent, Unique)(self, e));
		// NOTE: explicit module qualification (rather than UFCS/plain calls)
		// is required here - calling a name that has both a plain and a
		// template overload with an *explicit* template argument, across a
		// module boundary (this is ecrs.context calling into ecrs.storage),
		// fails to resolve in the D frontend otherwise ("no overload matches"),
		// apparently a limitation in how such mixed overload sets are looked
		// up across modules. Confirmed with a minimal repro during porting.
		return ecrs.storage.add!(Tcomponent, Unique)(.getStorage!(Tcomponent, Unique)(self), self.entityComponentIndices, e);
	}
}

void removeComponent(ref Context self, EntityId e, size_t componentIdVal) @trusted {
	assert(!inParallel(self), structuralChange);
	assert(hasComponent(self, e, componentIdVal));
	ecrs.storage.remove(existingStorage(self, componentIdVal), componentIdVal, self.entityComponentIndices, e);
}
template removeComponent(Tcomponent, size_t Unique = 0) {
	void removeComponent(ref Context self, EntityId e) @nogc nothrow {
		.removeComponent(self, e, componentId!(Tcomponent, Unique)());
	}
}

/// `elementSize`, if given, is only checked against the storage's.
void* getComponent(ref Context self, EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted {
	assert(hasComponent(self, e, componentIdVal));
	auto storage = &existingStorage(self, componentIdVal);
	assert(elementSize == ComponentStorage.invalid || elementSize == storage.elementSize);
	return (*storage).get(self.entityComponentIndices[e][componentIdVal]);
}
const(void)* getComponent(const ref Context self, EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted {
	assert(hasComponent(self, e, componentIdVal));
	auto storage = &existingStorage(self, componentIdVal);
	assert(elementSize == ComponentStorage.invalid || elementSize == storage.elementSize);
	return (*storage).get(self.entityComponentIndices[e][componentIdVal]);
}
template getComponent(Tcomponent, size_t Unique = 0) {
	ref Tcomponent getComponent(ref Context self, EntityId e) @trusted @nogc nothrow {
		return *cast(Tcomponent*) .getComponent(self, e, componentId!(Tcomponent, Unique)(), Tcomponent.sizeof);
	}
	ref const(Tcomponent) getComponent(const ref Context self, EntityId e) @trusted @nogc nothrow {
		return *cast(const(Tcomponent)*) .getComponent(self, e, componentId!(Tcomponent, Unique)(), Tcomponent.sizeof);
	}
}

void* getOrAddComponent(ref Context self, EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) {
	if (hasComponent(self, e, componentIdVal)) return getComponent(self, e, componentIdVal, elementSize);
	return addComponent(self, e, componentIdVal, elementSize);
}
template getOrAddComponent(Tcomponent, size_t Unique = 0) {
	ref Tcomponent getOrAddComponent(ref Context self, EntityId e) @nogc nothrow {
		if (.hasComponent!(Tcomponent, Unique)(self, e)) return .getComponent!(Tcomponent, Unique)(self, e);
		return .addComponent!(Tcomponent, Unique)(self, e);
	}
}


/// Registers a holder of entity ids outside the store, so every renumbering
/// rewrites it too (`E-Remap`). `userData` is passed back unchanged.
void addRemapHook(ref Context self, RemapHookFunction fn, void* userData) @trusted {
	assert(!inParallel(self), structuralChange);
	fp.dynarray.pushBack(self.remapHooks, RemapHook(fn, userData));
}
/// Returns false if no hook was registered with exactly this pair.
bool removeRemapHook(ref Context self, RemapHookFunction fn, void* userData) @trusted {
	assert(!inParallel(self), structuralChange);
	foreach (i; 0 .. fp.dynarray.length(self.remapHooks))
		if (self.remapHooks[i].fn is fn && self.remapHooks[i].userData is userData) {
			fp.dynarray.removeAt(self.remapHooks, i);
			return true;
		}
	return false;
}

/// One renumbering step over every holder at once: storage owners, each
/// component whose type registered a remap hook, the freelist, external
/// hooks, and the index lists themselves.
private void renumber(ref Context self, const(size_t)[] order, const(EntityId)[] remap) @trusted {
	assert(!inParallel(self), structuralChange);
	foreach (id; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[id].elementSize != ComponentStorage.invalid)
			relabel(self.storages[id], remap);
	foreach (i; 0 .. fp.dynarray.length(self.freelist))
		self.freelist[i] = remap[self.freelist[i]];
	foreach (i; 0 .. fp.dynarray.length(self.remapHooks))
		self.remapHooks[i].fn(self.remapHooks[i].userData, remap);

	auto table = self.entityComponentIndices;
	applyPermutation(order, (a, b) {
		auto tmp = table[a];
		table[a] = table[b];
		table[b] = tmp;
	});
}

/// Renumbers entities: `order[i]` is the entity that becomes `i`, over the
/// whole entity table, freed ids included. Entity 0 must stay put, so that
/// `invalidEntity` keeps its meaning. Every holder of an entity id is
/// rewritten in the same step (`E-Remap`), with nothing for the caller to
/// list. Moves no component data, so component addresses survive.
void reorderEntities(ref Context self, const(size_t)[] order) @trusted {
	assert(order.length == fp.dynarray.length(self.entityComponentIndices));
	assert(order.length == 0 || order[0] == invalidEntity);
	auto remap = buildRemap(order);
	scope(exit) allocFunction(remap, 0);
	renumber(self, order, remap[0 .. order.length]);
}

/// Exchanges two entities' ids. `b` defaults to the last entity slot.
void swapEntities(ref Context self, EntityId a, EntityId b = EntityId.max) @trusted {
	immutable n = fp.dynarray.length(self.entityComponentIndices);
	immutable resolvedB = b == EntityId.max ? cast(EntityId)(n - 1) : b;
	assert(a < n && resolvedB < n);
	auto order = cast(size_t*) allocFunction(null, n * size_t.sizeof);
	scope(exit) allocFunction(order, 0);
	foreach (i; 0 .. n) order[i] = i;
	order[a] = resolvedB;
	order[resolvedB] = a;
	reorderEntities(self, order[0 .. n]);
}

/// Renumbers the live entities to `0 .. entityCount` in their current order
/// and drops the freed ids from the table, leaving the freelist empty. Any
/// reference still naming a freed entity becomes `invalidEntity` rather than
/// an id a later `addEntity` hands out again.
void compact(ref Context self) @trusted {
	immutable n = fp.dynarray.length(self.entityComponentIndices);
	immutable freedCount = fp.dynarray.length(self.freelist);
	if (freedCount == 0) return;

	auto freed = cast(bool*) allocFunction(null, n * bool.sizeof);
	scope(exit) allocFunction(freed, 0);
	foreach (e; 0 .. n) freed[e] = false;
	foreach (i; 0 .. freedCount) freed[self.freelist[i]] = true;

	auto order = cast(size_t*) allocFunction(null, n * size_t.sizeof);
	scope(exit) allocFunction(order, 0);
	size_t live = 0, dead = n - freedCount;
	foreach (e; 0 .. n)
		order[freed[e] ? dead++ : live++] = e;
	assert(order[0] == invalidEntity);

	auto remap = buildRemap(order[0 .. n]);
	scope(exit) allocFunction(remap, 0);
	foreach (e; 0 .. n)
		if (freed[e]) remap[e] = invalidEntity;

	renumber(self, order[0 .. n], remap[0 .. n]);
	// The tail now holds the freed ids, whose index lists removeEntity released.
	fp.dynarray.popBackCount(self.entityComponentIndices, freedCount);
	fp.dynarray.clear(self.freelist);
}


/// Sorts the listed components' storage into entity order. Moves component
/// data, so it invalidates pointers into those storages.
template makeMonotonic(Tcomponents...) if (Tcomponents.length != 1 || !is(typeof(Tcomponents[0]) : size_t)) {
	void makeMonotonic(ref Context self) @nogc nothrow {
		assert(!inParallel(self), structuralChange);
		// See the NOTE in addComponent(Tcomponent, Unique) above: explicit
		// module qualification is required for the cross-module `!T` call.
		static foreach (T; Tcomponents)
			ecrs.storage.sortMonotonic!T(.getStorage!T(self), self.entityComponentIndices);
	}
}
template makeMonotonic(Tcomponent, size_t Unique = 0) {
	void makeMonotonic(ref Context self) @nogc nothrow {
		assert(!inParallel(self), structuralChange);
		ecrs.storage.sortMonotonic!(Tcomponent, Unique)(.getStorage!(Tcomponent, Unique)(self), self.entityComponentIndices);
	}
}
/// Ditto, by id. A component no entity ever had has nothing to sort.
void makeMonotonic(ref Context self, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted {
	assert(!inParallel(self), structuralChange);
	if (fp.dynarray.length(self.storages) <= componentIdVal || self.storages[componentIdVal].elementSize == ComponentStorage.invalid)
		return;
	assert(elementSize == ComponentStorage.invalid || elementSize == self.storages[componentIdVal].elementSize);
	self.storages[componentIdVal].sortMonotonic(componentIdVal, self.entityComponentIndices);
}

void makeAllMonotonic(ref Context self) @trusted {
	assert(!inParallel(self), structuralChange);
	foreach (id; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[id].elementSize != ComponentStorage.invalid)
			self.storages[id].sortMonotonic(id, self.entityComponentIndices);
}

EntityRange entities(const ref Context self) { return EntityRange(&self, 0); }


unittest {
	struct Vec2 { float x = 0, y = 0; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e1 = ctx.addEntity();
	auto c1 = &ctx.addComponent!Vec2(e1);
	c1.x = 1; c1.y = 2;

	EntityId e2 = ctx.addEntity();
	auto c2 = &ctx.addComponent!Vec2(e2);
	c2.x = 3; c2.y = 4;

	EntityId e3 = ctx.addEntity();
	auto c3 = &ctx.addComponent!Vec2(e3);
	c3.x = 5; c3.y = 6;

	// entityCount() includes the permanently-reserved invalid entity 0, so
	// creating a context + 3 real entities counts as 4.
	assert(ctx.entityCount() == 4);
	assert(ctx.hasComponent!Vec2(e1));

	ctx.removeEntity(e2);
	assert(ctx.entityCount() == 3);

	size_t seen = 0;
	float xsum = 0;
	foreach (e; ctx.entities())
		if (ctx.hasComponent!Vec2(e)) {
			xsum += ctx.getComponent!Vec2(e).x;
			seen++;
		}
	assert(seen == 2); // e1 and e3 (e2 was removed, entity 0 never had a Vec2)
	assert(xsum == 1 + 5);
}

unittest {
	// Entity 0 is the permanently-reserved invalid entity, so a fresh context
	// with N real entities added iterates N + 1 live entities (id 0 included).
	auto ctx = create();
	scope(exit) free(ctx);

	EntityId a = ctx.addEntity();
	EntityId b = ctx.addEntity();
	cast(void) a; cast(void) b;

	size_t count = 0;
	foreach (e; ctx.entities()) count++;
	assert(count == 3);

	ctx.removeEntity(b);
	count = 0;
	foreach (e; ctx.entities()) count++;
	assert(count == 2);
}

unittest {
	struct Counter { int value; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e = ctx.addEntity();
	assert(!ctx.hasComponent!Counter(e));
	auto c = &ctx.getOrAddComponent!Counter(e);
	c.value = 5;
	assert(ctx.hasComponent!Counter(e));
	assert(ctx.getComponent!Counter(e).value == 5);

	ctx.removeComponent!Counter(e);
	assert(!ctx.hasComponent!Counter(e));
}

unittest {
	// Context's runtime-componentId overloads (as opposed to the templated
	// ones exercised above) and freelist reuse in addEntity().
	struct Flag { int v; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e = ctx.addEntity();
	immutable id = componentId!Flag();

	assert(!ctx.hasComponent(e, id));
	auto p = ctx.getOrAddComponent(e, id); // component missing -> adds it
	(cast(Flag*) p).v = 42;
	assert(ctx.hasComponent(e, id));
	auto p2 = ctx.getOrAddComponent(e, id); // component present -> fetches it
	assert((cast(Flag*) p2).v == 42);
	assert((cast(Flag*) ctx.getComponent(e, id)).v == 42);

	ctx.removeComponent(e, id);
	assert(!ctx.hasComponent(e, id));
	auto p3 = ctx.addComponent(e, id, Flag.sizeof);
	assert((cast(Flag*) p3).v == 0);

	// Removing then re-adding an entity should recycle its id via the freelist.
	EntityId toRemove = ctx.addEntity();
	ctx.removeEntity(toRemove);
	EntityId reused = ctx.addEntity();
	assert(reused == toRemove);
}

unittest {
	// const(Context) component access (the getComponent/getStorage const
	// overloads), swapEntities/reorderEntities, and
	// makeMonotonic/makeAllMonotonic (runtime componentId form).
	struct Val { int v; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e1 = ctx.addEntity(); // id 1
	ctx.addComponent!Val(e1).v = 30;
	EntityId e2 = ctx.addEntity(); // id 2
	ctx.addComponent!Val(e2).v = 10;
	EntityId e3 = ctx.addEntity(); // id 3
	ctx.addComponent!Val(e3).v = 20;

	const(Context)* cctx = &ctx;
	assert((*cctx).getComponent!Val(e1).v == 30); // free functions don't UFCS off a pointer receiver - needs an explicit deref

	// swapEntities(a, b): explicit pair, then swap back.
	ctx.swapEntities(e1, e3);
	assert(ctx.getComponent!Val(e1).v == 20);
	assert(ctx.getComponent!Val(e3).v == 30);
	ctx.swapEntities(e1, e3);

	// swapEntities(a): default b resolves to the last entity slot.
	immutable lastId = cast(EntityId)(fp.dynarray.length(ctx.entityComponentIndices) - 1);
	assert(lastId == e3);
	ctx.swapEntities(e1);
	assert(ctx.getComponent!Val(lastId).v == 30);
	ctx.swapEntities(e1); // swap back

	// reorderEntities(): keep entity 0 fixed, reverse entities 1..3.
	immutable size_t[4] order = [0, 3, 2, 1];
	ctx.reorderEntities(order[]);
	assert(ctx.getComponent!Val(1).v == 20); // formerly entity 3's value
	assert(ctx.getComponent!Val(2).v == 10); // unchanged
	assert(ctx.getComponent!Val(3).v == 30); // formerly entity 1's value

	// A 3-cycle, to pin down which way `order` reads: `order[i]` is the entity
	// that *ends up at* i, not where i goes. The two disagree for any permutation
	// that is not its own inverse, and the pairwise `order = [0, 3, 2, 1]` above
	// cannot tell them apart.
	immutable size_t[4] cycle = [0, 3, 1, 2];
	ctx.reorderEntities(cycle[]);
	assert(ctx.getComponent!Val(1).v == 30); // entity 3 held 30 and lands at 1
	assert(ctx.getComponent!Val(2).v == 20);
	assert(ctx.getComponent!Val(3).v == 10);

	assert((*cctx).getStorage(componentId!Val(), Val.sizeof).liveCount() == 3);

	// makeMonotonic(runtime id) / makeAllMonotonic() re-sort storage by entity id.
	// An id no entity ever had has no storage, so nothing to sort.
	struct NeverAdded { int v; }
	ctx.makeMonotonic(componentId!NeverAdded());
	immutable id = componentId!Val();
	ctx.makeMonotonic(id);
	ctx.makeAllMonotonic();
	auto storage = &ctx.getStorage!Val();
	assert((*storage).getEntity(0) == 1);
	assert((*storage).getEntity(1) == 2);
	assert((*storage).getEntity(2) == 3);
}

unittest {
	// Finalizers run once per component, whichever way it goes: removeComponent,
	// removeEntity, or free(ctx) for what is left. A dynamic Relation owns a
	// dynarray this way; leaking it is what the hook exists to prevent.
	static struct Owned {
		int value;
		__gshared int finalized;
		static void finalize(ref Owned) @nogc nothrow { ++finalized; }
	}
	Owned.finalized = 0;
	{
		auto ctx = create();
		scope(exit) free(ctx);

		EntityId e1 = ctx.addEntity();
		EntityId e2 = ctx.addEntity();
		EntityId e3 = ctx.addEntity();
		ctx.addComponent!Owned(e1);
		ctx.addComponent!Owned(e2);
		ctx.addComponent!Owned(e3);

		ctx.removeComponent!Owned(e1);
		assert(Owned.finalized == 1);
		ctx.removeEntity(e2);
		assert(Owned.finalized == 2);
	}
	assert(Owned.finalized == 3);
}

unittest {
	// The renumbering reaches every holder without the caller naming any:
	// relation components (fixed, dynamic, term-valued), storage owners, the
	// freelist, and an external hook. A freed entity in the table no longer
	// stops it.
	import ecrs.relation : Relation, Term, dynamicExtent;
	alias Next = Relation!1;
	alias Many = Relation!(dynamicExtent);
	alias Typed = Relation!(1, true);

	static struct Memo {
		EntityId cached;
		static void remap(void* self, const(EntityId)[] remap) @nogc nothrow {
			auto memo = cast(Memo*) self;
			memo.cached = remap[memo.cached];
		}
	}

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e1 = ctx.addEntity(); // 1
	EntityId e2 = ctx.addEntity(); // 2
	EntityId e3 = ctx.addEntity(); // 3
	EntityId gone = ctx.addEntity(); // 4
	ctx.removeEntity(gone);

	ctx.addComponent!Next(e1).related[0] = e2;
	ctx.addComponent!Next(e2).related[0] = e3;
	ctx.addComponent!Next(e3).related[0] = invalidEntity;
	fp.dynarray.pushBack(ctx.addComponent!Many(e1).related, e3);
	ctx.addComponent!Typed(e2).related[0] = Term(e1);

	Memo memo = Memo(e3);
	ctx.addRemapHook(&Memo.remap, &memo);

	// 1 -> 3, 2 -> 1, 3 -> 2; the freed 4 stays where it is.
	immutable size_t[5] order = [0, 2, 3, 1, 4];
	ctx.reorderEntities(order[]);

	assert(ctx.getComponent!Next(3).related[0] == 1);
	assert(ctx.getComponent!Next(1).related[0] == 2);
	assert(ctx.getComponent!Next(2).related[0] == invalidEntity);
	assert(ctx.getComponent!Many(3).related[0] == 2);
	assert(ctx.getComponent!Typed(1).related[0].constant == 3);
	assert(ctx.getStorage!Next().getEntity(ctx.entityComponentIndices[3][componentId!Next()]) == 3);
	assert(memo.cached == 2);
	assert(ctx.freelist[0] == 4);

	assert(ctx.removeRemapHook(&Memo.remap, &memo));
	assert(!ctx.removeRemapHook(&Memo.remap, &memo));
	ctx.swapEntities(1, 2);
	assert(memo.cached == 2); // no longer hooked
	assert(ctx.getComponent!Next(3).related[0] == 2); // ... but components still are
}

unittest {
	// compact(): live entities renumbered densely in order, the table shrunk,
	// the freelist emptied, and references to a freed entity made invalid.
	import ecrs.relation : Relation;
	alias Next = Relation!1;
	struct Val { int v; }

	auto ctx = create();
	scope(exit) free(ctx);

	foreach (i; 1 .. 6) {
		EntityId e = ctx.addEntity();
		ctx.addComponent!Val(e).v = i * 10;
	}
	ctx.addComponent!Next(5).related[0] = 3;
	ctx.addComponent!Next(1).related[0] = 4;
	ctx.removeEntity(2);
	ctx.removeEntity(4);

	ctx.compact();
	assert(fp.dynarray.length(ctx.entityComponentIndices) == 4);
	assert(fp.dynarray.length(ctx.freelist) == 0);
	assert(ctx.entityCount() == 4);
	assert(ctx.getComponent!Val(1).v == 10);
	assert(ctx.getComponent!Val(2).v == 30);
	assert(ctx.getComponent!Val(3).v == 50);
	assert(ctx.getComponent!Next(3).related[0] == 2);
	assert(ctx.getComponent!Next(1).related[0] == invalidEntity);
	assert(ctx.addEntity() == 4);

	ctx.compact(); // nothing freed: a no-op
	assert(fp.dynarray.length(ctx.entityComponentIndices) == 5);
}

unittest {
	// A component's address survives everything a nested query might do:
	// adding more of the same type, registering new component types (which
	// relocates the storage table), and removing other components.
	struct Payload { int value; }
	struct LateA { int x; }
	struct LateB { long y; }

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId first = ctx.addEntity();
	Payload* held = &ctx.addComponent!Payload(first);
	held.value = 7;

	foreach (i; 0 .. 3000) {
		EntityId e = ctx.addEntity();
		ctx.addComponent!Payload(e).value = i;
		if (i == 1000) ctx.addComponent!LateA(e);
		if (i == 2000) ctx.addComponent!LateB(e);
		if (i % 3 == 0) ctx.removeComponent!Payload(e);
	}
	assert(&ctx.getComponent!Payload(first) is held);
	assert(held.value == 7);
}
