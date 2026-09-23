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

import fp.dynarray;
import fp.pointer : allocFunction, notFound;

import ecrs.registry : componentId, lookupComponentSize;
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
struct Context {
	private ComponentStorage* storages = null;
	EntityComponentIndices entityComponentIndices = null;
	size_t* freelist = null;
}

/// Constructs a context with the permanently-reserved invalid entity (id 0)
/// already allocated. Use this instead of `Context.init` directly.
Context create() {
	Context c;
	cast(void) addEntity(c);
	return c;
}

void free(ref Context self) @trusted {
	if (self.storages !is null) {
		foreach (i; 0 .. fp.dynarray.length(self.storages))
			ecrs.storage.free(self.storages[i]);
		fp.dynarray.free(self.storages);
	}
	if (self.entityComponentIndices !is null) {
		foreach (i; 0 .. fp.dynarray.length(self.entityComponentIndices))
			if (self.entityComponentIndices[i] !is null)
				fp.dynarray.free(self.entityComponentIndices[i]);
		fp.dynarray.free(self.entityComponentIndices);
	}
	if (self.freelist !is null) fp.dynarray.free(self.freelist);
}

// NOTE: the finalizer-accepting overload below deliberately isn't just a
// third defaulted parameter on this one - DMD treats a 2-arg call against
// a "fill in the default" match and the const overload's "convert self to
// const" match as equally good, which makes the 2-arg call ambiguous.
// Keeping the 2-arg and 3-arg mutable overloads exact-arity-only avoids that.
ref ComponentStorage getStorage(ref Context self, size_t componentIdVal, size_t elementSize) @trusted {
	return getStorage(self, componentIdVal, elementSize, null);
}
ref ComponentStorage getStorage(ref Context self, size_t componentIdVal, size_t elementSize, ComponentStorage.FinalizeFunction finalizeFunction) @trusted {
	while (fp.dynarray.length(self.storages) <= componentIdVal)
		fp.dynarray.pushBack(self.storages, ComponentStorage.init);
	if (self.storages[componentIdVal].elementSize == ComponentStorage.invalid)
		self.storages[componentIdVal] = ecrs.storage.create(elementSize, ComponentStorage.defaultReservedElementCount, finalizeFunction);
	assert(self.storages[componentIdVal].elementSize != ComponentStorage.invalid);
	return self.storages[componentIdVal];
}
ref const(ComponentStorage) getStorage(const ref Context self, size_t componentIdVal, size_t elementSize) @trusted {
	assert(fp.dynarray.length(self.storages) > componentIdVal);
	assert(self.storages[componentIdVal].elementSize != ComponentStorage.invalid);
	return self.storages[componentIdVal];
}
template getStorage(Tcomponent, size_t Unique = 0) {
	ref ComponentStorage getStorage(ref Context self) @nogc nothrow {
		return .getStorage(self, componentId!(Tcomponent, Unique)(), Tcomponent.sizeof, finalizerFor!Tcomponent());
	}
}

size_t entityCount(const ref Context self) @trusted {
	return fp.dynarray.length(self.entityComponentIndices) - fp.dynarray.length(self.freelist);
}

EntityId addEntity(ref Context self) @trusted {
	if (self.freelist !is null && fp.dynarray.length(self.freelist) > 0) {
		immutable e = *fp.dynarray.back(self.freelist);
		fp.dynarray.popBack(self.freelist);
		return cast(EntityId) e;
	}
	immutable out_ = cast(EntityId) fp.dynarray.length(self.entityComponentIndices);
	fp.dynarray.pushBack(self.entityComponentIndices, cast(ComponentIndexList) null);
	return out_;
}

void removeEntity(ref Context self, EntityId e) @trusted {
	assert(e < fp.dynarray.length(self.entityComponentIndices));
	if (self.entityComponentIndices[e] !is null) {
		auto indices = self.entityComponentIndices[e];
		foreach (componentIdVal; 0 .. fp.dynarray.length(indices))
			if (indices[componentIdVal] != ComponentStorage.invalid)
				finalizeElement(self.storages[componentIdVal], indices[componentIdVal]);
		fp.dynarray.free(self.entityComponentIndices[e]);
		self.entityComponentIndices[e] = null;
	}
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
void* addComponent(ref Context self, EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted {
	assert(!hasComponent(self, e, componentIdVal));
	immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
	auto storagePtr = &getStorage(self, componentIdVal, sz);
	ensureIndexSlot(self.entityComponentIndices[e], componentIdVal);
	immutable idx = (*storagePtr).size();
	self.entityComponentIndices[e][componentIdVal] = idx;
	(*storagePtr).allocate(1);
	return (*storagePtr).get(idx);
}
template addComponent(Tcomponent, size_t Unique = 0) {
	ref Tcomponent addComponent(ref Context self, EntityId e) @trusted @nogc nothrow {
		assert(!.hasComponent!(Tcomponent, Unique)(self, e));
		immutable id = componentId!(Tcomponent, Unique)();
		auto storagePtr = &.getStorage!(Tcomponent, Unique)(self);
		ensureIndexSlot(self.entityComponentIndices[e], id);
		immutable idx = (*storagePtr).size();
		self.entityComponentIndices[e][id] = idx;
		// NOTE: explicit module qualification (rather than UFCS/plain calls)
		// is required here - calling a name that has both a plain and a
		// template overload with an *explicit* template argument, across a
		// module boundary (this is ecrs.context calling into ecrs.storage),
		// fails to resolve under DMD otherwise ("no overload matches"),
		// apparently a limitation in how such mixed overload sets are looked
		// up across modules. Confirmed with a minimal repro during porting.
		ecrs.storage.allocate!Tcomponent(*storagePtr, 1);
		auto outPtr = &ecrs.storage.get!Tcomponent(*storagePtr, idx);
		static if (isWithEntity!Tcomponent)
			outPtr.entity = e;
		return *outPtr;
	}
}

void removeComponent(ref Context self, EntityId e, size_t componentIdVal) @trusted {
	assert(hasComponent(self, e, componentIdVal));
	immutable sz = lookupComponentSize(componentIdVal);
	finalizeElement(getStorage(self, componentIdVal, sz), self.entityComponentIndices[e][componentIdVal]);
	self.entityComponentIndices[e][componentIdVal] = ComponentStorage.invalid;
	// NOTE: as in the C++ version, this leaves the slot in the backing
	// ComponentStorage occupied - it does not compact storage. The
	// component's own resources (if any) were just released above via
	// finalizeElement(), so the orphaned slot itself is inert.
}
template removeComponent(Tcomponent, size_t Unique = 0) {
	void removeComponent(ref Context self, EntityId e) @nogc nothrow {
		.removeComponent(self, e, componentId!(Tcomponent, Unique)());
	}
}

void* getComponent(ref Context self, EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted {
	assert(hasComponent(self, e, componentIdVal));
	immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
	return getStorage(self, componentIdVal, sz).get(self.entityComponentIndices[e][componentIdVal]);
}
const(void)* getComponent(const ref Context self, EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted {
	assert(hasComponent(self, e, componentIdVal));
	immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
	return getStorage(self, componentIdVal, sz).get(self.entityComponentIndices[e][componentIdVal]);
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

void swapEntities(ref Context self, EntityId a, EntityId b = EntityId.max) @trusted {
	immutable resolvedB = b == EntityId.max ? cast(EntityId)(fp.dynarray.length(self.entityComponentIndices) - 1) : b;
	assert(a < fp.dynarray.length(self.entityComponentIndices));
	assert(resolvedB < fp.dynarray.length(self.entityComponentIndices));
	auto tmp = self.entityComponentIndices[a];
	self.entityComponentIndices[a] = self.entityComponentIndices[resolvedB];
	self.entityComponentIndices[resolvedB] = tmp;
}
/// Also notifies each of `Tcomponents2notify` (via their `swapEntities`
/// static method) before the low-level index swap, so components that
/// cache their owning entity id (e.g. `WithEntity`, a relation) stay correct.
template swapEntities(Tcomponents2notify...) {
	void swapEntities(ref Context self, EntityId a, EntityId b = EntityId.max) @trusted @nogc nothrow {
		immutable resolvedB = b == EntityId.max ? cast(EntityId)(fp.dynarray.length(self.entityComponentIndices) - 1) : b;
		static foreach (T; Tcomponents2notify) {
			{
				auto storagePtr = &.getStorage!T(self);
				T* data = (*storagePtr).data!T();
				foreach_reverse (i; 0 .. (*storagePtr).size())
					T.swapEntities(data[i], self.entityComponentIndices, a, resolvedB);
			}
		}
		.swapEntities(self, a, resolvedB);
	}
}

void reorderEntities(ref Context self, const(size_t)[] order) {
	assert(order.length == entityCount(self));
	applyPermutation(order, (a, b) { swapEntities(self, cast(EntityId) a, cast(EntityId) b); });
}
/// Ditto, relabelling the entity ids each of `Tcomponents2notify` holds (via
/// their `remapEntities` static method) so components that reference entities -
/// `WithEntity`, a relation - stay correct across the renumbering.
///
/// `remapEntities` and not `swapEntities`: `applyPermutation` makes O(n) swaps,
/// so notifying per swap rescanned every instance of every listed component n
/// times. Relabelling once is the same permutation - composing the transpositions
/// over the labels and applying the permutation to them directly agree - and it
/// turns the notification from O(n * references) into O(references).
template reorderEntities(Tcomponents2notify...) {
	void reorderEntities(ref Context self, const(size_t)[] order) @nogc nothrow @trusted {
		assert(order.length == entityCount(self));
		static foreach (T; Tcomponents2notify)
			static assert(hasRemapEntities!T,
				T.stringof ~ " is listed in a reorderEntities() but has no remapEntities() hook"
				~ " - a swapEntities()-only component would silently keep its old entity ids.");

		auto remap = buildRemap(order);
		scope(exit) allocFunction(remap, 0);
		const(EntityId)[] remapSlice = remap[0 .. order.length];
		static foreach (T; Tcomponents2notify) {
			{
				auto storagePtr = &.getStorage!T(self);
				T* data = (*storagePtr).data!T();
				foreach (i; 0 .. (*storagePtr).size())
					T.remapEntities(data[i], self.entityComponentIndices, remapSlice);
			}
		}

		// Independent of the relabelling above: this moves component data between
		// entity slots, which no slot's *contents* depend on.
		applyPermutation(order, (a, b) {
			.swapEntities(self, cast(EntityId) a, cast(EntityId) b);
		});
	}
}

template makeMonotonic(Tcomponents...) if (Tcomponents.length != 1 || !is(typeof(Tcomponents[0]) : size_t)) {
	void makeMonotonic(ref Context self) @nogc nothrow {
		// See the NOTE in addComponent(Tcomponent, Unique) above: explicit
		// module qualification is required for the cross-module `!T` call.
		static foreach (T; Tcomponents)
			ecrs.storage.sortMonotonic!T(.getStorage!T(self), self.entityComponentIndices);
	}
}
template makeMonotonic(Tcomponent, size_t Unique = 0) {
	void makeMonotonic(ref Context self) @nogc nothrow {
		ecrs.storage.sortMonotonic!(Tcomponent, Unique)(.getStorage!(Tcomponent, Unique)(self), self.entityComponentIndices);
	}
}
void makeMonotonic(ref Context self, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) {
	immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
	getStorage(self, componentIdVal, sz).sortMonotonic(componentIdVal, self.entityComponentIndices);
}

void makeAllMonotonic(ref Context self) @trusted {
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
	// overloads), swapEntities/reorderEntities (runtime, non-template
	// forms), and makeMonotonic/makeAllMonotonic (runtime componentId form).
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

	// makeMonotonic(runtime id) / makeAllMonotonic() re-sort storage by entity id.
	immutable id = componentId!Val();
	ctx.makeMonotonic(id);
	ctx.makeAllMonotonic();
	assert(getEntity(ctx.entityComponentIndices, 0, id) == 1);
	assert(getEntity(ctx.entityComponentIndices, 1, id) == 2);
	assert(getEntity(ctx.entityComponentIndices, 2, id) == 3);
}

unittest {
	// removeComponent()/removeEntity() finalize a component that owns
	// resources of its own (here, a dynamic Relation's backing array)
	// instead of leaking them - ComponentStorage is flat POD bytes with no
	// destructor support, so this hook (ecrs.storage.hasFinalize /
	// Relation.finalize) is the only place that cleanup can happen. Verified
	// for real (LeakSanitizer, not just this in-process check) via a
	// standalone repro during development.
	import ecrs.relation : Relation, dynamicExtent;
	alias DynRel = Relation!(dynamicExtent, false);

	auto ctx = create();
	scope(exit) free(ctx);

	immutable id = componentId!DynRel();

	// removeComponent(): the entity survives, only the component goes away.
	EntityId e1 = ctx.addEntity();
	auto c1 = &ctx.addComponent!DynRel(e1);
	fp.dynarray.pushBack(c1.related, EntityId(1));
	fp.dynarray.pushBack(c1.related, EntityId(2));
	immutable idx1 = ctx.entityComponentIndices[e1][id];
	ctx.removeComponent!DynRel(e1);
	// The slot is still physically present (removeComponent doesn't compact
	// storage) but finalize() must have run and released/nulled `related`.
	ref ComponentStorage storage1 = ctx.getStorage!DynRel();
	assert(ecrs.storage.get!DynRel(storage1, idx1).related is null);

	// removeEntity(): the component is still attached when the entity goes.
	EntityId e2 = ctx.addEntity();
	auto c2 = &ctx.addComponent!DynRel(e2);
	fp.dynarray.pushBack(c2.related, EntityId(3));
	immutable idx2 = ctx.entityComponentIndices[e2][id];
	ctx.removeEntity(e2);
	ref ComponentStorage storage2 = ctx.getStorage!DynRel();
	assert(ecrs.storage.get!DynRel(storage2, idx2).related is null);
}


unittest {
	// reorderEntities!(Tcomponents2notify): the renumbering has to reach inside a
	// component that *references* entities, not just move component data between
	// slots. A relation pointing at the entity after it stays pointing at it.
	import ecrs.relation : Relation, dynamicExtent;

	struct Link {
		Relation!1 relation;
		alias relation this;
		static void swapEntities(ref Link self, ref EntityComponentIndices idx, EntityId a, EntityId b) @nogc nothrow {
			Relation!1.swapEntities(self.relation, idx, a, b);
		}
		static void remapEntities(ref Link self, ref EntityComponentIndices idx, const(EntityId)[] remap) @nogc nothrow {
			Relation!1.remapEntities(self.relation, idx, remap);
		}
	}

	auto ctx = create();
	scope(exit) free(ctx);

	EntityId e1 = ctx.addEntity(); // 1
	EntityId e2 = ctx.addEntity(); // 2
	EntityId e3 = ctx.addEntity(); // 3
	ctx.addComponent!Link(e1).related[0] = e2;
	ctx.addComponent!Link(e2).related[0] = e3;
	ctx.addComponent!Link(e3).related[0] = invalidEntity;

	// 1 -> 3, 2 -> 1, 3 -> 2, so the chain becomes 3 -> 1 -> 2 -> invalid.
	immutable size_t[4] order = [0, 2, 3, 1];
	ctx.reorderEntities!Link(order[]);

	assert(ctx.getComponent!Link(3).related[0] == 1);
	assert(ctx.getComponent!Link(1).related[0] == 2);
	assert(ctx.getComponent!Link(2).related[0] == invalidEntity);
}
