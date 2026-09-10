/// The entity/component database (`Context`) and the current-context-aware
/// `Entity` handle. Ported from context.hpp.
///
/// As with storage.d, every method spells out `@nogc nothrow` explicitly -
/// the module-level colon attribute below does not propagate into struct
/// member functions.
module ecrs.context;

// import core.stdc.stdlib : cMalloc = malloc, cFree = free;

import fp.dynarray;
import fp.pointer : allocFunction, notFound;

import ecrs.registry : componentId, lookupComponentSize;
import ecrs.storage;

@nogc nothrow:


private bool freelistContains(inout size_t* freelist, size_t value) @trusted @nogc nothrow {
	if (freelist is null) return false;
	immutable n = fp.dynarray.length(cast(size_t*) freelist);
	foreach (i; 0 .. n)
		if ((cast(size_t*) freelist)[i] == value) return true;
	return false;
}

private void reorderEntitiesCore(ref Context self, const(size_t)[] order, void function(ref Context, size_t, size_t) @nogc nothrow swapFunction) @trusted @nogc nothrow {
	immutable n = order.length;
	assert(n == self.entityCount());
	if (n <= 1) return;

	size_t* swaps = cast(size_t*) allocFunction(null, n * size_t.sizeof);
	scope(exit) allocFunction(swaps, 0);
	foreach (i; 0 .. n) swaps[order[i]] = i;

	foreach (i; 0 .. n)
		while (swaps[i] != i) {
			swapFunction(self, swaps[i], i);
			immutable t = swaps[swaps[i]]; swaps[swaps[i]] = swaps[i]; swaps[i] = t;
		}
}


/// Forward-facing entity/component handle bound to whichever `Context` was
/// last marked current on this thread (`Context.makeCurrent`). Mirrors
/// `context::entity` in the C++ version; `current context` is genuinely
/// thread-local here (a plain D `static`), matching the original's
/// `thread_local`, unlike the process-global registry in ecrs.registry.
struct Entity {
	private static Context* currentContext_ = null;

	static void setCurrentContext(ref Context ctx) @nogc nothrow { currentContext_ = &ctx; }
	static Context* currentContext() @nogc nothrow { return currentContext_; }

	EntityId entity_ = invalidEntity;
	alias entity_ this;

	this(EntityId e) @nogc nothrow { entity_ = e; }

	void remove() @nogc nothrow {
		assert(currentContext_ !is null);
		currentContext_.removeEntity(entity_);
	}

	bool hasComponent(size_t componentIdVal) const @nogc nothrow {
		assert(currentContext_ !is null);
		return currentContext_.hasComponent(entity_, componentIdVal);
	}
	template hasComponent(Tcomponent, size_t Unique = 0) {
		bool hasComponent() const @nogc nothrow {
			assert(currentContext_ !is null);
			return currentContext_.hasComponent!(Tcomponent, Unique)(entity_);
		}
	}

	void* addComponent(size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @nogc nothrow {
		assert(currentContext_ !is null);
		return currentContext_.addComponent(entity_, componentIdVal, elementSize);
	}
	template addComponent(Tcomponent, size_t Unique = 0) {
		ref Tcomponent addComponent() @nogc nothrow {
			assert(currentContext_ !is null);
			return currentContext_.addComponent!(Tcomponent, Unique)(entity_);
		}
	}

	void removeComponent(size_t componentIdVal) @nogc nothrow {
		assert(currentContext_ !is null);
		currentContext_.removeComponent(entity_, componentIdVal);
	}
	template removeComponent(Tcomponent, size_t Unique = 0) {
		void removeComponent() @nogc nothrow {
			assert(currentContext_ !is null);
			currentContext_.removeComponent!(Tcomponent, Unique)(entity_);
		}
	}

	void* getComponent(size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @nogc nothrow {
		assert(currentContext_ !is null);
		return currentContext_.getComponent(entity_, componentIdVal, elementSize);
	}
	template getComponent(Tcomponent, size_t Unique = 0) {
		ref Tcomponent getComponent() @nogc nothrow {
			assert(currentContext_ !is null);
			return currentContext_.getComponent!(Tcomponent, Unique)(entity_);
		}
	}

	void* getOrAddComponent(size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @nogc nothrow {
		assert(currentContext_ !is null);
		return currentContext_.getOrAddComponent(entity_, componentIdVal, elementSize);
	}
	template getOrAddComponent(Tcomponent, size_t Unique = 0) {
		ref Tcomponent getOrAddComponent() @nogc nothrow {
			assert(currentContext_ !is null);
			return currentContext_.getOrAddComponent!(Tcomponent, Unique)(entity_);
		}
	}
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
	Entity front() const @nogc nothrow { return Entity(cast(EntityId) index); }
	void popFront() @nogc nothrow { index++; skipFreed(); }
}


/// The entity/component database: owns one `ComponentStorage` per
/// registered component id, plus the per-entity index tables mapping entity
/// -> component slot. A genuine RAII value in D (unlike the C++ version,
/// which needed a separate `fp::auto_free<context>` wrapper for that) -
/// destructing a `Context` frees everything it owns.
struct Context {
	private ComponentStorage* storages = null;
	EntityComponentIndices entityComponentIndices = null;
	size_t* freelist = null;

	/// Constructs a context with the permanently-reserved invalid entity (id
	/// 0) already allocated. Use this instead of `Context.init` directly.
	static Context create() @nogc nothrow {
		Context c;
		cast(void) c.addEntity();
		return c;
	}

	@disable this(this);

	void free() @trusted @nogc nothrow {
		if (storages !is null) {
			foreach (i; 0 .. fp.dynarray.length(storages))
				storages[i].free();
			fp.dynarray.free(storages);
		}
		if (entityComponentIndices !is null) {
			foreach (i; 0 .. fp.dynarray.length(entityComponentIndices))
				if (entityComponentIndices[i] !is null)
					fp.dynarray.free(entityComponentIndices[i]);
			fp.dynarray.free(entityComponentIndices);
		}
		if (freelist !is null) fp.dynarray.free(freelist);
	}

	// NOTE: the finalizer-accepting overload below deliberately isn't just a
	// third defaulted parameter on this one - DMD treats a 2-arg call against
	// a "fill in the default" match and the const overload's "convert this to
	// const" match as equally good, which makes the 2-arg call ambiguous.
	// Keeping the 2-arg and 3-arg mutable overloads exact-arity-only avoids that.
	ref ComponentStorage getStorage(size_t componentIdVal, size_t elementSize) @trusted @nogc nothrow {
		return this.getStorage(componentIdVal, elementSize, null);
	}
	ref ComponentStorage getStorage(size_t componentIdVal, size_t elementSize, ComponentStorage.FinalizeFunction finalizeFunction) @trusted @nogc nothrow {
		while (fp.dynarray.length(storages) <= componentIdVal)
			fp.dynarray.pushBack(storages, ComponentStorage.init);
		if (storages[componentIdVal].elementSize == ComponentStorage.invalid)
			storages[componentIdVal] = ComponentStorage(elementSize, ComponentStorage.defaultReservedElementCount, finalizeFunction);
		assert(storages[componentIdVal].elementSize != ComponentStorage.invalid);
		return storages[componentIdVal];
	}
	ref const(ComponentStorage) getStorage(size_t componentIdVal, size_t elementSize) const @trusted @nogc nothrow {
		assert(fp.dynarray.length(storages) > componentIdVal);
		assert(storages[componentIdVal].elementSize != ComponentStorage.invalid);
		return storages[componentIdVal];
	}
	template getStorage(Tcomponent, size_t Unique = 0) {
		ref ComponentStorage getStorage() @nogc nothrow {
			return this.getStorage(componentId!(Tcomponent, Unique)(), Tcomponent.sizeof, finalizerFor!Tcomponent());
		}
	}

	size_t entityCount() const @trusted @nogc nothrow {
		return fp.dynarray.length(entityComponentIndices) - fp.dynarray.length(freelist);
	}

	EntityId addEntity() @trusted @nogc nothrow {
		if (freelist !is null && fp.dynarray.length(freelist) > 0) {
			immutable e = *fp.dynarray.back(freelist);
			fp.dynarray.popBack(freelist);
			return cast(EntityId) e;
		}
		immutable out_ = cast(EntityId) fp.dynarray.length(entityComponentIndices);
		fp.dynarray.pushBack(entityComponentIndices, cast(ComponentIndexList) null);
		return out_;
	}

	void removeEntity(EntityId e) @trusted @nogc nothrow {
		assert(e < fp.dynarray.length(entityComponentIndices));
		if (entityComponentIndices[e] !is null) {
			auto indices = entityComponentIndices[e];
			foreach (componentIdVal; 0 .. fp.dynarray.length(indices))
				if (indices[componentIdVal] != ComponentStorage.invalid)
					storages[componentIdVal].finalizeElement(indices[componentIdVal]);
			fp.dynarray.free(entityComponentIndices[e]);
			entityComponentIndices[e] = null;
		}
		fp.dynarray.pushBack(freelist, cast(size_t) e);
	}

	bool hasComponent(EntityId e, size_t componentIdVal) const @trusted @nogc nothrow {
		return entityComponentIndices !is null
			&& e < fp.dynarray.length(entityComponentIndices)
			&& entityComponentIndices[e] !is null
			&& fp.dynarray.length(entityComponentIndices[e]) > componentIdVal
			&& entityComponentIndices[e][componentIdVal] != ComponentStorage.invalid;
	}
	template hasComponent(Tcomponent, size_t Unique = 0) {
		bool hasComponent(EntityId e) const @nogc nothrow {
			return this.hasComponent(e, componentId!(Tcomponent, Unique)());
		}
	}

	/// Type-erased: the new slot is zero-filled rather than constructed,
	/// since there's no compile-time type here to initialize it properly.
	/// Prefer the templated overload below whenever `Tcomponent` is known.
	void* addComponent(EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted @nogc nothrow {
		assert(!hasComponent(e, componentIdVal));
		immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
		auto storagePtr = &getStorage(componentIdVal, sz);
		ensureIndexSlot(entityComponentIndices[e], componentIdVal);
		immutable idx = storagePtr.size();
		entityComponentIndices[e][componentIdVal] = idx;
		storagePtr.allocate(1);
		return storagePtr.get(idx);
	}
	template addComponent(Tcomponent, size_t Unique = 0) {
		ref Tcomponent addComponent(EntityId e) @trusted @nogc nothrow {
			assert(!this.hasComponent!(Tcomponent, Unique)(e));
			immutable id = componentId!(Tcomponent, Unique)();
			auto storagePtr = &this.getStorage!(Tcomponent, Unique)();
			ensureIndexSlot(entityComponentIndices[e], id);
			immutable idx = storagePtr.size();
			entityComponentIndices[e][id] = idx;
			storagePtr.allocate!Tcomponent(1);
			auto outPtr = &storagePtr.get!Tcomponent(idx);
			static if (isWithEntity!Tcomponent)
				outPtr.entity = e;
			return *outPtr;
		}
	}

	void removeComponent(EntityId e, size_t componentIdVal) @trusted @nogc nothrow {
		assert(hasComponent(e, componentIdVal));
		immutable sz = lookupComponentSize(componentIdVal);
		getStorage(componentIdVal, sz).finalizeElement(entityComponentIndices[e][componentIdVal]);
		entityComponentIndices[e][componentIdVal] = ComponentStorage.invalid;
		// NOTE: as in the C++ version, this leaves the slot in the backing
		// ComponentStorage occupied - it does not compact storage. The
		// component's own resources (if any) were just released above via
		// finalizeElement(), so the orphaned slot itself is inert.
	}
	template removeComponent(Tcomponent, size_t Unique = 0) {
		void removeComponent(EntityId e) @nogc nothrow {
			this.removeComponent(e, componentId!(Tcomponent, Unique)());
		}
	}

	void* getComponent(EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @trusted @nogc nothrow {
		assert(hasComponent(e, componentIdVal));
		immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
		return getStorage(componentIdVal, sz).get(entityComponentIndices[e][componentIdVal]);
	}
	const(void)* getComponent(EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) const @trusted @nogc nothrow {
		assert(hasComponent(e, componentIdVal));
		immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
		return getStorage(componentIdVal, sz).get(entityComponentIndices[e][componentIdVal]);
	}
	template getComponent(Tcomponent, size_t Unique = 0) {
		ref Tcomponent getComponent(EntityId e) @trusted @nogc nothrow {
			return *cast(Tcomponent*) this.getComponent(e, componentId!(Tcomponent, Unique)(), Tcomponent.sizeof);
		}
		ref const(Tcomponent) getComponent(EntityId e) const @trusted @nogc nothrow {
			return *cast(const(Tcomponent)*) this.getComponent(e, componentId!(Tcomponent, Unique)(), Tcomponent.sizeof);
		}
	}

	void* getOrAddComponent(EntityId e, size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @nogc nothrow {
		if (hasComponent(e, componentIdVal)) return getComponent(e, componentIdVal, elementSize);
		return addComponent(e, componentIdVal, elementSize);
	}
	template getOrAddComponent(Tcomponent, size_t Unique = 0) {
		ref Tcomponent getOrAddComponent(EntityId e) @nogc nothrow {
			if (this.hasComponent!(Tcomponent, Unique)(e)) return this.getComponent!(Tcomponent, Unique)(e);
			return this.addComponent!(Tcomponent, Unique)(e);
		}
	}

	void swapEntities(EntityId a, EntityId b = EntityId.max) @trusted @nogc nothrow {
		immutable resolvedB = b == EntityId.max ? cast(EntityId)(fp.dynarray.length(entityComponentIndices) - 1) : b;
		assert(a < fp.dynarray.length(entityComponentIndices));
		assert(resolvedB < fp.dynarray.length(entityComponentIndices));
		auto tmp = entityComponentIndices[a];
		entityComponentIndices[a] = entityComponentIndices[resolvedB];
		entityComponentIndices[resolvedB] = tmp;
	}
	/// Also notifies each of `Tcomponents2notify` (via their `swapEntities`
	/// static method) before the low-level index swap, so components that
	/// cache their owning entity id (e.g. `WithEntity`, a relation) stay correct.
	template swapEntities(Tcomponents2notify...) {
		void swapEntities(EntityId a, EntityId b = EntityId.max) @trusted @nogc nothrow {
			immutable resolvedB = b == EntityId.max ? cast(EntityId)(fp.dynarray.length(entityComponentIndices) - 1) : b;
			static foreach (T; Tcomponents2notify) {
				{
					auto storagePtr = &this.getStorage!T();
					T* data = storagePtr.data!T();
					foreach_reverse (i; 0 .. storagePtr.size())
						T.swapEntities(data[i], entityComponentIndices, a, resolvedB);
				}
			}
			this.swapEntities(a, resolvedB);
		}
	}

	void reorderEntities(const(size_t)[] order) @nogc nothrow {
		static void doSwap(ref Context self, size_t a, size_t b) @nogc nothrow {
			self.swapEntities(cast(EntityId) a, cast(EntityId) b);
		}
		reorderEntitiesCore(this, order, &doSwap);
	}
	template reorderEntities(Tcomponents2notify...) {
		void reorderEntities(const(size_t)[] order) @nogc nothrow {
			static void doSwap(ref Context self, size_t a, size_t b) @nogc nothrow {
				self.swapEntities!Tcomponents2notify(cast(EntityId) a, cast(EntityId) b);
			}
			reorderEntitiesCore(this, order, &doSwap);
		}
	}

	template makeMonotonic(Tcomponents...) if (Tcomponents.length != 1 || !is(typeof(Tcomponents[0]) : size_t)) {
		void makeMonotonic() @nogc nothrow {
			static foreach (T; Tcomponents)
				this.getStorage!T().sortMonotonic!T(entityComponentIndices);
		}
	}
	template makeMonotonic(Tcomponent, size_t Unique = 0) {
		void makeMonotonic() @nogc nothrow {
			this.getStorage!(Tcomponent, Unique)().sortMonotonic!(Tcomponent, Unique)(entityComponentIndices);
		}
	}
	void makeMonotonic(size_t componentIdVal, size_t elementSize = ComponentStorage.invalid) @nogc nothrow {
		immutable sz = elementSize == ComponentStorage.invalid ? lookupComponentSize(componentIdVal) : elementSize;
		getStorage(componentIdVal, sz).sortMonotonic(componentIdVal, entityComponentIndices);
	}

	void makeAllMonotonic() @trusted @nogc nothrow {
		foreach (id; 0 .. fp.dynarray.length(storages))
			if (storages[id].elementSize != ComponentStorage.invalid)
				storages[id].sortMonotonic(id, entityComponentIndices);
	}

	EntityRange entities() const @nogc nothrow { return EntityRange(&this, 0); }

	void makeCurrent() @nogc nothrow { Entity.setCurrentContext(this); }
}


unittest {
	struct Vec2 { float x = 0, y = 0; }

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	Entity e1 = ctx.addEntity();
	auto c1 = &e1.addComponent!Vec2();
	c1.x = 1; c1.y = 2;

	Entity e2 = ctx.addEntity();
	auto c2 = &e2.addComponent!Vec2();
	c2.x = 3; c2.y = 4;

	Entity e3 = ctx.addEntity();
	auto c3 = &e3.addComponent!Vec2();
	c3.x = 5; c3.y = 6;

	// entityCount() includes the permanently-reserved invalid entity 0, so
	// creating a context + 3 real entities counts as 4.
	assert(ctx.entityCount() == 4);
	assert(e1.hasComponent!Vec2());

	e2.remove();
	assert(ctx.entityCount() == 3);

	size_t seen = 0;
	float xsum = 0;
	foreach (e; ctx.entities())
		if (e.hasComponent!Vec2()) {
			xsum += e.getComponent!Vec2().x;
			seen++;
		}
	assert(seen == 2); // e1 and e3 (e2 was removed, entity 0 never had a Vec2)
	assert(xsum == 1 + 5);
}

unittest {
	// Entity 0 is the permanently-reserved invalid entity, so a fresh context
	// with N real entities added iterates N + 1 live entities (id 0 included).
	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	Entity a = ctx.addEntity();
	Entity b = ctx.addEntity();
	cast(void) a; cast(void) b;

	size_t count = 0;
	foreach (e; ctx.entities()) count++;
	assert(count == 3);

	b.remove();
	count = 0;
	foreach (e; ctx.entities()) count++;
	assert(count == 2);
}

unittest {
	struct Counter { int value; }

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	Entity e = ctx.addEntity();
	assert(!e.hasComponent!Counter());
	auto c = &e.getOrAddComponent!Counter();
	c.value = 5;
	assert(e.hasComponent!Counter());
	assert(e.getComponent!Counter().value == 5);

	e.removeComponent!Counter();
	assert(!e.hasComponent!Counter());
}

unittest {
	// Entity's runtime-componentId overloads (as opposed to the templated
	// ones exercised above), Entity.currentContext(), and freelist reuse in
	// Context.addEntity().
	struct Flag { int v; }

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();
	assert(Entity.currentContext() !is null);

	Entity e = ctx.addEntity();
	immutable id = componentId!Flag();

	assert(!e.hasComponent(id));
	auto p = e.getOrAddComponent(id); // component missing -> adds it
	(cast(Flag*) p).v = 42;
	assert(e.hasComponent(id));
	auto p2 = e.getOrAddComponent(id); // component present -> fetches it
	assert((cast(Flag*) p2).v == 42);
	assert((cast(Flag*) e.getComponent(id)).v == 42);

	e.removeComponent(id);
	assert(!e.hasComponent(id));
	auto p3 = e.addComponent(id, Flag.sizeof);
	assert((cast(Flag*) p3).v == 0);

	// Removing then re-adding an entity should recycle its id via the freelist.
	Entity toRemove = ctx.addEntity();
	immutable removedId = cast(EntityId) toRemove;
	toRemove.remove();
	Entity reused = ctx.addEntity();
	assert(cast(EntityId) reused == removedId);
}

unittest {
	// const(Context) component access (Context.getComponent/getStorage const
	// overloads), Context.swapEntities/reorderEntities (runtime, non-template
	// forms), and makeMonotonic/makeAllMonotonic (runtime componentId form).
	struct Val { int v; }

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	Entity e1 = ctx.addEntity(); // id 1
	e1.addComponent!Val().v = 30;
	Entity e2 = ctx.addEntity(); // id 2
	e2.addComponent!Val().v = 10;
	Entity e3 = ctx.addEntity(); // id 3
	e3.addComponent!Val().v = 20;

	const(Context)* cctx = &ctx;
	assert(cctx.getComponent!Val(cast(EntityId) e1).v == 30);

	// swapEntities(a, b): explicit pair, then swap back.
	ctx.swapEntities(cast(EntityId) e1, cast(EntityId) e3);
	assert(ctx.getComponent!Val(cast(EntityId) e1).v == 20);
	assert(ctx.getComponent!Val(cast(EntityId) e3).v == 30);
	ctx.swapEntities(cast(EntityId) e1, cast(EntityId) e3);

	// swapEntities(a): default b resolves to the last entity slot.
	immutable lastId = cast(EntityId)(fp.dynarray.length(ctx.entityComponentIndices) - 1);
	assert(lastId == cast(EntityId) e3);
	ctx.swapEntities(cast(EntityId) e1);
	assert(ctx.getComponent!Val(lastId).v == 30);
	ctx.swapEntities(cast(EntityId) e1); // swap back

	// reorderEntities(): keep entity 0 fixed, reverse entities 1..3.
	immutable size_t[4] order = [0, 3, 2, 1];
	ctx.reorderEntities(order[]);
	assert(ctx.getComponent!Val(1).v == 20); // formerly entity 3's value
	assert(ctx.getComponent!Val(2).v == 10); // unchanged
	assert(ctx.getComponent!Val(3).v == 30); // formerly entity 1's value

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

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	immutable id = componentId!DynRel();

	// removeComponent(): the entity survives, only the component goes away.
	Entity e1 = ctx.addEntity();
	auto c1 = &e1.addComponent!DynRel();
	fp.dynarray.pushBack(c1.related, EntityId(1));
	fp.dynarray.pushBack(c1.related, EntityId(2));
	immutable idx1 = ctx.entityComponentIndices[cast(EntityId) e1][id];
	e1.removeComponent!DynRel();
	// The slot is still physically present (removeComponent doesn't compact
	// storage) but finalize() must have run and released/nulled `related`.
	assert(ctx.getStorage!DynRel().get!DynRel(idx1).related is null);

	// removeEntity(): the component is still attached when the entity goes.
	Entity e2 = ctx.addEntity();
	auto c2 = &e2.addComponent!DynRel();
	fp.dynarray.pushBack(c2.related, EntityId(3));
	immutable idx2 = ctx.entityComponentIndices[cast(EntityId) e2][id];
	e2.remove();
	assert(ctx.getStorage!DynRel().get!DynRel(idx2).related is null);
}
