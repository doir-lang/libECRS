/// The entity and component database, `Context`.
///
/// There is deliberately no `Entity` handle wrapping a thread-local current context: callers pass the `Context`, and an `EntityId` where relevant, to every function.
module ecrs.context;

static import core.atomic;

static import bc.platform;
static import bc.monitor;
static import ecrs.registry;
static import ecrs.storage;
static import fp.dynarray;
static import fp.lifecycle;
static import fp.pointer;
static import fp.algorithms;

public import ecrs.registry : EntityId, invalidEntity;

@nogc nothrow:


/// What a `Context`'s `writeObserver` is called with: its `writeObserverData`, then the entity and component id about to be added, removed or handed out for writing.
alias WriteObserver = void function(void* userData, EntityId e, size_t componentId) @nogc nothrow;

/// A holder of entity ids outside the store, such as a query memo table, that every renumbering rewrites alongside the components.
/// `remap[old]` is the id `old` becomes.
alias RemapHookFunction = void function(void* userData, const(EntityId)[] remap) @nogc nothrow;

private struct RemapHook {
	RemapHookFunction hook;
	void* userData;
}

private enum JournalKind : ubyte { touchedStorage, removedEntity, removedComponent, replacedComponent }

/// One undoable step of a transaction; `saved` is the offset of a replaced component's old bytes in `Journal.saved`.
///
/// Additions are not journaled one by one: a storage's first is a `touchedStorage` holding its size in `slot` and its hole count in `saved`, and new entities are those past `Context.firstNew`.
private struct JournalEntry {
	JournalKind kind;
	EntityId e;
	size_t componentId;
	size_t slot;
	size_t saved;
}

// A transaction's undo log; `Context` keeps it in a monitor, the one lock concurrent writers share.
private struct Journal {
	JournalEntry* entries = null;
	ubyte* saved = null; // replaced components' old bytes, each at an offset aligned to `savedAlignment`
}

/// The entity and component database: one `ecrs.storage.Storage` per component id, and each entity's index list mapping its components to their slots.
///
/// It is plain data, released only by `free`: pair `create` with `scope(exit) free(context)`.
///
/// Between `beginTransaction` and `commitTransaction` it journals every change, so `rollbackTransaction` can restore it as it was without allocating.
/// Removals and replacements take an entry each; additions take one per storage, however many there are, so building a large store in one transaction costs no journal to speak of.
///
/// Concurrency: any number of threads may read at once, and may write existing components of distinct entities.
/// Structural changes, meaning adding or removing entities, components, storages or remap hooks, renumbering and sorting, need exclusive access; inside an `ecrs.schedules` parallel combinator they fail an assert rather than race, whatever the pool size, unless made between `beginExclusive` and `endExclusive` by a caller that keeps every other thread out of the store meanwhile.
/// Between `beginConcurrentWrites` and `endConcurrentWrites` threads may also add, set and remove components of distinct existing entities, in storages that already exist, from inside parallel combinators too.
struct Context {
	private ecrs.storage.Storage* storages = null;
	ecrs.storage.IndexTable indexTable = null; /// Every entity's index list, freed entities' included.
	size_t* freelist = null; /// Freed entity ids, which `addEntity` hands out again, last freed first.
	private RemapHook* remapHooks = null;
	private size_t parallelDepth = 0; // atomic; nonzero while a parallel schedule runs
	private size_t exclusiveDepth = 0; // nonzero while one thread holds the store to itself, read only by that thread
	private bool transaction = false;
	private size_t firstNew; // the entity count when the transaction began; it adds entities only past it
	private bool concurrent = false; // inside `beginConcurrentWrites`
	private bc.monitor.Monitor!Journal journal; // write-held while a change reserves and appends entries
	/// If set, called before every component write this module makes or hands out: `addComponent`, `removeComponent`, `getForWriting`, and whatever is built on them (`findForWriting`, `ensureComponent`, `setComponent`, `findSingletonForWriting`).
	/// An audit sets it to assert that a writer keeps to what it may write; it must not change the store, and with concurrent writers it is called from each of their threads.
	/// Removing an entity or clearing a component does not call it.
	WriteObserver writeObserver = null;
	void* writeObserverData = null; /// Passed to `writeObserver`.
}

/// Whether an `ecrs.schedules` parallel combinator is running on `self`.
///
/// Examples:
/// ---
/// Context context = create();
/// assert(!inParallel(context));
/// free(context);
/// ---
bool inParallel(const ref Context self) @trusted {
	return core.atomic.atomicLoad(bc.platform.asShared(self.parallelDepth)) != 0;
}

// wrapper: names the parallel bookkeeping the schedules keep
/// Marks `self` as inside a parallel combinator until the matching `exitParallel`.
///
/// Examples:
/// ---
/// Context context = create();
/// enterParallel(context);
/// assert(inParallel(context));
/// exitParallel(context);
/// assert(!inParallel(context));
/// free(context);
/// ---
package void enterParallel(ref Context self) @trusted {
	immutable depth = core.atomic.atomicOp!"+="(bc.platform.asShared(self.parallelDepth), 1);
	assert(depth > 0, "ecrs: the parallel depth wrapped");
}

// wrapper: names the parallel bookkeeping the schedules keep
/// Ditto
package void exitParallel(ref Context self) @trusted {
	assert(core.atomic.atomicLoad(bc.platform.asShared(self.parallelDepth)) > 0, "ecrs: leaving a parallel schedule that did not begin");
	core.atomic.atomicOp!"-="(bc.platform.asShared(self.parallelDepth), 1);
}

private enum string structuralChange = "ecrs: structural change inside a parallel schedule; make it after the pass, or between `beginExclusive` and `endExclusive`";

/// Marks `self` as held by the calling thread alone until the matching `endExclusive`, so structural changes it makes meanwhile are allowed even inside an `ecrs.schedules` parallel combinator.
/// The caller guarantees what the mark claims: every other thread stays out of the store, reading included, until it ends, as a stop-the-world protocol of the caller's own keeps them.
/// Marks nest, and the phase `beginConcurrentWrites` opens still forbids adding or removing entities and storages.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// beginExclusive(context);
/// assert(inExclusive(context) && addEntity(context) != invalidEntity);
/// endExclusive(context);
/// assert(!inExclusive(context));
/// ---
void beginExclusive(ref Context self) {
	assert(self.exclusiveDepth < size_t.max, "ecrs: the exclusive depth would wrap");
	++self.exclusiveDepth;
	assert(structureFree(self), "ecrs: an exclusive hold that does not free structural changes");
}

/// Ditto
void endExclusive(ref Context self) {
	assert(self.exclusiveDepth, "ecrs: endExclusive without beginExclusive");
	--self.exclusiveDepth;
}

/// Whether a `beginExclusive` on `self` is still open.
///
/// Examples:
/// ---
/// Context context = create();
/// assert(!inExclusive(context));
/// free(context);
/// ---
bool inExclusive(const ref Context self) {
	return self.exclusiveDepth != 0;
}

// Whether a structural change may happen now: outside parallel combinators, or inside an exclusive hold.
private bool structureFree(const ref Context self) {
	return self.exclusiveDepth != 0 || !inParallel(self);
}
private enum string concurrentStructure = "ecrs: an entity or storage added or removed during concurrent writes; make it before `beginConcurrentWrites`";
private enum string unprepared = "ecrs: a concurrent addition to a storage `reserveConcurrentAdds` did not prepare";


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
	/// Context context = create();
	/// scope(exit) free(context);
	/// EntityRange range = entities(context);
	/// assert(!range.empty && range.front == invalidEntity);
	/// range.popFront();
	/// assert(range.empty);
	/// ---
	bool empty() const @trusted @nogc nothrow { return index >= fp.dynarray.length(context.indexTable); }
	/// Ditto
	EntityId front() const @nogc nothrow {
		assert(!empty, "ecrs: front of a finished entity range");
		return cast(EntityId) index;
	}
	/// Ditto
	void popFront() @nogc nothrow {
		assert(!empty, "ecrs: popFront of a finished entity range");
		++index;
		skipFreed(this);
	}
}

private void skipFreed(ref EntityRange range) @trusted {
	assert(range.context !is null, "ecrs: an entity range over no context");
	while (!range.empty && freelistContains(range.context.freelist, range.index))
		++range.index;
	assert(range.empty || !freelistContains(range.context.freelist, range.index), "ecrs: an entity range stopped on a freed entity");
}

/// Every live entity of `self` in id order, the reserved entity 0 included.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// size_t count = 0;
/// foreach (entity; entities(context)) ++count;
/// assert(count == 2);
/// ---
EntityRange entities(const ref Context self) {
	EntityRange range = EntityRange(&self, 0);
	skipFreed(range);
	assert(range.empty || range.index == invalidEntity, "ecrs: an entity range that skipped the reserved entity");
	return range;
}


private ref ecrs.storage.Storage existingStorage(ref Context self, size_t componentId) @trusted {
	assert(fp.dynarray.length(self.storages) > componentId, "ecrs: a storage past those made");
	assert(self.storages[componentId].elementSize != ecrs.storage.Storage.unknownSize, "ecrs: a storage never made");
	return self.storages[componentId];
}
private ref const(ecrs.storage.Storage) existingStorage(const ref Context self, size_t componentId) @trusted {
	assert(fp.dynarray.length(self.storages) > componentId, "ecrs: a storage past those made");
	assert(self.storages[componentId].elementSize != ecrs.storage.Storage.unknownSize, "ecrs: a storage never made");
	return self.storages[componentId];
}

private bool hasStorage(const ref Context self, size_t componentId) @trusted {
	return componentId < fp.dynarray.length(self.storages)
		&& self.storages[componentId].elementSize != ecrs.storage.Storage.unknownSize;
}

// wrapper: names reserving entity 0, which every context holds
private bool reserveInvalidEntity(ref Context self) @trusted {
	assert(fp.dynarray.length(self.indexTable) == invalidEntity, "ecrs: the invalid entity reserved after others");
	immutable reserved = fp.dynarray.pushBack(self.indexTable, cast(ecrs.storage.IndexList) null);
	assert(!reserved || fp.dynarray.length(self.indexTable) == invalidEntity + 1, "ecrs: reserving the invalid entity made the wrong number of entities");
	return reserved;
}


// --- transactions ------------------------------------------------------------

private enum size_t savedAlignment = 16;

private enum string notInTransaction = "ecrs: renumbering or sorting inside a transaction; commit or roll it back first";

// wrapper: reads a private field
/// Whether a transaction is open on `self`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(!inTransaction(context));
/// beginTransaction(context);
/// assert(inTransaction(context));
/// commitTransaction(context);
/// ---
bool inTransaction(const ref Context self) { return self.transaction; }

/// Opens a transaction on `self`, which must not have one open: from here every change through this module is journaled, until `commitTransaction` keeps them or `rollbackTransaction` undoes them.
/// It cannot fail; the journal allocates as changes are made, and a change whose entry cannot be allocated fails, leaving `self` as it was.
///
/// Inside a transaction, `addEntity` never reuses a freed id, removing an entity or component keeps its storage until the commit, and a component's existing value is replaced only through `setComponent`: a write through a pointer from `getComponent` is not journaled, so a rollback does not undo it.
/// Renumbering and sorting are not allowed.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// beginTransaction(context);
/// EntityId e = addEntity(context);
/// rollbackTransaction(context);
/// assert(entityCount(context) == 1 && e == 1);
/// ---
void beginTransaction(ref Context self) {
	assert(!self.transaction, "ecrs: transactions do not nest");
	assert(structureFree(self), structuralChange);
	self.transaction = true;
	self.firstNew = fp.dynarray.length(self.indexTable);
	assert(fp.dynarray.length(bc.monitor.read(self.journal).value.entries) == 0, "ecrs: a transaction began over another's journal");
}

private bool reserveJournal(ref Journal journal, size_t n) @trusted {
	assert(n > 0, "ecrs: reserving room for no journal entries");
	immutable reserved = fp.dynarray.reserveAtLeast(journal.entries, fp.dynarray.length(journal.entries) + n) !is null;
	assert(!reserved || fp.dynarray.capacity(journal.entries) >= fp.dynarray.length(journal.entries) + n, "ecrs: reserved too little journal");
	return reserved;
}

// Appends an entry; the caller has reserved room for it with `reserveJournal`.
private void record(ref Journal journal, JournalEntry entry) @trusted {
	assert(fp.dynarray.capacity(journal.entries) > fp.dynarray.length(journal.entries), "ecrs: a journal entry recorded without room reserved for it");
	immutable recorded = fp.dynarray.pushBack(journal.entries, entry);
	assert(recorded, "ecrs: a journal entry refused despite its reserved room");
}

// Before the transaction's first `add` to `storage`, whose lock the caller holds, records where a rollback restores it.
// False if the journal cannot grow.
private bool journalStorage(ref Context self, ref ecrs.storage.Storage storage, size_t componentId) @trusted {
	assert(self.transaction, "ecrs: journalling a storage outside a transaction");
	if (storage.journaled) return true;
	auto journal = bc.monitor.write(self.journal);
	if (!reserveJournal(journal.value, 1)) return false;
	record(journal.value, JournalEntry(JournalKind.touchedStorage, invalidEntity, componentId, ecrs.storage.slotCount(storage), ecrs.storage.holeCount(storage)));
	storage.journaled = true;
	return true;
}

// Empties `journal`, which the caller holds as `self`'s.
private void endTransaction(ref Context self, ref Journal journal) @trusted {
	foreach (entry; fp.dynarray.slice(journal.entries))
		if (entry.kind == JournalKind.touchedStorage) existingStorage(self, entry.componentId).journaled = false;
	fp.dynarray.clear(journal.entries);
	fp.dynarray.clear(journal.saved);
	self.transaction = false;
	foreach (i; 0 .. fp.dynarray.length(self.storages)) assert(!self.storages[i].journaled, "ecrs: a storage still journaled after its transaction");
}

/// Closes the open transaction on `self`, keeping its changes: what it removed is finalized and freed, and the old values `setComponent` replaced end their lifetimes.
/// It cannot fail.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// *addComponent!int(context, e) = 1;
/// beginTransaction(context);
/// assert(setComponent!int(context, e, 2));
/// commitTransaction(context);
/// assert(getComponent!int(context, e) == 2 && !inTransaction(context));
/// ---
void commitTransaction(ref Context self) @trusted {
	assert(self.transaction, "ecrs: committing outside a transaction");
	assert(!self.concurrent, "ecrs: committing during concurrent writes");
	auto journal = bc.monitor.write(self.journal);
	foreach (entry; fp.dynarray.slice(journal.value.entries)) final switch (entry.kind) {
		case JournalKind.touchedStorage:
			break;
		case JournalKind.removedEntity:
			fp.dynarray.free(self.indexTable[entry.e]);
			self.indexTable[entry.e] = null;
			break;
		case JournalKind.removedComponent:
			ecrs.storage.release(existingStorage(self, entry.componentId), entry.slot);
			break;
		case JournalKind.replacedComponent:
			ecrs.storage.finalizeBytes(existingStorage(self, entry.componentId), journal.value.saved + entry.saved);
			break;
	}
	endTransaction(self, journal.value);
	assert(validate(self), "ecrs: a transaction left the store's invariants broken");
}

/// Closes the open transaction on `self`, undoing its changes in reverse order, so every entity and component is as it was when it began, holes included: each storage it added to goes back to its size and holes then, and the entities it added are cut from the table.
/// Storage generations still advance, and storages and index-list room it grew stay allocated.
/// It cannot fail.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// *addComponent!int(context, e) = 1;
/// beginTransaction(context);
/// assert(setComponent!int(context, e, 2));
/// assert(removeComponent!int(context, e));
/// assert(addComponent!short(context, e) !is null);
/// rollbackTransaction(context);
/// assert(getComponent!int(context, e) == 1 && !hasComponent!short(context, e));
/// ---
void rollbackTransaction(ref Context self) @trusted {
	assert(self.transaction, "ecrs: rolling back outside a transaction");
	assert(!self.concurrent, "ecrs: rolling back during concurrent writes");
	auto journal = bc.monitor.write(self.journal);
	foreach_reverse (entry; fp.dynarray.slice(journal.value.entries)) final switch (entry.kind) {
		case JournalKind.touchedStorage:
			ecrs.storage.restore(existingStorage(self, entry.componentId), entry.componentId, self.indexTable, entry.slot, entry.saved);
			break;
		case JournalKind.removedEntity:
			assert(fp.dynarray.length(self.freelist) > 0 && *fp.dynarray.back(self.freelist) == entry.e, "ecrs: a removed entity missing from the end of the freelist");
			cast(void) fp.dynarray.removeLast(self.freelist);
			break;
		case JournalKind.removedComponent:
			// An addition after the removal gave `e` a new slot, which its storage's `touchedStorage` reclaims further on.
			if (hasComponent(self, entry.e, entry.componentId)) cast(void) ecrs.storage.detach(existingStorage(self, entry.componentId), entry.componentId, self.indexTable, entry.e);
			ecrs.storage.reattach(existingStorage(self, entry.componentId), entry.componentId, self.indexTable, entry.e, entry.slot);
			break;
		case JournalKind.replacedComponent:
			auto storage = &existingStorage(self, entry.componentId);
			void* p = ecrs.storage.getForWriting(*storage, entry.slot);
			ecrs.storage.finalizeBytes(*storage, p);
			fp.pointer.copy((cast(ubyte*) p)[0 .. storage.elementSize], journal.value.saved[entry.saved .. entry.saved + storage.elementSize]);
			break;
	}
	// The entities it added are the tail of the table; restoring their storages has taken every component off them.
	foreach (e; self.firstNew .. fp.dynarray.length(self.indexTable)) fp.dynarray.free(self.indexTable[e]);
	cast(void) fp.dynarray.removeLast(self.indexTable, fp.dynarray.length(self.indexTable) - self.firstNew);
	endTransaction(self, journal.value);
	assert(validate(self), "ecrs: a transaction left the store's invariants broken");
}


/// Readies the storage of component `componentId`, making it with `elementSize`-byte elements if need be, for up to `n` additions during concurrent writes: slots are made now and handed out without a lock then, so nothing another thread reads moves.
/// Within one phase an entity takes one new slot per component it gains, even one it held before the phase and lost in it, so `n` is the number of entities the writers change unless one gains the same component twice.
/// Inside a transaction the storage is journaled now.
/// Call it, outside the phase, for every storage the writers add to.
///
/// Returns false if allocation fails, leaving the storage able to be prepared again.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(reserveConcurrentAdds(context, ecrs.registry.componentId!int(), 8, int.sizeof));
/// beginConcurrentWrites(context);
/// endConcurrentWrites(context);
/// ---
bool reserveConcurrentAdds(ref Context self, size_t componentId, size_t n, size_t elementSize = ecrs.storage.Storage.unknownSize) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.concurrent, concurrentStructure);
	immutable size = elementSize == ecrs.storage.Storage.unknownSize ? ecrs.registry.elementSizeOf(componentId) : elementSize;
	assert(size != ecrs.storage.Storage.unknownSize, "ecrs: reserving additions of a component of unknown size");
	auto storage = getStorage(self, componentId, size);
	immutable reserved = storage !is null && (!self.transaction || journalStorage(self, *storage, componentId)) && ecrs.storage.prepareClaims(*storage, n);
	assert(!reserved || n == 0 || storage.claimLimit >= n, "ecrs: reserved fewer additions than asked for");
	return reserved;
}

/// Ditto, for component `(T, unique)`.
/// Returns false also if `T` cannot be registered.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(reserveConcurrentAdds!int(context, 8));
/// beginConcurrentWrites(context);
/// endConcurrentWrites(context);
/// ---
template reserveConcurrentAdds(T, size_t unique = 0) {
	bool reserveConcurrentAdds(ref Context self, size_t n) {
		immutable id = ecrs.registry.componentId!(T, unique)();
		return id != fp.pointer.notFound && .reserveConcurrentAdds(self, id, n, T.sizeof);
	}
}

/// Gives back every addition `reserveConcurrentAdds` prepared and no concurrent writes used, as when a step after the reservation fails before `beginConcurrentWrites`; until then, ordinary additions to those storages would take the prepared slots.
/// Storages without a reservation are left alone, and it cannot fail.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(reserveConcurrentAdds!int(context, 8));
/// cancelConcurrentAdds(context);
/// EntityId e = addEntity(context);
/// assert(addComponent!int(context, e) !is null && ecrs.storage.liveCount(*getStorage!int(context)) == 1);
/// ---
void cancelConcurrentAdds(ref Context self) @trusted {
	assert(!self.concurrent, "ecrs: cancelling reservations during concurrent writes; endConcurrentWrites gives them back");
	foreach (i; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[i].elementSize != ecrs.storage.Storage.unknownSize) ecrs.storage.endClaims(self.storages[i]);
	foreach (i; 0 .. fp.dynarray.length(self.storages)) assert(!self.storages[i].claimLimit, "ecrs: a storage still reserved after cancelling");
}

/// Opens a phase in which several threads may add, set and remove components of existing entities at once, until `endConcurrentWrites`: each entity is changed by one thread at a time, each storage they add to has been readied by `reserveConcurrentAdds`, and removals happen only inside a transaction, which keeps their slots until it ends.
/// Meanwhile no entity or storage may be added or removed, nor anything renumbered or sorted.
/// The phase may enclose `ecrs.schedules` parallel combinators, whose schedules may then make these writes, but must open and close outside them.
/// Inside a transaction the changes are journaled as ever, so a rollback undoes them; the journal is the one lock writers share.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(reserveConcurrentAdds!int(context, 1) && reserveConcurrentAdds!short(context, 1));
/// beginConcurrentWrites(context);
/// assert(setComponent!int(context, e, 3) && setComponent!short(context, e, 4)); // from any thread, each with its own entities
/// endConcurrentWrites(context);
/// assert(getComponent!int(context, e) == 3);
/// ---
void beginConcurrentWrites(ref Context self) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.concurrent, "ecrs: concurrent writes do not nest");
	self.concurrent = true;
	foreach (i; 0 .. fp.dynarray.length(self.storages)) self.storages[i].quiet = true;
}

/// Closes the phase `beginConcurrentWrites` opened, every thread writing in it having finished, and gives back the slots prepared storages did not use.
/// It cannot fail.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// beginConcurrentWrites(context);
/// endConcurrentWrites(context);
/// ---
void endConcurrentWrites(ref Context self) @trusted {
	assert(structureFree(self), structuralChange);
	assert(self.concurrent, "ecrs: ending concurrent writes that did not begin");
	self.concurrent = false;
	foreach (i; 0 .. fp.dynarray.length(self.storages)) {
		ecrs.storage.endQuiet(self.storages[i]);
		ecrs.storage.endClaims(self.storages[i]);
	}
	foreach (i; 0 .. fp.dynarray.length(self.storages)) assert(!self.storages[i].quiet && !self.storages[i].claimLimit, "ecrs: a storage left quiet or claiming after concurrent writes");
}

/// A context with the invalid entity, id 0, already reserved.
/// Use it rather than `Context.init`.
/// It cannot fail: if it cannot allocate, the first `addEntity` reserves entity 0 instead.
///
/// Examples:
/// ---
/// Context context = create();
/// assert(entityCount(context) == 1);
/// free(context);
/// ---
Context create() {
	Context c;
	cast(void) reserveInvalidEntity(c);
	assert(entityCount(c) <= 1 && !c.transaction && !c.concurrent, "ecrs: a new context that is not empty and idle");
	return c;
}

/// Ends every component's lifetime and frees everything `self` owns, leaving it as `Context.init`.
/// An open transaction is committed first.
///
/// Examples:
/// ---
/// Context context = create();
/// free(context);
/// assert(entityCount(context) == 0);
/// ---
void free(ref Context self) @trusted {
	assert(!self.concurrent, "ecrs: freeing a context during concurrent writes");
	assert(!inParallel(self), "ecrs: freeing a context inside a parallel schedule");
	if (self.transaction) commitTransaction(self);
	{
		auto journal = bc.monitor.write(self.journal);
		fp.dynarray.free(journal.value.entries);
		fp.dynarray.free(journal.value.saved);
	}
	foreach (i; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[i].elementSize != ecrs.storage.Storage.unknownSize)
			ecrs.storage.free(self.storages[i]);
	fp.dynarray.free(self.storages);
	foreach (i; 0 .. fp.dynarray.length(self.indexTable))
		fp.dynarray.free(self.indexTable[i]);
	fp.dynarray.free(self.indexTable);
	fp.dynarray.free(self.freelist);
	fp.dynarray.free(self.remapHooks);
	self = Context.init;
}


/// The storage for component `componentId`, created on first use with `elementSize`-byte elements and the hooks its type registered.
/// The pointer is valid until another storage is created.
///
/// Returns null if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// auto storage = getStorage(context, ecrs.registry.componentId!int(), int.sizeof);
/// assert(storage !is null && ecrs.storage.empty(*storage));
/// ---
ecrs.storage.Storage* getStorage(ref Context self, size_t componentId, size_t elementSize) @trusted {
	if (hasStorage(self, componentId)) return &self.storages[componentId];
	assert(structureFree(self), structuralChange);
	assert(!self.concurrent, concurrentStructure);
	assert(elementSize != ecrs.storage.Storage.unknownSize, "ecrs: component of unknown size");

	immutable count = fp.dynarray.length(self.storages);
	if (componentId >= count) {
		if (fp.dynarray.growToSize(self.storages, componentId + 1) is null) return null;
		foreach (i; count .. componentId + 1) self.storages[i] = ecrs.storage.Storage.init;
	}
	immutable hooks = ecrs.registry.hooksOf(componentId);
	self.storages[componentId] = ecrs.storage.create(elementSize, hooks.finalizer, hooks.remapFunction);
	assert(hasStorage(self, componentId) && self.storages[componentId].elementSize == elementSize, "ecrs: made a storage of the wrong size");
	return &self.storages[componentId];
}

/// Ditto, for a const context, which cannot create one: returns null if no entity has had the component.
/// `elementSize`, unless `Storage.unknownSize`, is checked against the storage's.
///
/// Examples:
/// ---
/// const Context context = create();
/// assert(getStorage(context, ecrs.registry.componentId!int()) is null);
/// ---
const(ecrs.storage.Storage)* getStorage(const ref Context self, size_t componentId, size_t elementSize = ecrs.storage.Storage.unknownSize) @trusted {
	if (!hasStorage(self, componentId)) return null;
	assert(elementSize == ecrs.storage.Storage.unknownSize || elementSize == self.storages[componentId].elementSize, "ecrs: a storage asked for with the wrong element size");
	return &self.storages[componentId];
}

/// Ditto, for component `(T, unique)`.
/// Returns null also if `T` cannot be registered.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(getStorage!int(context) !is null);
/// ---
template getStorage(T, size_t unique = 0) {
	ecrs.storage.Storage* getStorage(ref Context self) {
		immutable id = ecrs.registry.componentId!(T, unique)();
		return id == fp.pointer.notFound ? null : .getStorage(self, id, T.sizeof);
	}
}

// wrapper: reads a private field
/// One past the highest component id `self` has room for, so `getStorage` over `0 .. storageCount` visits every storage it has.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// immutable id = ecrs.registry.componentId!int();
/// assert(getStorage(context, id, int.sizeof) !is null);
/// assert(storageCount(context) > id);
/// ---
size_t storageCount(const ref Context self) @trusted {
	return fp.dynarray.length(self.storages);
}

/// `ecrs.storage.generation` of component `componentId`'s storage, or 0 if no entity has had the component.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// immutable id = ecrs.registry.componentId!int();
/// assert(generation(context, id) == 0);
/// assert(addComponent(context, addEntity(context), id) !is null);
/// assert(generation(context, id) > 0);
/// ---
size_t generation(const ref Context self, size_t componentId) {
	auto storage = getStorage(self, componentId);
	return storage is null ? 0 : ecrs.storage.generation(*storage);
}

/// A counter that advances whenever any component of `self` changes, as the per-component `generation` does for one: the sum of every storage's.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// immutable before = generation(context);
/// assert(addComponent!int(context, addEntity(context)) !is null);
/// assert(generation(context) > before);
/// ---
size_t generation(const ref Context self) @trusted {
	size_t sum = 0;
	foreach (i; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[i].elementSize != ecrs.storage.Storage.unknownSize)
			sum += ecrs.storage.generation(self.storages[i]);
	return sum;
}


/// The number of live entities, the reserved entity 0 included.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// cast(void) addEntity(context);
/// assert(entityCount(context) == 2);
/// ---
size_t entityCount(const ref Context self) @trusted {
	assert(fp.dynarray.length(self.freelist) <= fp.dynarray.length(self.indexTable), "ecrs: more freed entities than entities");
	return fp.dynarray.length(self.indexTable) - fp.dynarray.length(self.freelist);
}

/// A new entity with no components, reusing the most recently freed id if there is one, unless a transaction is open.
///
/// Returns `invalidEntity` if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(e == 1);
/// ---
EntityId addEntity(ref Context self) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.concurrent, concurrentStructure);
	if (self.transaction) {
		// Never a freed id: a rollback removes what the transaction added by cutting the table back to `firstNew`.
		if (fp.dynarray.reserveAtLeast(self.indexTable, fp.dynarray.length(self.indexTable) + 2) is null) return invalidEntity;
		if (fp.dynarray.length(self.indexTable) == 0) cast(void) reserveInvalidEntity(self); // reserved above
		immutable e = cast(EntityId) fp.dynarray.length(self.indexTable);
		cast(void) fp.dynarray.pushBack(self.indexTable, cast(ecrs.storage.IndexList) null); // reserved above
		assert(e >= self.firstNew && e != invalidEntity, "ecrs: a transaction gave out an id from before it began");
		return e;
	}
	if (fp.dynarray.length(self.indexTable) == 0 && !reserveInvalidEntity(self)) return invalidEntity;
	if (fp.dynarray.length(self.freelist) > 0) {
		immutable e = *fp.dynarray.back(self.freelist);
		cast(void) fp.dynarray.removeLast(self.freelist);
		assert(e != invalidEntity && e < fp.dynarray.length(self.indexTable), "ecrs: a freed id past the table");
		assert(self.indexTable[e] is null, "ecrs: a freed entity still holding its index list");
		return cast(EntityId) e;
	}
	immutable e = cast(EntityId) fp.dynarray.length(self.indexTable);
	assert(e < EntityId.max, "ecrs: entity ids exhausted");
	if (!fp.dynarray.pushBack(self.indexTable, cast(ecrs.storage.IndexList) null)) return invalidEntity;
	return e;
}

/// Adds `n` live entities with consecutive ids and no components, returning the first; unlike `addEntity` it never reuses a freed id, so the run is contiguous whatever was removed.
/// Inside a transaction a rollback removes them, as it does what `addEntity` adds.
///
/// Returns `invalidEntity` if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// immutable first = addEntities(context, 3);
/// assert(first == 1 && entityCount(context) == 4);
/// ---
EntityId addEntities(ref Context self, size_t n) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.concurrent, concurrentStructure);
	if (fp.dynarray.reserveAtLeast(self.indexTable, fp.dynarray.length(self.indexTable) + n + 1) is null) return invalidEntity;
	if (fp.dynarray.length(self.indexTable) == 0) cast(void) reserveInvalidEntity(self); // reserved above
	immutable first = cast(EntityId) fp.dynarray.length(self.indexTable);
	assert(first != invalidEntity && first + n <= EntityId.max, "ecrs: entity ids exhausted");
	foreach (i; 0 .. n) cast(void) fp.dynarray.pushBack(self.indexTable, cast(ecrs.storage.IndexList) null); // reserved above
	assert(fp.dynarray.length(self.indexTable) == first + n, "ecrs: added the wrong number of entities");
	return first;
}

/// Removes the live entity `e`, which must not be `invalidEntity`, ending its components' lifetimes; its id goes on the freelist for `addEntity` to hand out again.
///
/// Returns false if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(removeEntity(context, e));
/// assert(entityCount(context) == 1);
/// ---
bool removeEntity(ref Context self, EntityId e) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.concurrent, concurrentStructure);
	assert(e != invalidEntity && e < fp.dynarray.length(self.indexTable), "ecrs: removing an entity the table does not have");
	assert(fp.dynarray.length(self.freelist) == 0 || *fp.dynarray.back(self.freelist) != e, "ecrs: removing an entity twice");
	if (fp.dynarray.reserveAtLeast(self.freelist, fp.dynarray.length(self.freelist) + 1) is null) return false;

	auto indices = self.indexTable[e];
	if (self.transaction) {
		size_t count = 0;
		foreach (componentId; 0 .. fp.dynarray.length(indices))
			if (indices[componentId] != ecrs.storage.Storage.absent) ++count;
		auto journal = bc.monitor.write(self.journal);
		if (!reserveJournal(journal.value, count + 1)) return false;
		// The index list stays, so a rollback can reattach the components; the commit frees it.
		foreach (componentId; 0 .. fp.dynarray.length(indices))
			if (indices[componentId] != ecrs.storage.Storage.absent)
				record(journal.value, JournalEntry(JournalKind.removedComponent, e, componentId, ecrs.storage.detach(self.storages[componentId], componentId, self.indexTable, e)));
		record(journal.value, JournalEntry(JournalKind.removedEntity, e));
		cast(void) fp.dynarray.pushBack(self.freelist, cast(size_t) e); // reserved above
		return true;
	}
	foreach (componentId; 0 .. fp.dynarray.length(indices))
		if (indices[componentId] != ecrs.storage.Storage.absent)
			cast(void) ecrs.storage.remove(self.storages[componentId], componentId, self.indexTable, e);
	fp.dynarray.free(self.indexTable[e]);
	self.indexTable[e] = null;
	cast(void) fp.dynarray.pushBack(self.freelist, cast(size_t) e); // reserved above
	assert(*fp.dynarray.back(self.freelist) == e, "ecrs: a removed entity missing from the freelist");
	return true;
}


/// Whether entity `e` has component `componentId`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(!hasComponent(context, e, ecrs.registry.componentId!int()));
/// ---
bool hasComponent(const ref Context self, EntityId e, size_t componentId) @trusted {
	return e < fp.dynarray.length(self.indexTable)
		&& fp.dynarray.length(self.indexTable[e]) > componentId
		&& self.indexTable[e][componentId] != ecrs.storage.Storage.absent;
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(addComponent!int(context, e) !is null);
/// assert(hasComponent!int(context, e));
/// ---
template hasComponent(T, size_t unique = 0) {
	bool hasComponent(const ref Context self, EntityId e) {
		return .hasComponent(self, e, ecrs.registry.componentId!(T, unique)());
	}
}

/// Gives the live entity `e`, which must not have it yet, component `componentId`, zero-filled since there is no type to construct; prefer the typed form when the type is known.
/// `elementSize` defaults to the registered size.
///
/// The component's address is stable until it is removed or a renumbering or sort moves it; adding other components, of any type, never does.
///
/// Returns null if allocation fails, leaving `e` without the component.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// int* p = cast(int*) addComponent(context, e, ecrs.registry.componentId!int());
/// assert(p !is null && *p == 0);
/// ---
void* addComponent(ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.unknownSize) {
	assert(self.concurrent || structureFree(self), structuralChange);
	assert(!hasComponent(self, e, componentId), "ecrs: adding a component the entity already has");
	assert(e != invalidEntity && e < fp.dynarray.length(self.indexTable), "ecrs: adding a component to an entity the table does not have");
	if (self.writeObserver !is null) self.writeObserver(self.writeObserverData, e, componentId);
	immutable size = elementSize == ecrs.storage.Storage.unknownSize ? ecrs.registry.elementSizeOf(componentId) : elementSize;
	auto storage = getStorage(self, componentId, size);
	if (storage is null) return null;
	assert(!self.concurrent || storage.claimLimit, unprepared);
	if (self.transaction && !journalStorage(self, *storage, componentId)) return null;
	auto added = ecrs.storage.add(*storage, componentId, self.indexTable, e);
	assert(added is null || hasComponent(self, e, componentId), "ecrs: an added component the entity does not have");
	return added;
}

/// Ditto, for component `(T, unique)`, which starts as `T.init`.
/// Returns null also if `T` cannot be registered.
///
/// Examples:
/// ---
/// static struct Position { float x = 1, y = 2; }
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// Position* p = addComponent!Position(context, e);
/// assert(p !is null && p.y == 2);
/// ---
template addComponent(T, size_t unique = 0) {
	T* addComponent(ref Context self, EntityId e) {
		assert(self.concurrent || structureFree(self), structuralChange);
		assert(!.hasComponent!(T, unique)(self, e), "ecrs: adding a component the entity already has");
		assert(e != invalidEntity, "ecrs: adding a component to the invalid entity");
		if (self.writeObserver !is null) self.writeObserver(self.writeObserverData, e, ecrs.registry.componentId!(T, unique)());
		auto storage = .getStorage!(T, unique)(self);
		if (storage is null) return null;
		assert(!self.concurrent || storage.claimLimit, unprepared);
		if (self.transaction && !journalStorage(self, *storage, ecrs.registry.componentId!(T, unique)())) return null;
		auto added = ecrs.storage.add!(T, unique)(*storage, self.indexTable, e);
		assert(added is null || .hasComponent!(T, unique)(self, e), "ecrs: an added component the entity does not have");
		return added;
	}
}

/// Removes entity `e`'s component `componentId`, which it must have, ending its lifetime; inside a transaction, the commit ends it.
///
/// Returns false only inside a transaction, if its journal cannot grow, leaving `e` as it was; outside one it cannot fail.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// immutable id = ecrs.registry.componentId!int();
/// assert(addComponent(context, e, id) !is null);
/// assert(removeComponent(context, e, id));
/// assert(!hasComponent(context, e, id));
/// ---
bool removeComponent(ref Context self, EntityId e, size_t componentId) {
	assert(self.concurrent || structureFree(self), structuralChange);
	assert(hasComponent(self, e, componentId), "ecrs: removing a component the entity does not have");
	if (self.writeObserver !is null) self.writeObserver(self.writeObserverData, e, componentId);
	auto storage = &existingStorage(self, componentId);
	assert(!self.concurrent || self.transaction, "ecrs: concurrent writes remove components only inside a transaction, which keeps their slots until it ends");
	if (!self.transaction) return ecrs.storage.remove(*storage, componentId, self.indexTable, e);
	auto journal = bc.monitor.write(self.journal);
	if (!reserveJournal(journal.value, 1)) return false;
	record(journal.value, JournalEntry(JournalKind.removedComponent, e, componentId, ecrs.storage.detach(*storage, componentId, self.indexTable, e)));
	assert(!hasComponent(self, e, componentId), "ecrs: a removed component the entity still has");
	return true;
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(addComponent!int(context, e) !is null);
/// assert(removeComponent!int(context, e));
/// assert(!hasComponent!int(context, e));
/// ---
template removeComponent(T, size_t unique = 0) {
	bool removeComponent(ref Context self, EntityId e) {
		return .removeComponent(self, e, ecrs.registry.componentId!(T, unique)());
	}
}
/// Removes component `componentId` from every entity that has it, ending each one's lifetime; inside a transaction, the commit ends them.
///
/// Returns false only inside a transaction, if its journal cannot grow, removing nothing; outside one it cannot fail.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// immutable id = ecrs.registry.componentId!int();
/// assert(addComponent(context, e, id) !is null);
/// assert(clearComponent(context, id));
/// assert(!hasComponent(context, e, id));
/// ---
bool clearComponent(ref Context self, size_t componentId) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.concurrent, concurrentStructure);
	if (!hasStorage(self, componentId)) return true;
	auto storage = &self.storages[componentId];
	if (self.transaction) {
		auto journal = bc.monitor.write(self.journal);
		if (!reserveJournal(journal.value, ecrs.storage.liveCount(*storage))) return false;
		foreach (slot; 0 .. ecrs.storage.slotCount(*storage)) {
			immutable slotOwner = ecrs.storage.owner(*storage, slot);
			if (slotOwner != invalidEntity)
				record(journal.value, JournalEntry(JournalKind.removedComponent, slotOwner, componentId, ecrs.storage.detach(*storage, componentId, self.indexTable, slotOwner)));
		}
		assert(ecrs.storage.empty(*storage), "ecrs: clearComponent left components");
		return true;
	}
	// Descending, so popping the last slot never skips an owner.
	foreach_reverse (slot; 0 .. ecrs.storage.slotCount(*storage)) {
		immutable slotOwner = ecrs.storage.owner(*storage, slot);
		if (slotOwner != invalidEntity)
			cast(void) ecrs.storage.remove(*storage, componentId, self.indexTable, slotOwner);
	}
	assert(ecrs.storage.empty(*storage), "ecrs: clearComponent left components");
	return true;
}

/// Entity `e`'s component `componentId`, which it must have, for reading; reading counts no change.
/// `elementSize`, unless `Storage.unknownSize`, is checked against the storage's.
/// Write through `getForWriting` or `setComponent`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// immutable id = ecrs.registry.componentId!int();
/// void* added = addComponent(context, e, id);
/// assert(getComponent(context, e, id) is added);
/// ---
const(void)* getComponent(const ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.unknownSize) @trusted {
	assert(hasComponent(self, e, componentId), "ecrs: reading a component the entity does not have");
	auto storage = &existingStorage(self, componentId);
	assert(elementSize == ecrs.storage.Storage.unknownSize || elementSize == storage.elementSize, "ecrs: reading a component as the wrong type");
	assert(ecrs.storage.owner(*storage, self.indexTable[e][componentId]) == e, "ecrs: an index naming a slot another entity owns");
	return ecrs.storage.get(*storage, self.indexTable[e][componentId]);
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// *addComponent!int(context, e) = 3;
/// assert(getComponent!int(context, e) == 3);
/// ---
template getComponent(T, size_t unique = 0) {
	ref const(T) getComponent(const ref Context self, EntityId e) @trusted {
		return *cast(const(T)*) .getComponent(self, e, ecrs.registry.componentId!(T, unique)(), T.sizeof);
	}
}

/// Entity `e`'s component `componentId`, or null if `e` lacks it, for reading; reading counts no change.
/// `elementSize`, unless `Storage.unknownSize`, is checked against the storage's.
/// The address is stable on the terms `addComponent` gives.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// immutable id = ecrs.registry.componentId!int();
/// assert(findComponent(context, e, id) is null);
/// void* added = addComponent(context, e, id);
/// assert(findComponent(context, e, id) is added);
/// ---
const(void)* findComponent(const ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.unknownSize) @trusted {
	if (!hasComponent(self, e, componentId)) return null;
	return getComponent(self, e, componentId, elementSize);
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(findComponent!int(context, e) is null);
/// *addComponent!int(context, e) = 3;
/// if (auto p = findComponent!int(context, e)) assert(*p == 3);
/// ---
template findComponent(T, size_t unique = 0) {
	const(T)* findComponent(const ref Context self, EntityId e) @trusted {
		return cast(const(T)*) .findComponent(self, e, ecrs.registry.componentId!(T, unique)(), T.sizeof);
	}
}

/// Entity `e`'s component `componentId`, which it must have, for writing in place: counts a change in its storage, so `untilStable` and `whenChanged` see it.
/// Inside a transaction an in-place write is not journaled, so a rollback keeps a write to a component that predates the transaction; replace such a component with `setComponent`, which is journaled.
/// `elementSize`, unless `Storage.unknownSize`, is checked against the storage's.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// immutable id = ecrs.registry.componentId!int();
/// void* added = addComponent(context, e, id);
/// assert(getForWriting(context, e, id) is added);
/// ---
void* getForWriting(ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.unknownSize) @trusted {
	assert(hasComponent(self, e, componentId), "ecrs: writing a component the entity does not have");
	auto storage = &existingStorage(self, componentId);
	assert(elementSize == ecrs.storage.Storage.unknownSize || elementSize == storage.elementSize, "ecrs: writing a component as the wrong type");
	assert(ecrs.storage.owner(*storage, self.indexTable[e][componentId]) == e, "ecrs: an index naming a slot another entity owns");
	if (self.writeObserver !is null) self.writeObserver(self.writeObserverData, e, componentId);
	return ecrs.storage.getForWriting(*storage, self.indexTable[e][componentId]);
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// *addComponent!int(context, e) = 3;
/// getForWriting!int(context, e) += 1;
/// assert(getComponent!int(context, e) == 4);
/// ---
template getForWriting(T, size_t unique = 0) {
	ref T getForWriting(ref Context self, EntityId e) @trusted {
		return *cast(T*) .getForWriting(self, e, ecrs.registry.componentId!(T, unique)(), T.sizeof);
	}
}

/// Entity `e`'s component `componentId`, or null if `e` lacks it, for writing in place, on the terms `getForWriting` gives.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// immutable id = ecrs.registry.componentId!int();
/// assert(findForWriting(context, e, id) is null);
/// void* added = addComponent(context, e, id);
/// assert(findForWriting(context, e, id) is added);
/// ---
void* findForWriting(ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.unknownSize) @trusted {
	if (!hasComponent(self, e, componentId)) return null;
	return getForWriting(self, e, componentId, elementSize);
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(findForWriting!int(context, e) is null);
/// *addComponent!int(context, e) = 3;
/// if (auto p = findForWriting!int(context, e)) *p = 4;
/// assert(getComponent!int(context, e) == 4);
/// ---
template findForWriting(T, size_t unique = 0) {
	T* findForWriting(ref Context self, EntityId e) @trusted {
		return cast(T*) .findForWriting(self, e, ecrs.registry.componentId!(T, unique)(), T.sizeof);
	}
}

/// Entity `e`'s component `componentId` for writing, as `findForWriting` gives it, added as `addComponent` would if `e` lacks it.
///
/// Returns null if adding fails, leaving `e` without the component.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// immutable id = ecrs.registry.componentId!int();
/// void* p = ensureComponent(context, e, id);
/// assert(p !is null && ensureComponent(context, e, id) is p);
/// ---
void* ensureComponent(ref Context self, EntityId e, size_t componentId, size_t elementSize = ecrs.storage.Storage.unknownSize) {
	if (auto p = findForWriting(self, e, componentId, elementSize)) return p;
	auto added = addComponent(self, e, componentId, elementSize);
	assert(added is null || hasComponent(self, e, componentId), "ecrs: ensured a component the entity does not have");
	return added;
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// int* p = ensureComponent!int(context, e);
/// assert(p !is null && ensureComponent!int(context, e) is p);
/// ---
template ensureComponent(T, size_t unique = 0) {
	T* ensureComponent(ref Context self, EntityId e) {
		if (auto p = .findForWriting!(T, unique)(self, e)) return p;
		return .addComponent!(T, unique)(self, e);
	}
}

/// The component `(T, unique)` of the one entity holding it, for a component kept once per store, such as an index or a system's state; null if no entity holds it.
/// It reads through a `const` store, so it never creates the storage, and any thread may call it while others read.
/// With several holders it gives the first in slot order.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(findSingleton!int(context) is null);
/// *addSingleton!int(context) = 4;
/// assert(*findSingleton!int(context) == 4);
/// ---
template findSingleton(T, size_t unique = 0) {
	const(T)* findSingleton(const ref Context self) @trusted {
		auto storage = getStorage(self, ecrs.registry.componentId!(T, unique)());
		if (storage is null) return null;
		foreach (slot; 0 .. ecrs.storage.slotCount(*storage))
			if (ecrs.storage.owner(*storage, slot) != invalidEntity) return &ecrs.storage.get!T(*storage, slot);
		return null;
	}
}

/// The component `(T, unique)` kept once per store, as `findSingleton` finds it, for writing in place on the terms `getForWriting` gives, or null if there is none.
/// Like `findSingleton`, it never adds a storage, so a thread may call it while others read the store.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(findSingletonForWriting!int(context) is null);
/// cast(void) addSingleton!int(context);
/// *findSingletonForWriting!int(context) = 5;
/// assert(*findSingleton!int(context) == 5);
/// ---
template findSingletonForWriting(T, size_t unique = 0) {
	T* findSingletonForWriting(ref Context self) @trusted {
		auto storage = cast(ecrs.storage.Storage*) getStorage(*cast(const(Context)*) &self, ecrs.registry.componentId!(T, unique)());
		if (storage is null) return null;
		foreach (slot; 0 .. ecrs.storage.slotCount(*storage))
			if (ecrs.storage.owner(*storage, slot) != invalidEntity) {
				if (self.writeObserver !is null) self.writeObserver(self.writeObserverData, ecrs.storage.owner(*storage, slot), ecrs.registry.componentId!(T, unique)());
				return &ecrs.storage.getForWriting!T(*storage, slot);
			}
		return null;
	}
}

/// Adds an entity holding a new, empty component `(T, unique)`, for a component kept once per store, and returns the component for writing; `findSingleton` finds it from then on.
///
/// Returns null if allocation fails, having removed the new entity again, or, if that too was refused, left it empty.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// int* state = addSingleton!int(context);
/// assert(state !is null && *state == 0 && findSingleton!int(context) is state);
/// ---
template addSingleton(T, size_t unique = 0) {
	T* addSingleton(ref Context self) {
		assert(findSingleton!(T, unique)(self) is null, "ecrs: adding a second singleton of one type");
		immutable holder = addEntity(self);
		if (holder == invalidEntity) return null;
		auto component = .addComponent!(T, unique)(self, holder);
		// If even the removal is refused, an empty entity remains that nothing reaches.
		if (component is null) cast(void) removeEntity(self, holder);
		return component;
	}
}

/// Gives entity `e` component `(T, unique)` with `value`, adding it as `addComponent` would or replacing the one it has, whose lifetime ends; inside a transaction the old value is kept until the commit, so a rollback restores it, unless the transaction added `e`, which a rollback removes whole.
/// The component keeps its address, and the old value is moved by its bytes.
/// Takes over `value`'s lifetime.
///
/// Returns false if allocation fails, leaving `e` as it was and ending `value`'s lifetime.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(setComponent!int(context, e, 1));
/// const(int)* p = &getComponent!int(context, e);
/// assert(setComponent!int(context, e, 2));
/// assert(&getComponent!int(context, e) is p && *p == 2);
/// ---
template setComponent(T, size_t unique = 0) {
	bool setComponent(ref Context self, EntityId e, T value) @trusted {
		auto existing = .findForWriting!(T, unique)(self, e);
		if (existing is null) {
			auto p = .addComponent!(T, unique)(self, e);
			if (p is null) {
				fp.lifecycle.endLifetime(value);
				return false;
			}
			fp.lifecycle.moveInto(*p, value);
			return true;
		}
		// An entity the transaction added goes whole on a rollback, so its old value need not be kept for one.
		if (!self.transaction || e >= self.firstNew) {
			fp.lifecycle.moveInto(*existing, value);
			return true;
		}
		immutable id = ecrs.registry.componentId!(T, unique)();
		auto journal = bc.monitor.write(self.journal);
		auto saved = &journal.value.saved;
		immutable offset = (fp.dynarray.length(*saved) + savedAlignment - 1) / savedAlignment * savedAlignment;
		if (!reserveJournal(journal.value, 1) || fp.dynarray.reserveAtLeast(*saved, offset + T.sizeof) is null || fp.dynarray.growToSize(*saved, offset + T.sizeof) is null) {
			fp.lifecycle.endLifetime(value);
			return false;
		}
		assert(offset % savedAlignment == 0 && offset + T.sizeof <= fp.dynarray.length(*saved), "ecrs: a saved value misaligned or past its buffer");
		record(journal.value, JournalEntry(JournalKind.replacedComponent, e, id, self.indexTable[e][id], offset));
		fp.pointer.copy((*saved)[offset .. offset + T.sizeof], (cast(const(ubyte)*) existing)[0 .. T.sizeof]);
		fp.pointer.fill((cast(ubyte*) existing)[0 .. T.sizeof], 0);
		fp.lifecycle.moveInto(*existing, value);
		return true;
	}
}


/// Registers a holder of entity ids outside the store, so every renumbering rewrites it too.
/// `userData` is passed back to `hook` unchanged.
///
/// Returns false if allocation fails, registering nothing.
///
/// Examples:
/// ---
/// static void onRemap(void*, const(EntityId)[]) @nogc nothrow {}
/// Context context = create();
/// scope(exit) free(context);
/// assert(addRemapHook(context, &onRemap, null));
/// ---
bool addRemapHook(ref Context self, RemapHookFunction hook, void* userData) @trusted {
	assert(structureFree(self), structuralChange);
	assert(hook !is null, "ecrs: a remap hook that is no function");
	return fp.dynarray.pushBack(self.remapHooks, RemapHook(hook, userData));
}

/// Unregisters the hook added with exactly `hook` and `userData`, returning false if there is none.
///
/// Examples:
/// ---
/// static void onRemap(void*, const(EntityId)[]) @nogc nothrow {}
/// Context context = create();
/// scope(exit) free(context);
/// assert(addRemapHook(context, &onRemap, null));
/// assert(removeRemapHook(context, &onRemap, null));
/// assert(!removeRemapHook(context, &onRemap, null));
/// ---
bool removeRemapHook(ref Context self, RemapHookFunction hook, void* userData) @trusted {
	assert(structureFree(self), structuralChange);
	foreach (i; 0 .. fp.dynarray.length(self.remapHooks))
		if (self.remapHooks[i].hook is hook && self.remapHooks[i].userData is userData) {
			cast(void) fp.dynarray.removeAt(self.remapHooks, i);
			return true;
		}
	return false;
}


// Renumbers every holder at once: the index lists, storage owners, components with a remap hook, the freelist and external hooks.
private bool renumber(ref Context self, const(size_t)[] order, const(EntityId)[] remap) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.transaction, notInTransaction);
	auto table = self.indexTable;
	// The only step that can fail goes first, so a failure leaves every holder untouched.
	if (!fp.algorithms.applyPermutation(order, (a, b) {
		auto t = table[a];
		table[a] = table[b];
		table[b] = t;
	})) return false;

	foreach (id; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[id].elementSize != ecrs.storage.Storage.unknownSize)
			ecrs.storage.relabel(self.storages[id], remap);
	foreach (i; 0 .. fp.dynarray.length(self.freelist)) {
		assert(self.freelist[i] < remap.length, "ecrs: a freed id past the remap");
		self.freelist[i] = remap[self.freelist[i]];
	}
	foreach (i; 0 .. fp.dynarray.length(self.remapHooks))
		self.remapHooks[i].hook(self.remapHooks[i].userData, remap);
	assert(remap.length == 0 || remap[invalidEntity] == invalidEntity, "ecrs: a renumbering that moved the invalid entity");
	return true;
}

/// Renumbers entities, `order[i]` being the entity that becomes `i`, over the whole entity table, freed ids included.
/// Entity 0 must stay put, so `invalidEntity` keeps its meaning.
/// Every holder of an entity id is rewritten in the same step: component owners, components whose type has a remap hook, the freelist and remap hooks.
/// No component moves, so their addresses survive.
///
/// Returns false if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId a = addEntity(context), b = addEntity(context);
/// *addComponent!int(context, a) = 10;
/// immutable size_t[3] order = [0, 2, 1];
/// assert(reorderEntities(context, order[]));
/// assert(getComponent!int(context, b) == 10);
/// ---
bool reorderEntities(ref Context self, const(size_t)[] order) @trusted {
	assert(order.length == fp.dynarray.length(self.indexTable), "ecrs: an order for a different number of entities");
	assert(order.length == 0 || order[0] == invalidEntity, "ecrs: an order that moves the invalid entity");
	auto remap = ecrs.storage.buildRemap(order);
	if (remap is null) return false;
	scope(exit) cast(void) fp.pointer.allocator(remap, 0);
	if (!renumber(self, order, remap[0 .. order.length])) return false;
	assert(validate(self), "ecrs: a renumbering broke the store's invariants");
	return true;
}

/// Exchanges the ids of entities `a` and `b`, `b` defaulting to the last slot of the entity table, as `reorderEntities` does.
///
/// Returns false if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId a = addEntity(context), b = addEntity(context);
/// *addComponent!int(context, a) = 10;
/// assert(swapEntities(context, a, b));
/// assert(getComponent!int(context, b) == 10);
/// ---
bool swapEntities(ref Context self, EntityId a, EntityId b = EntityId.max) @trusted {
	immutable n = fp.dynarray.length(self.indexTable);
	immutable resolvedB = b == EntityId.max ? cast(EntityId)(n - 1) : b;
	assert(a < n && resolvedB < n, "ecrs: swapping an entity the table does not have");
	assert(a != invalidEntity && resolvedB != invalidEntity, "ecrs: swapping the invalid entity");
	auto order = cast(size_t*) fp.pointer.allocator(null, n * size_t.sizeof);
	if (order is null) return false;
	scope(exit) cast(void) fp.pointer.allocator(order, 0);
	foreach (i; 0 .. n) order[i] = i;
	order[a] = resolvedB;
	order[resolvedB] = a;
	assert(order[a] == resolvedB && order[resolvedB] == a, "ecrs: a swap that does not exchange its two entities");
	return reorderEntities(self, order[0 .. n]);
}

/// Renumbers the live entities to `0 .. entityCount` in their current order and drops the freed ids from the table, emptying the freelist.
/// A reference still naming a freed entity becomes `invalidEntity` rather than an id a later `addEntity` hands out again.
///
/// Returns false if allocation fails, leaving `self` as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId a = addEntity(context), b = addEntity(context);
/// *addComponent!int(context, b) = 10;
/// assert(removeEntity(context, a));
/// assert(compact(context));
/// assert(getComponent!int(context, 1) == 10);
/// ---
bool compact(ref Context self) @trusted {
	assert(!self.transaction, notInTransaction);
	immutable n = fp.dynarray.length(self.indexTable);
	immutable freedCount = fp.dynarray.length(self.freelist);
	if (freedCount == 0) return true;

	auto freed = cast(bool*) fp.pointer.allocator(null, n * bool.sizeof);
	if (freed is null) return false;
	scope(exit) cast(void) fp.pointer.allocator(freed, 0);
	foreach (e; 0 .. n) freed[e] = false;
	foreach (i; 0 .. freedCount) freed[self.freelist[i]] = true;

	auto order = cast(size_t*) fp.pointer.allocator(null, n * size_t.sizeof);
	if (order is null) return false;
	scope(exit) cast(void) fp.pointer.allocator(order, 0);
	size_t live = 0, dead = n - freedCount;
	foreach (e; 0 .. n)
		order[freed[e] ? dead++ : live++] = e;
	assert(order[0] == invalidEntity, "ecrs: a compaction that moves the invalid entity");
	assert(live == n - freedCount && dead == n, "ecrs: freed entities counted twice or missed; is an id on the freelist twice?");

	auto remap = ecrs.storage.buildRemap(order[0 .. n]);
	if (remap is null) return false;
	scope(exit) cast(void) fp.pointer.allocator(remap, 0);
	foreach (e; 0 .. n)
		if (freed[e]) remap[e] = invalidEntity;

	if (!renumber(self, order[0 .. n], remap[0 .. n])) return false;
	// The tail now holds the freed ids, whose index lists removeEntity released.
	cast(void) fp.dynarray.removeLast(self.indexTable, freedCount);
	fp.dynarray.clear(self.freelist);
	assert(validate(self), "ecrs: a compaction broke the store's invariants");
	assert(fp.dynarray.length(self.indexTable) == n - freedCount, "ecrs: a compaction kept freed entities");
	return true;
}


/// Sorts each of the listed components' storages into entity order.
/// It moves components, so it invalidates pointers into those storages.
///
/// Returns false if allocation fails for any of them; each storage it could not sort is left as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId a = addEntity(context), b = addEntity(context);
/// *addComponent!int(context, b) = 2;
/// *addComponent!int(context, a) = 1;
/// assert(sortByOwner!(int, short)(context));
/// assert(ecrs.storage.slotOwnersOf(*getStorage!int(context)) == [a, b]);
/// ---
template sortByOwner(Ts...) if (Ts.length != 1 || !is(typeof(Ts[0]) : size_t)) {
	bool sortByOwner(ref Context self) {
		assert(structureFree(self), structuralChange);
		assert(!self.transaction, notInTransaction);
		bool sorted = true;
		static foreach (T; Ts) {{
			auto storage = .getStorage!T(self);
			sorted &= storage !is null && ecrs.storage.sortByOwner!T(*storage, self.indexTable);
		}}
		assert(!sorted || validate(self), "ecrs: a sort broke the store's invariants");
		return sorted;
	}
}

/// Ditto, for component `(T, unique)`.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(sortByOwner!(int, 1)(context));
/// ---
template sortByOwner(T, size_t unique = 0) {
	bool sortByOwner(ref Context self) {
		assert(structureFree(self), structuralChange);
		assert(!self.transaction, notInTransaction);
		auto storage = .getStorage!(T, unique)(self);
		immutable sorted = storage !is null && ecrs.storage.sortByOwner!(T, unique)(*storage, self.indexTable);
		assert(!sorted || validate(self), "ecrs: a sort broke the store's invariants");
		return sorted;
	}
}

/// Ditto, for component `componentId`; one no entity ever had has nothing to sort.
/// `elementSize`, unless `Storage.unknownSize`, is checked against the storage's.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(sortByOwner(context, ecrs.registry.componentId!int()));
/// ---
bool sortByOwner(ref Context self, size_t componentId, size_t elementSize = ecrs.storage.Storage.unknownSize) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.transaction, notInTransaction);
	if (!hasStorage(self, componentId)) return true;
	assert(elementSize == ecrs.storage.Storage.unknownSize || elementSize == self.storages[componentId].elementSize, "ecrs: sorting a storage as the wrong element size");
	immutable sorted = ecrs.storage.sortByOwner(self.storages[componentId], componentId, self.indexTable);
	assert(!sorted || validate(self), "ecrs: a sort broke the store's invariants");
	return sorted;
}

/// Sorts every component storage into entity order, as `sortByOwner` does.
///
/// Returns false if allocation fails for any storage; each one it could not sort is left as it was.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// assert(sortAllByOwner(context));
/// ---
bool sortAllByOwner(ref Context self) @trusted {
	assert(structureFree(self), structuralChange);
	assert(!self.transaction, notInTransaction);
	bool sorted = true;
	foreach (id; 0 .. fp.dynarray.length(self.storages))
		if (self.storages[id].elementSize != ecrs.storage.Storage.unknownSize)
			sorted &= ecrs.storage.sortByOwner(self.storages[id], id, self.indexTable);
	assert(!sorted || validate(self), "ecrs: a sort broke the store's invariants");
	return sorted;
}


/// Whether `self`'s two views of who owns what agree, outside a transaction: every component slot's owner is a live entity whose index list names that slot, every slot an index list names is owned by its entity, and no freed id is listed twice or keeps an index list.
/// It reads the whole store, so it is for tests and audits.
///
/// Examples:
/// ---
/// Context context = create();
/// scope(exit) free(context);
/// EntityId e = addEntity(context);
/// assert(addComponent!int(context, e) !is null);
/// assert(validate(context));
/// ---
bool validate(const ref Context self) @trusted {
	assert(!self.transaction, notInTransaction);
	immutable entityLimit = fp.dynarray.length(self.indexTable);
	foreach (i; 0 .. fp.dynarray.length(self.freelist)) {
		immutable freed = self.freelist[i];
		if (freed == invalidEntity || freed >= entityLimit || self.indexTable[freed] !is null) return false;
		foreach (j; 0 .. i)
			if (self.freelist[j] == freed) return false;
	}
	size_t owned = 0, listed = 0;
	foreach (id; 0 .. fp.dynarray.length(self.storages)) {
		if (self.storages[id].elementSize == ecrs.storage.Storage.unknownSize) continue;
		foreach (slot, slotOwner; ecrs.storage.slotOwnersOf(self.storages[id])) {
			if (slotOwner == invalidEntity) continue;
			++owned;
			if (slotOwner >= entityLimit || fp.dynarray.length(self.indexTable[slotOwner]) <= id || self.indexTable[slotOwner][id] != slot) return false;
		}
	}
	foreach (e; 0 .. entityLimit)
		foreach (id; 0 .. fp.dynarray.length(self.indexTable[e]))
			listed += self.indexTable[e][id] != ecrs.storage.Storage.absent;
	return owned == listed;
}


version(unittest) {
	private struct Tracked {
		int value;
		__gshared int finalized;
		void finalize() @nogc nothrow {
			if (value != 0) ++finalized;
			value = 0;
		}
	}

	// Every kind of change a transaction journals; false at the first refused one.
	private bool transactionScript(ref Context context, EntityId kept, EntityId doomed) @trusted {
		static import ecrs.relation;
		alias Many = ecrs.relation.Relation!(ecrs.relation.dynamicArity);
		EntityId fresh = addEntity(context);
		if (fresh == invalidEntity || addComponent!Tracked(context, fresh) is null) return false;
		getForWriting!Tracked(context, fresh).value = 7;
		Many list;
		if (!fp.dynarray.pushBack(list.related, fresh)) return false;
		if (!setComponent!Many(context, kept, list)) return false;
		if (!setComponent!int(context, kept, 11) || !setComponent!int(context, kept, 12)) return false;
		if (!removeComponent!Tracked(context, kept) || addComponent!Tracked(context, kept) is null) return false;
		getForWriting!Tracked(context, kept).value = 9;
		if (!removeEntity(context, doomed)) return false;
		EntityId brief = addEntity(context);
		if (brief == invalidEntity || !setComponent!int(context, brief, 3) || !removeEntity(context, brief)) return false;
		// A component cleared in a transaction is journaled owner by owner, so a rollback brings each back.
		if (!setComponent!short(context, kept, 6)) return false;
		return clearComponent(context, componentId!short());
	}

	private ubyte* snapshot(ref Context context) {
		static import ecrs.serialization;
		auto bytes = ecrs.serialization.serialize(context);
		assert(bytes !is null);
		return bytes;
	}

	private alias componentId = ecrs.registry.componentId;
}

unittest {
	// Transactions: a rollback restores the store exactly, even after any refused allocation, and allocates nothing itself; a commit keeps the changes.
	static import ecrs.relation;
	alias Many = ecrs.relation.Relation!(ecrs.relation.dynamicArity);

	size_t refusals = 0;
	foreach (commit; [false, true])
		for (size_t budget = 0;; ++budget) {
			Tracked.finalized = 0;
			auto context = create();
			scope(exit) free(context);
			EntityId kept = addEntity(context), doomed = addEntity(context), freed = addEntity(context);
			// `freed`'s components leave holes, which the transaction's additions reuse and a rollback must give back in order.
			addComponent!Tracked(context, freed).value = 3;
			assert(setComponent!int(context, freed, 5));
			assert(setComponent!int(context, kept, 10) && setComponent!short(context, doomed, 4));
			Many list;
			assert(fp.dynarray.pushBack(list.related, doomed));
			assert(setComponent!Many(context, kept, list));
			addComponent!Tracked(context, kept).value = 1;
			addComponent!Tracked(context, doomed).value = 2;
			assert(removeEntity(context, freed));
			Tracked.finalized = 0;
			int* held = &getForWriting!int(context, kept);
			auto before = snapshot(context);
			scope(exit) fp.dynarray.free(before);

			assert(!inTransaction(context));
			beginTransaction(context);
			assert(inTransaction(context));
			ecrs.registry.failAllocationsAfter(budget);
			immutable done = transactionScript(context, kept, doomed);
			if (!done) ++refusals;
			if (!done || !commit) {
				// Nothing is left to allocate with: the rollback must manage without.
				ecrs.registry.failAllocationsAfter(0);
				rollbackTransaction(context);
				ecrs.registry.restoreAllocations();
				auto after = snapshot(context);
				scope(exit) fp.dynarray.free(after);
				assert(fp.dynarray.slice(after) == fp.dynarray.slice(before));
				if (done) assert(Tracked.finalized == 2); // fresh's and kept's new Tracked, once each
				assert(getComponent!Tracked(context, kept).value == 1 && getComponent!Tracked(context, doomed).value == 2);
				assert(&getComponent!int(context, kept) is held && *held == 10);
				assert(addEntity(context) == freed); // the freelist is back too
				if (done) break;
				continue;
			}
			ecrs.registry.restoreAllocations();
			assert(Tracked.finalized == 0);
			commitTransaction(context);
			assert(!inTransaction(context) && !hasComponent!short(context, kept));
			assert(Tracked.finalized == 2); // kept's old Tracked and doomed's
			assert(&getComponent!int(context, kept) is held && *held == 12);
			assert(getComponent!Tracked(context, kept).value == 9 && getComponent!Many(context, kept).related[0] == 4);
			assert(!hasComponent!short(context, doomed) && context.indexTable[doomed] is null);
			assert(entityCount(context) == 3 && fp.dynarray.length(context.indexTable) == 6);
			break;
		}
	assert(refusals >= 20); // every allocation in the script, refused in turn, once per mode

	// Freeing a context with a transaction open keeps its changes and ends every lifetime once.
	Tracked.finalized = 0;
	{
		auto context = create();
		scope(exit) free(context);
		EntityId e = addEntity(context);
		addComponent!Tracked(context, e).value = 1;
		beginTransaction(context);
		assert(removeComponent!Tracked(context, e));
		assert(Tracked.finalized == 0);
	}
	assert(Tracked.finalized == 1);
}

unittest {
	// Entities: creation, the reserved entity 0, freelist reuse and iteration.
	auto context = create();
	scope(exit) free(context);
	assert(entityCount(context) == 1);

	EntityId a = addEntity(context);
	EntityId b = addEntity(context);
	size_t count = 0;
	foreach (e; entities(context)) ++count;
	assert(count == 3);

	assert(removeEntity(context, a));
	count = 0;
	foreach (e; entities(context)) {
		assert(e != a);
		++count;
	}
	assert(count == 2 && entityCount(context) == 2);
	assert(addEntity(context) == a);

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

	auto context = create();
	scope(exit) free(context);

	EntityId e1 = addEntity(context);
	*addComponent!Vec2(context, e1) = Vec2(1, 2);
	EntityId e2 = addEntity(context);
	*addComponent!Vec2(context, e2) = Vec2(3, 4);
	EntityId e3 = addEntity(context);
	*addComponent!Vec2(context, e3) = Vec2(5, 6);
	assert(entityCount(context) == 4);
	assert(hasComponent!Vec2(context, e1));

	assert(removeEntity(context, e2));
	assert(entityCount(context) == 3);

	size_t seen = 0;
	float xsum = 0;
	foreach (e; entities(context))
		if (hasComponent!Vec2(context, e)) {
			xsum += getComponent!Vec2(context, e).x;
			++seen;
		}
	assert(seen == 2);
	assert(xsum == 1 + 5);

	assert(!hasComponent!Counter(context, e1));
	assert(findComponent!Counter(context, e1) is null);
	assert(findComponent!Counter(context, invalidEntity) is null);
	assert(findComponent!Vec2(context, e1) is &getComponent!Vec2(context, e1));
	const(Context)* view = &context;
	assert(findComponent!Vec2(*view, e3).x == 5);
	auto c = ensureComponent!Counter(context, e1);
	c.value = 5;
	assert(ensureComponent!Counter(context, e1) is c);
	assert(getComponent!Counter(context, e1).value == 5);
	assert(removeComponent!Counter(context, e1));
	assert(!hasComponent!Counter(context, e1));
	assert(findComponent!Counter(context, e1) is null);
}

unittest {
	// Components through the runtime-id forms.
	struct Flag { int v; }

	auto context = create();
	scope(exit) free(context);

	EntityId e = addEntity(context);
	immutable id = ecrs.registry.componentId!Flag();

	assert(!hasComponent(context, e, id));
	assert(findComponent(context, e, id) is null);
	auto p = ensureComponent(context, e, id);
	(cast(Flag*) p).v = 42;
	assert(hasComponent(context, e, id));
	assert(ensureComponent(context, e, id) is p);
	assert((cast(Flag*) getComponent(context, e, id)).v == 42);
	assert(findComponent(context, e, id, Flag.sizeof) is p);
	assert(findComponent(*cast(const(Context)*) &context, e, id) is p);

	assert(removeComponent(context, e, id));
	assert(!hasComponent(context, e, id));
	auto p3 = addComponent(context, e, id, Flag.sizeof);
	assert((cast(Flag*) p3).v == 0);

	const(Context)* constCtx = &context;
	assert(getStorage(*constCtx, id, Flag.sizeof) !is null);
	assert(getStorage(*constCtx, ecrs.registry.componentId!(Flag, 1)()) is null);

	// clearComponent empties one storage, past a hole, and leaves other components alone; generation advances.
	struct Other { int v; }
	immutable other = ecrs.registry.componentId!Other();
	assert(generation(context, other) == 0);
	assert(clearComponent(context, other)); // no storage yet: nothing to clear
	EntityId[4] marked;
	foreach (ref m; marked) {
		m = addEntity(context);
		assert(addComponent(context, m, id) !is null && addComponent!Other(context, m) !is null);
	}
	assert(removeComponent(context, marked[1], id));
	immutable g = generation(context, id), whole = generation(context);
	assert(clearComponent(context, id));
	assert(generation(context, id) > g && generation(context) > whole);
	assert(ecrs.storage.empty(*getStorage(*constCtx, id)));
	foreach (m; marked)
		assert(!hasComponent(context, m, id) && hasComponent!Other(context, m));

	// The whole context's generation moves with any one storage's, and holds still under const access.
	immutable settled = generation(context);
	cast(void) getComponent!Other(*constCtx, marked[0]);
	assert(generation(context) == settled);
	++getForWriting!Other(context, marked[0]).v;
	assert(generation(context) > settled);
}

unittest {
	// Every allocation failure leaves the context as it was.
	struct Payload { int value; }
	auto context = create();
	scope(exit) free(context);

	Context unreserved;
	ecrs.registry.failAllocationsAfter(0);
	assert(addEntity(unreserved) == invalidEntity);
	ecrs.registry.restoreAllocations();
	assert(entityCount(unreserved) == 0);

	EntityId e = addEntity(context);
	immutable id = ecrs.registry.componentId!Payload();
	foreach (n; 0 .. 16) {
		ecrs.registry.failAllocationsAfter(n);
		auto p = addComponent!Payload(context, e);
		ecrs.registry.restoreAllocations();
		if (p !is null) break;
		assert(!hasComponent(context, e, id));
	}
	assert(hasComponent(context, e, id));

	EntityId other = addEntity(context);
	ecrs.registry.failAllocationsAfter(0);
	assert(!removeEntity(context, e));
	assert(!swapEntities(context, e, other));
	ecrs.registry.restoreAllocations();
	assert(hasComponent(context, e, id) && entityCount(context) == 3);

	assert(removeEntity(context, other));
	ecrs.registry.failAllocationsAfter(0);
	assert(!compact(context));
	ecrs.registry.restoreAllocations();
	assert(fp.dynarray.length(context.freelist) == 1);
	assert(compact(context));
	assert(fp.dynarray.length(context.freelist) == 0);

	// The remap allocates first, so the second allocation failing reaches the permutation itself.
	assert(fp.dynarray.length(context.indexTable) == 2);
	immutable size_t[2] order = [0, 1];
	ecrs.registry.failAllocationsAfter(1);
	assert(!reorderEntities(context, order[]));
	ecrs.registry.restoreAllocations();
	assert(hasComponent(context, e, id));
}

unittest {
	// Const access, swapEntities, reorderEntities and sortByOwner.
	struct Val { int v; }

	auto context = create();
	scope(exit) free(context);

	EntityId e1 = addEntity(context);
	*addComponent!Val(context, e1) = Val(30);
	EntityId e2 = addEntity(context);
	*addComponent!Val(context, e2) = Val(10);
	EntityId e3 = addEntity(context);
	*addComponent!Val(context, e3) = Val(20);

	const(Context)* constCtx = &context;
	assert(getComponent!Val(*constCtx, e1).v == 30);

	assert(swapEntities(context, e1, e3));
	assert(getComponent!Val(context, e1).v == 20);
	assert(getComponent!Val(context, e3).v == 30);
	assert(swapEntities(context, e1, e3));

	// With one entity named, the other is the last slot.
	immutable lastId = cast(EntityId)(fp.dynarray.length(context.indexTable) - 1);
	assert(lastId == e3);
	assert(swapEntities(context, e1));
	assert(getComponent!Val(context, lastId).v == 30);
	assert(swapEntities(context, e1));

	immutable size_t[4] order = [0, 3, 2, 1];
	assert(reorderEntities(context, order[]));
	assert(getComponent!Val(context, 1).v == 20);
	assert(getComponent!Val(context, 2).v == 10);
	assert(getComponent!Val(context, 3).v == 30);

	// A 3-cycle pins down that `order[i]` is the entity ending up at i, not where i goes.
	immutable size_t[4] cycle = [0, 3, 1, 2];
	assert(reorderEntities(context, cycle[]));
	assert(getComponent!Val(context, 1).v == 30);
	assert(getComponent!Val(context, 2).v == 20);
	assert(getComponent!Val(context, 3).v == 10);

	assert(ecrs.storage.liveCount(*getStorage(*constCtx, ecrs.registry.componentId!Val(), Val.sizeof)) == 3);

	struct NeverAdded { int v; }
	assert(sortByOwner(context, ecrs.registry.componentId!NeverAdded()));
	assert(sortByOwner(context, ecrs.registry.componentId!Val()));
	assert(sortAllByOwner(context));
	auto storage = getStorage!Val(context);
	assert(ecrs.storage.slotOwnersOf(*storage) == [1, 2, 3]);
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
		auto context = create();
		scope(exit) free(context);

		EntityId e1 = addEntity(context);
		EntityId e2 = addEntity(context);
		EntityId e3 = addEntity(context);
		addComponent!Owned(context, e1).value = 1;
		addComponent!Owned(context, e2).value = 1;
		addComponent!Owned(context, e3).value = 1;

		assert(removeComponent!Owned(context, e1));
		assert(Owned.finalized == 1);
		assert(removeEntity(context, e2));
		assert(Owned.finalized == 2);
	}
	assert(Owned.finalized == 3);
}

unittest {
	// A renumbering reaches every holder without the caller naming any, past a freed entity in the table.
	static import ecrs.relation;
	alias Next = ecrs.relation.Relation!1;
	alias Many = ecrs.relation.Relation!(ecrs.relation.dynamicArity);
	alias Typed = ecrs.relation.Relation!(1, true);

	static struct Memo {
		EntityId cached;
		static void remap(void* self, const(EntityId)[] remap) @nogc nothrow {
			auto memo = cast(Memo*) self;
			memo.cached = remap[memo.cached];
		}
	}

	auto context = create();
	scope(exit) free(context);

	EntityId e1 = addEntity(context);
	EntityId e2 = addEntity(context);
	EntityId e3 = addEntity(context);
	EntityId gone = addEntity(context);
	assert(removeEntity(context, gone));

	addComponent!Next(context, e1).related[0] = e2;
	addComponent!Next(context, e2).related[0] = e3;
	addComponent!Next(context, e3).related[0] = invalidEntity;
	assert(fp.dynarray.pushBack(addComponent!Many(context, e1).related, e3));
	addComponent!Typed(context, e2).related[0] = ecrs.relation.Term(e1);

	Memo memo = Memo(e3);
	assert(addRemapHook(context, &Memo.remap, &memo));

	// 1 -> 3, 2 -> 1, 3 -> 2; the freed 4 stays where it is.
	immutable size_t[5] order = [0, 2, 3, 1, 4];
	assert(reorderEntities(context, order[]));

	assert(getComponent!Next(context, 3).related[0] == 1);
	assert(getComponent!Next(context, 1).related[0] == 2);
	assert(getComponent!Next(context, 2).related[0] == invalidEntity);
	assert(getComponent!Many(context, 3).related[0] == 2);
	assert(getComponent!Typed(context, 1).related[0].constant == 3);
	assert(ecrs.storage.owner(*getStorage!Next(context), context.indexTable[3][ecrs.registry.componentId!Next()]) == 3);
	assert(memo.cached == 2);
	assert(context.freelist[0] == 4);

	assert(removeRemapHook(context, &Memo.remap, &memo));
	assert(!removeRemapHook(context, &Memo.remap, &memo));
	assert(swapEntities(context, 1, 2));
	assert(memo.cached == 2);
	assert(getComponent!Next(context, 3).related[0] == 2);
}

unittest {
	// compact renumbers live entities densely in order, shrinks the table, empties the freelist and invalidates references to freed entities.
	static import ecrs.relation;
	alias Next = ecrs.relation.Relation!1;
	struct Val { int v; }

	auto context = create();
	scope(exit) free(context);

	foreach (i; 1 .. 6) {
		EntityId e = addEntity(context);
		*addComponent!Val(context, e) = Val(i * 10);
	}
	addComponent!Next(context, 5).related[0] = 3;
	addComponent!Next(context, 1).related[0] = 4;
	assert(removeEntity(context, 2));
	assert(removeEntity(context, 4));

	assert(compact(context));
	assert(fp.dynarray.length(context.indexTable) == 4);
	assert(fp.dynarray.length(context.freelist) == 0);
	assert(entityCount(context) == 4);
	assert(getComponent!Val(context, 1).v == 10);
	assert(getComponent!Val(context, 2).v == 30);
	assert(getComponent!Val(context, 3).v == 50);
	assert(getComponent!Next(context, 3).related[0] == 2);
	assert(getComponent!Next(context, 1).related[0] == invalidEntity);
	assert(addEntity(context) == 4);

	assert(compact(context)); // nothing freed: a no-op
	assert(fp.dynarray.length(context.indexTable) == 5);
}

unittest {
	// A component's address survives more of its type, new component types relocating the storage table, and other removals.
	struct Payload { int value; }
	struct LateA { int x; }
	struct LateB { long y; }

	auto context = create();
	scope(exit) free(context);

	EntityId first = addEntity(context);
	Payload* held = addComponent!Payload(context, first);
	held.value = 7;

	foreach (i; 0 .. 3000) {
		EntityId e = addEntity(context);
		addComponent!Payload(context, e).value = i;
		if (i == 1000) assert(addComponent!LateA(context, e) !is null);
		if (i == 2000) assert(addComponent!LateB(context, e) !is null);
		if (i % 3 == 0) removeComponent!Payload(context, e);
	}
	assert(&getComponent!Payload(context, first) is held);
	assert(held.value == 7);
}

unittest {
	// Concurrent writes: threads change components of their own entities inside a transaction, which a rollback undoes exactly and a commit keeps.
	static import bc.threadpool;
	static struct Job { Context* context; EntityId first; size_t count; bool ok; }
	static void write(void* arg) @nogc nothrow {
		auto job = cast(Job*) arg;
		job.ok = true;
		foreach (i; 0 .. job.count) {
			immutable e = cast(EntityId) (job.first + i);
			job.ok &= setComponent!int(*job.context, e, cast(int) e) && setComponent!short(*job.context, e, 7) && setComponent!int(*job.context, e, cast(int) e * 2);
			if (e % 3 == 0) job.ok &= removeComponent!short(*job.context, e);
		}
	}
	auto pool = bc.threadpool.create(4);
	assert(pool !is null);
	scope(exit) bc.threadpool.free(pool);
	foreach (commit; [false, true]) {
		auto context = create();
		scope(exit) free(context);
		EntityId kept = addEntity(context);
		assert(setComponent!int(context, kept, 1));
		auto before = snapshot(context);
		scope(exit) fp.dynarray.free(before);
		beginTransaction(context);
		immutable first = addEntities(context, 400);
		assert(first != invalidEntity);
		Job[8] jobs;
		bc.threadpool.Job[8] work;
		foreach (i, ref job; jobs) {
			job = Job(&context, cast(EntityId) (first + i * 50), 50);
			work[i] = bc.threadpool.Job(&write, &job);
		}
		// A reservation given back, as a step failing before the phase opens would, leaves the storages as they were.
		immutable slots = ecrs.storage.slotCount(*getStorage!int(context));
		assert(reserveConcurrentAdds!int(context, 400));
		cancelConcurrentAdds(context);
		assert(ecrs.storage.slotCount(*getStorage!int(context)) == slots && !getStorage!int(context).claimLimit);
		assert(reserveConcurrentAdds!int(context, 400) && reserveConcurrentAdds!short(context, 400));
		beginConcurrentWrites(context);
		assert(bc.threadpool.run(pool, work[]));
		endConcurrentWrites(context);
		foreach (ref job; jobs) assert(job.ok);
		if (!commit) {
			rollbackTransaction(context);
			auto after = snapshot(context);
			scope(exit) fp.dynarray.free(after);
			assert(fp.dynarray.slice(after) == fp.dynarray.slice(before));
			continue;
		}
		commitTransaction(context);
		foreach (i; 0 .. 400) {
			immutable e = cast(EntityId) (first + i);
			assert(getComponent!int(context, e) == e * 2 && hasComponent!short(context, e) == (e % 3 != 0));
		}

		// A storage only written in place, never prepared, still counts the phase as a change; one only read does not.
		immutable written = generation(context, ecrs.registry.componentId!int()), read = generation(context, ecrs.registry.componentId!short());
		beginConcurrentWrites(context);
		getForWriting!int(context, first) = 9;
		cast(void) getComponent!short(cast(const) context, first % 3 ? first : cast(EntityId) (first + 1));
		endConcurrentWrites(context);
		assert(generation(context, ecrs.registry.componentId!int()) > written && generation(context, ecrs.registry.componentId!short()) == read);

		// Slots prepared and never claimed are given back when the phase ends.
		assert(reserveConcurrentAdds!long(context, 5));
		beginConcurrentWrites(context);
		endConcurrentWrites(context);
		assert(ecrs.storage.slotCount(context.storages[ecrs.registry.componentId!long()]) == 0);
	}
}

unittest { // reads count no change; writes through getForWriting, findForWriting, ensureComponent and setComponent each do
	Context context = create();
	scope(exit) free(context);
	immutable e = addEntity(context);
	*addComponent!int(context, e) = 1;
	immutable id = ecrs.registry.componentId!int();
	auto g = generation(context, id);
	assert(getComponent!int(context, e) == 1 && *findComponent!int(context, e) == 1 && findComponent!short(context, e) is null);
	assert(generation(context, id) == g);
	static assert(!__traits(compiles, getComponent!int(context, e) = 2));
	getForWriting!int(context, e) = 2;
	assert(generation(context, id) > g);
	g = generation(context, id);
	*findForWriting!int(context, e) = 3;
	assert(generation(context, id) > g);
	g = generation(context, id);
	*ensureComponent!int(context, e) = 4;
	assert(generation(context, id) > g);
	g = generation(context, id);
	assert(setComponent!int(context, e, 5) && generation(context, id) > g && getComponent!int(context, e) == 5);

	// The write observer hears each write and its component before it happens, and no read.
	static struct Heard { size_t writes; EntityId entity; size_t component; }
	static void hear(void* data, EntityId entity, size_t component) @nogc nothrow { auto h = cast(Heard*) data; ++h.writes; h.entity = entity; h.component = component; }
	Heard heard;
	context.writeObserver = &hear;
	context.writeObserverData = &heard;
	assert(getComponent!int(context, e) == 5 && findComponent!short(context, e) is null && findForWriting!short(context, e) is null && heard.writes == 0);
	getForWriting!int(context, e) = 6;
	assert(heard.writes == 1 && heard.entity == e && heard.component == id);
	*findForWriting!int(context, e) = 7;
	*ensureComponent!int(context, e) = 8;
	assert(setComponent!int(context, e, 9) && heard.writes == 4);
	assert(setComponent!short(context, e, 1) && heard.writes == 5 && heard.component == ecrs.registry.componentId!short());
	assert(*ensureComponent!byte(context, e) == 0 && heard.writes == 6);
	assert(removeComponent!short(context, e) && removeComponent!byte(context, e) && heard.writes == 8);
	context.writeObserver = null;
	assert(setComponent!int(context, e, 5) && heard.writes == 8);

	// A singleton likewise: found for reading it counts nothing, found for writing it counts the write.
	assert(findSingletonForWriting!long(context) is null && addSingleton!long(context) !is null);
	immutable singleton = ecrs.registry.componentId!long();
	g = generation(context, singleton);
	assert(*findSingleton!long(context) == 0 && generation(context, singleton) == g);
	context.writeObserver = &hear;
	*findSingletonForWriting!long(context) = 6;
	context.writeObserver = null;
	assert(heard.writes == 9 && heard.component == singleton);
	assert(generation(context, singleton) > g && *findSingleton!long(context) == 6);
	// Once its entity loses it, the storage stays but holds no singleton.
	auto storage = getStorage(context, singleton);
	EntityId holder = invalidEntity;
	foreach (slot; 0 .. ecrs.storage.slotCount(*storage))
		if (ecrs.storage.owner(*storage, slot) != invalidEntity) holder = ecrs.storage.owner(*storage, slot);
	assert(holder != invalidEntity && removeComponent!long(context, holder));
	assert(getStorage(context, singleton) !is null && findSingleton!long(context) is null && findSingletonForWriting!long(context) is null);
}
