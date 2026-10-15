/// Systems, and combinators that run them over a `Context`, one after another or concurrently on a `bc.threadpool`.
///
/// A per-entity system is a function `bool fn(ref Context, EntityId)`; a whole system is anything callable as `bool system(ref Context)`. Either reports failure by returning false.
module ecrs.system;

static import bc.threadpool;
static import ecrs.context;
static import ecrs.registry;
static import fp.dynarray;

@nogc nothrow:


/// The shape a whole system takes as a plain function pointer. The combinators accept any callable system, as `isSystem` describes, not just this.
alias SystemFunction = bool function(ref ecrs.context.Context) @nogc nothrow;

// Whether `S` can be invoked as a whole system: `bool s(ref Context)`.
private enum isSystem(S) = __traits(compiles, (ref S system, ref ecrs.context.Context context) {
	bool result = system(context);
});

private template allSystems(Systems...) {
	static if (Systems.length == 0)
		enum allSystems = true;
	else
		enum allSystems = isSystem!(Systems[0]) && allSystems!(Systems[1 .. $]);
}

// Whether `T` owns the context a system should run against as a `ctx` member, so a bound schedule can take it directly.
private enum isContextLike(T) = !is(immutable T == immutable ecrs.context.Context)
	&& __traits(hasMember, T, "ctx")
	&& is(typeof(T.ctx) == ecrs.context.Context);


/// Runs `fn` over every live entity in order, stopping at the first that fails. Returns whether every visited entity succeeded.
///
/// Examples:
/// ---
/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// assert(sequential!visit(ctx));
/// ---
template sequential(alias fn) {
	bool sequential(ref ecrs.context.Context context) {
		foreach (e; ecrs.context.entities(context))
			if (!fn(context, e))
				return false;
		return true;
	}
}

// The pool whose job this thread runs, if any; a job may not wait on its own pool, so passes nested in one run inline.
private bc.threadpool.ThreadPool* runningPool = null;

private bool canDispatch(bc.threadpool.ThreadPool* pool) {
	return bc.threadpool.workerCount(pool) > 1 && runningPool !is pool;
}


/// Runs `fn` over every live entity concurrently on `pool`, one job per entity, and returns whether every one succeeded. Unlike `sequential!fn` it never stops early, so running inline visits exactly the entities the pool would; it runs inline on a single-worker pool, inside one of `pool`'s own jobs, which may not wait on it, and when allocating or submitting the jobs fails.
///
/// `parallel!fn(pool)` binds the pool, returning a whole system: a copyable struct callable as `bool opCall(ref Context)`, or with any type owning its context as a `ctx` member.
///
/// Examples:
/// ---
/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// assert(parallel!visit(ctx, pool));
/// assert(parallel!visit(pool)(ctx));
/// ---
template parallel(alias fn) {
	private struct Item {
		ecrs.context.Context* context;
		bc.threadpool.ThreadPool* pool;
		ecrs.registry.EntityId entity;
		bool result = true;
	}

	private void runItem(void* arg) {
		auto item = cast(Item*) arg;
		auto outer = runningPool;
		runningPool = item.pool;
		scope(exit) runningPool = outer;
		item.result = fn(*item.context, item.entity);
	}

	private bool andAllEntities(ref ecrs.context.Context context) {
		bool valid = true;
		foreach (e; ecrs.context.entities(context))
			valid &= fn(context, e);
		return valid;
	}

	private bool dispatch(ref ecrs.context.Context context, bc.threadpool.ThreadPool* pool) @trusted {
		// Marked even when it runs inline, so a structural change fails the same way whatever the pool size.
		ecrs.context.enterParallel(context);
		scope(exit) ecrs.context.exitParallel(context);
		if (!canDispatch(pool))
			return andAllEntities(context);

		immutable n = ecrs.context.entityCount(context);
		if (n == 0) return true;
		Item* items = fp.dynarray.create!Item(n);
		scope(exit) fp.dynarray.free(items);
		bc.threadpool.Job* jobs = fp.dynarray.create!(bc.threadpool.Job)(n);
		scope(exit) fp.dynarray.free(jobs);
		if (items is null || jobs is null)
			return andAllEntities(context);

		size_t i = 0;
		foreach (e; ecrs.context.entities(context)) {
			items[i] = Item(&context, pool, e);
			jobs[i] = bc.threadpool.Job(&runItem, &items[i]);
			++i;
		}
		if (!bc.threadpool.run(pool, jobs[0 .. n]))
			return andAllEntities(context);

		bool valid = true;
		foreach (j; 0 .. n) valid &= items[j].result;
		return valid;
	}

	bool parallel(ref ecrs.context.Context context, bc.threadpool.ThreadPool* pool) {
		return dispatch(context, pool);
	}

	/// `parallel!fn` with its pool bound, from `parallel!fn(pool)`.
	struct Bound {
		private bc.threadpool.ThreadPool* pool;

		@nogc nothrow:
		/// Runs the pass over `context`.
		///
		/// Examples:
		/// ---
		/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
		/// auto ctx = ecrs.context.create();
		/// scope(exit) ecrs.context.free(ctx);
		/// auto pool = bc.threadpool.create(2);
		/// scope(exit) bc.threadpool.free(pool);
		/// auto pass = parallel!visit(pool);
		/// assert(pass(ctx));
		/// ---
		bool opCall(ref ecrs.context.Context context) { return dispatch(context, pool); }

		/// Ditto, over the context a type owns as a `ctx` member.
		bool opCall(ContextLike)(ref ContextLike contextLike) if (isContextLike!ContextLike) {
			return dispatch(contextLike.ctx, pool);
		}
	}

	Bound parallel(bc.threadpool.ThreadPool* pool) {
		return Bound(pool);
	}
}


/// Runs whole systems in order, stopping at the first that fails, and returns whether all of them succeeded. Unlike the whole-system `parallel`, which has no first failure to stop at, it suits systems that work on what earlier ones produce.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// static bool fails(ref ecrs.context.Context) @nogc nothrow { return false; }
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// assert(sequential(ctx, &succeeds, &succeeds));
/// assert(!sequential(ctx, &fails, &succeeds));
/// ---
bool sequential(Systems...)(ref ecrs.context.Context context, Systems systems) {
	static foreach (system; systems)
		if (!system(context))
			return false;
	return true;
}

// Runs every system in order and ANDs the results: what `parallel` does when it cannot run anything concurrently.
private bool andAll(Systems...)(ref ecrs.context.Context context, Systems systems) {
	bool valid = true;
	static foreach (system; systems)
		valid &= system(context);
	return valid;
}

/// `sequential(Systems...)` with its systems bound, from `sequential(systems)`: a copyable struct that is itself a system, so it can be stored, nested in another combinator, or called on any type owning its context as a `ctx` member.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// Sequential!(typeof(&succeeds)) schedule = sequential(&succeeds);
/// auto copy = schedule;
/// ---
struct Sequential(Systems...) {
	private Systems systems;

	@nogc nothrow:
	/// Runs the systems over `context`.
	///
	/// Examples:
	/// ---
	/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
	/// auto ctx = ecrs.context.create();
	/// scope(exit) ecrs.context.free(ctx);
	/// assert(sequential(&succeeds)(ctx));
	/// ---
	bool opCall(ref ecrs.context.Context context) { return .sequential(context, systems); }

	/// Ditto, over the context a type owns as a `ctx` member.
	bool opCall(ContextLike)(ref ContextLike contextLike) if (isContextLike!ContextLike) {
		return .sequential(contextLike.ctx, systems);
	}
}

/// Ditto
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// auto schedule = sequential(&succeeds, &succeeds);
/// assert(schedule(ctx));
/// ---
Sequential!Systems sequential(Systems...)(Systems systems) if (Systems.length > 0 && allSystems!Systems) {
	return Sequential!Systems(systems);
}


// One system queued onto the pool, its callable type-erased so a schedule can mix function pointers with the combinators' structs.
private struct SystemJob {
	void* system;
	bool function(void*, ref ecrs.context.Context) @nogc nothrow invoke;
	ecrs.context.Context* context;
	bc.threadpool.ThreadPool* pool;
	bool result;
}

private bool invokeSystem(System)(void* system, ref ecrs.context.Context context) {
	return (*cast(System*) system)(context);
}

private void runSystem(void* arg) {
	auto job = cast(SystemJob*) arg;
	auto outer = runningPool;
	runningPool = job.pool;
	scope(exit) runningPool = outer;
	job.result = job.invoke(job.system, *job.context);
}

/// Runs whole systems concurrently on `pool`, queuing all of them at once, and returns whether every one succeeded. Every system runs, however many fail; with fewer than two systems, a single-worker pool, a call from inside one of `pool`'s own jobs, or a pool that cannot take the jobs, they run inline, in the order given.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// assert(parallel(ctx, pool, &succeeds, &succeeds));
/// ---
bool parallel(Systems...)(ref ecrs.context.Context context, bc.threadpool.ThreadPool* pool, Systems systems) @trusted {
	ecrs.context.enterParallel(context);
	scope(exit) ecrs.context.exitParallel(context);
	static if (Systems.length <= 1)
		return andAll(context, systems);
	else {
		if (!canDispatch(pool))
			return andAll(context, systems);

		SystemJob[Systems.length] systemJobs;
		bc.threadpool.Job[Systems.length] jobs;
		static foreach (i, System; Systems) {
			systemJobs[i] = SystemJob(&systems[i], &invokeSystem!System, &context, pool);
			jobs[i] = bc.threadpool.Job(&runSystem, &systemJobs[i]);
		}
		// `run` blocks until every job finishes, so `systems` outlives them.
		if (!bc.threadpool.run(pool, jobs[]))
			return andAll(context, systems);

		bool valid = true;
		foreach (i; 0 .. Systems.length)
			valid &= systemJobs[i].result;
		return valid;
	}
}

/// `parallel(Systems...)` with its pool and systems bound, from `parallel(pool, systems)`: a copyable struct that is itself a system, as `Sequential` is.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// Parallel!(typeof(&succeeds)) schedule = parallel(pool, &succeeds);
/// auto copy = schedule;
/// ---
struct Parallel(Systems...) {
	private bc.threadpool.ThreadPool* pool;
	private Systems systems;

	@nogc nothrow:
	/// Runs the systems over `context`.
	///
	/// Examples:
	/// ---
	/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
	/// auto ctx = ecrs.context.create();
	/// scope(exit) ecrs.context.free(ctx);
	/// auto pool = bc.threadpool.create(2);
	/// scope(exit) bc.threadpool.free(pool);
	/// assert(parallel(pool, &succeeds, &succeeds)(ctx));
	/// ---
	bool opCall(ref ecrs.context.Context context) { return .parallel(context, pool, systems); }

	/// Ditto, over the context a type owns as a `ctx` member.
	bool opCall(ContextLike)(ref ContextLike contextLike) if (isContextLike!ContextLike) {
		return .parallel(contextLike.ctx, pool, systems);
	}
}

/// Ditto
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto ctx = ecrs.context.create();
/// scope(exit) ecrs.context.free(ctx);
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// auto schedule = parallel(pool, &succeeds, &succeeds);
/// assert(schedule(ctx));
/// ---
Parallel!Systems parallel(Systems...)(bc.threadpool.ThreadPool* pool, Systems systems) if (Systems.length > 0 && allSystems!Systems) {
	return Parallel!Systems(pool, systems);
}


version(unittest) {
	private struct Counter(int tag) { int value; }

	// Increments the entity's `C`, if it has one.
	private bool bump(C = Counter!0)(ref ecrs.context.Context context, ecrs.registry.EntityId e) {
		if (ecrs.context.hasComponent!C(context, e))
			++ecrs.context.getComponent!C(context, e).value;
		return true;
	}

	// A context with entities 1 .. count + 1, entity i holding a `C` of value i - 1.
	private ecrs.context.Context countedContext(C = Counter!0)(size_t count) {
		auto context = ecrs.context.create();
		foreach (i; 0 .. count) {
			immutable e = ecrs.context.addEntity(context);
			assert(e != ecrs.registry.invalidEntity);
			ecrs.context.addComponent!C(context, e).value = cast(int) i;
		}
		return context;
	}

	private int valueOf(C = Counter!0)(ref ecrs.context.Context context, size_t e) {
		return ecrs.context.getComponent!C(context, cast(ecrs.registry.EntityId) e).value;
	}

	private bc.threadpool.ThreadPool* makePool(size_t workers) {
		auto pool = bc.threadpool.create(workers);
		assert(pool !is null);
		return pool;
	}
}

unittest {
	// Per-entity combinators, sequential and on pools of one and several workers, bound or not.
	auto ctx = countedContext(50);
	scope(exit) ecrs.context.free(ctx);

	assert(sequential!bump(ctx));
	foreach (i; 0 .. 50) assert(valueOf(ctx, i + 1) == i + 1);

	// sequential!fn stops at the first entity that fails.
	static size_t visited;
	static bool failsAtTwo(ref ecrs.context.Context, ecrs.registry.EntityId e) @nogc nothrow {
		++visited;
		return e != 2;
	}
	visited = 0;
	assert(!sequential!failsAtTwo(ctx));
	assert(visited == 3);

	foreach (workers; [1, 4]) {
		auto pool = makePool(workers);
		scope(exit) bc.threadpool.free(pool);
		immutable before = valueOf(ctx, 1);
		assert(parallel!bump(ctx, pool));
		assert(parallel!bump(pool)(ctx));
		foreach (i; 0 .. 50) assert(valueOf(ctx, i + 1) == i + before + 2);
	}

	// Bound per-entity passes compose sequentially, each finishing before the next starts.
	auto pool = makePool(4);
	scope(exit) bc.threadpool.free(pool);
	immutable before = valueOf(ctx, 1);
	auto runBump = parallel!bump(pool);
	assert(sequential(ctx, runBump, parallel!bump(pool)));
	assert(valueOf(ctx, 1) == before + 2);

	// Failing to allocate the jobs runs the pass inline instead.
	ecrs.registry.failAllocationsAfter(0);
	immutable passed = parallel!bump(ctx, pool);
	ecrs.registry.restoreAllocations();
	assert(passed && valueOf(ctx, 1) == before + 3);

	// A fresh pool's job stack must grow, so failing that allocation makes the pool refuse the jobs, and the pass runs inline.
	auto fresh = makePool(4);
	scope(exit) bc.threadpool.free(fresh);
	ecrs.registry.failAllocationsAfter(2);
	immutable refused = parallel!bump(ctx, fresh);
	ecrs.registry.restoreAllocations();
	assert(refused && valueOf(ctx, 1) == before + 4);
}

unittest {
	// Whole-system combinators: concurrent systems touching disjoint components, and in-order fallbacks.
	alias A = Counter!1, B = Counter!2, C = Counter!3;
	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);
	immutable e = ecrs.context.addEntity(ctx);
	ecrs.context.addComponent!A(ctx, e).value = 1;
	ecrs.context.addComponent!B(ctx, e).value = 10;
	ecrs.context.addComponent!C(ctx, e).value = 100;

	auto pool = makePool(4);
	scope(exit) bc.threadpool.free(pool);
	assert(parallel(ctx, pool, &sequential!(bump!A), &sequential!(bump!B), &sequential!(bump!C)));
	assert(valueOf!A(ctx, e) == 2 && valueOf!B(ctx, e) == 11 && valueOf!C(ctx, e) == 101);

	// With one worker the systems run in the order given, so a later one sees what an earlier one wrote.
	static bool copyAToB(ref ecrs.context.Context ctx, ecrs.registry.EntityId e) @nogc nothrow {
		if (ecrs.context.hasComponent!A(ctx, e) && ecrs.context.hasComponent!B(ctx, e))
			if (ecrs.context.hasComponent!A(ctx, e) && ecrs.context.hasComponent!B(ctx, e))
			ecrs.context.getComponent!B(ctx, e).value = ecrs.context.getComponent!A(ctx, e).value;
		return true;
	}
	auto serial = makePool(1);
	scope(exit) bc.threadpool.free(serial);
	assert(parallel(ctx, serial, &sequential!(bump!A), &sequential!copyAToB));
	assert(valueOf!A(ctx, e) == 3 && valueOf!B(ctx, e) == 3);

	// Fewer than two systems skip the pool; none is vacuously true, and one failure still reports through.
	static bool fails(ref ecrs.context.Context) @nogc nothrow { return false; }
	assert(parallel(ctx, pool));
	assert(parallel(ctx, pool, &sequential!(bump!A)));
	assert(valueOf!A(ctx, e) == 4);
	assert(!parallel(ctx, pool, &fails));

	// A pool that cannot take the jobs runs the systems inline.
	auto fresh = makePool(4);
	scope(exit) bc.threadpool.free(fresh);
	ecrs.registry.failAllocationsAfter(0);
	immutable refused = parallel(ctx, fresh, &sequential!(bump!A), &sequential!(bump!A));
	ecrs.registry.restoreAllocations();
	assert(refused && valueOf!A(ctx, e) == 6);
}

unittest {
	// sequential stops at the first failure, bound or not; parallel never does, whatever the pool.
	import core.atomic : atomicLoad, atomicOp, atomicStore;

	// Shared, since worker threads would bump their own thread-local copies of a static.
	static shared int runs;
	static bool fails(ref ecrs.context.Context) @nogc nothrow { runs.atomicOp!"+="(1); return false; }
	static bool succeeds(ref ecrs.context.Context) @nogc nothrow { runs.atomicOp!"+="(1); return true; }

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	runs.atomicStore(0);
	assert(!sequential(ctx, &fails, &succeeds));
	assert(runs.atomicLoad() == 1);

	runs.atomicStore(0);
	assert(!sequential(&fails, &succeeds)(ctx));
	assert(runs.atomicLoad() == 1);

	foreach (workers; [1, 4]) {
		auto pool = makePool(workers);
		scope(exit) bc.threadpool.free(pool);
		runs.atomicStore(0);
		assert(!parallel(ctx, pool, &fails, &succeeds));
		assert(runs.atomicLoad() == 2);
		runs.atomicStore(0);
		assert(!parallel(ctx, pool, &fails));
		assert(runs.atomicLoad() == 1);
	}
}

unittest {
	// Bound whole-system schedules are copyable systems that nest, mix function pointers with structs, and take a context owner.
	alias A = Counter!1, B = Counter!2;
	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);
	immutable e = ecrs.context.addEntity(ctx);
	ecrs.context.addComponent!A(ctx, e).value = 0;
	ecrs.context.addComponent!B(ctx, e).value = 0;

	auto twice = sequential(&sequential!(bump!A), &sequential!(bump!A));
	assert(twice(ctx));
	auto copy = twice;
	assert(copy(ctx));
	assert(sequential(twice, copy)(ctx));
	assert(valueOf!A(ctx, e) == 8);

	auto pool = makePool(4);
	scope(exit) bc.threadpool.free(pool);
	auto schedule = parallel(pool, &sequential!(bump!A), sequential(&sequential!(bump!B)));
	assert(schedule(ctx));
	auto scheduleCopy = schedule;
	assert(sequential(schedule, scheduleCopy)(ctx));
	assert(valueOf!A(ctx, e) == 11 && valueOf!B(ctx, e) == 3);

	assert(parallel(pool, parallel!(bump!A)(pool), parallel!(bump!B)(pool))(ctx));
	assert(valueOf!A(ctx, e) == 12 && valueOf!B(ctx, e) == 4);

	static struct Wrapper {
		ecrs.context.Context ctx;
		int payload;
	}
	auto wrapper = Wrapper(ctx, 7);
	assert(twice(wrapper));
	assert(schedule(wrapper));
	assert(parallel!(bump!A)(pool)(wrapper));
	assert(valueOf!A(ctx, e) == 16);
}

unittest {
	// Both parallel combinators mark the context while they run, even inline, so structural changes inside fail an assert.
	import core.atomic : atomicOp, atomicStore;
	static shared int sawParallel;

	static bool observe(ref ecrs.context.Context ctx, ecrs.registry.EntityId) @nogc nothrow {
		if (ecrs.context.inParallel(ctx)) sawParallel.atomicOp!"+="(1);
		return true;
	}
	static bool observeWhole(ref ecrs.context.Context ctx) @nogc nothrow {
		if (ecrs.context.inParallel(ctx)) sawParallel.atomicOp!"+="(1);
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);
	foreach (i; 0 .. 4) assert(ecrs.context.addEntity(ctx) != ecrs.registry.invalidEntity);

	foreach (workers; [1, 4]) {
		auto pool = makePool(workers);
		scope(exit) bc.threadpool.free(pool);

		sawParallel.atomicStore(0);
		assert(parallel!observe(ctx, pool));
		assert(sawParallel == ecrs.context.entityCount(ctx));
		assert(!ecrs.context.inParallel(ctx));

		sawParallel.atomicStore(0);
		assert(parallel(ctx, pool, &observeWhole));
		assert(parallel(ctx, pool, &observeWhole, &observeWhole));
		assert(sawParallel == 3);
		assert(!ecrs.context.inParallel(ctx));
	}

	assert(sequential!observe(ctx));
	assert(!ecrs.context.inParallel(ctx));
}
