module ecrs.system;

import ecrs.context;
import ecrs.storage : EntityId;
import bc.threadpool;

import fp.dynarray;

import std.algorithm.searching : all;

@nogc nothrow:


// ============================================================================
// Per-entity combinators
// ============================================================================

/// Runs `fn` over every entity in order, stopping at the first one that fails.
template sequential(alias fn) {
	bool sequential(ref Context context) {
		foreach (e; context.entities())
			if(!fn(context, cast(EntityId) e))
				return false;
		return true;
	}
}

template parallel(alias fn) {
	private struct Item {
		Context* context;
		EntityId entity;
		bool result = true;
	}

	private void runItem(void* arg) @nogc nothrow {
		auto item = cast(Item*) arg;
		item.result = fn(*item.context, item.entity);
	}

	/// Every entity, in order, ANDed - `sequential!fn` without the short
	/// circuit, so a single-worker pool visits exactly the entities a
	/// multi-worker one would. See `ecrs.system.andAll`.
	private bool andAllEntities(ref Context context) @nogc nothrow {
		bool valid = true;
		foreach (e; context.entities())
			valid &= fn(context, cast(EntityId) e);
		return valid;
	}

	private bool dispatch(ref Context context, ThreadPool* pool) @trusted @nogc nothrow {
		if (pool.workerCount() <= 1)
			return andAllEntities(context);

		EntityId* liveEntities = null; fp.dynarray.reserve(liveEntities, context.entityCount());
		scope(exit) fp.dynarray.free(liveEntities);
		foreach (e; context.entities())
			fp.dynarray.pushBack(liveEntities, cast(EntityId) e);

		immutable n = fp.dynarray.length(liveEntities);
		if (n == 0) return true;

		Item* items = fp.dynarray.create!Item(n);
		scope(exit) fp.dynarray.free(items);
		Job* jobs = fp.dynarray.create!Job(n);
		scope(exit) fp.dynarray.free(jobs);

		foreach (i; 0 .. n) {
			items[i] = Item(&context, liveEntities[i]);
			jobs[i] = Job(&runItem, &items[i]);
		}

		pool.run(jobs[0 .. n]);
		return fp.dynarray.slice(items).all!(item => item.result);
	}

	bool parallel(ref Context context, ThreadPool* pool) @trusted @nogc nothrow {
		return dispatch(context, pool);
	}

	/// Binds `pool` up front, returning a savable, copyable callable
	/// (`bool opCall(ref Context) @nogc nothrow`) so `parallel!fn(pool)` can
	/// be used as a whole system - e.g. passed to `sequential(Systems...)`
	/// or the whole-system `parallel(Systems...)` combinator, both of which
	/// only invoke each system with `(ref Context)` - or simply called as
	/// `parallel!fn(pool)(context)`. A plain struct is used instead of a
	/// closure since capturing `pool` in a delegate would need GC
	/// allocation, which isn't available under `-betterC`.
	struct Bound {
		private ThreadPool* pool;
		this(ThreadPool* pool) @nogc nothrow { this.pool = pool; }
		bool opCall(ref Context context) @nogc nothrow { return dispatch(context, pool); }

		/// Ditto, for a type that owns its context as a `ctx` member. See
		/// `ecrs.system.isContextLike`.
		bool opCall(ContextLike)(ref ContextLike contextLike) @nogc nothrow
		if (isContextLike!ContextLike) {
			return dispatch(contextLike.ctx, pool);
		}
	}
	Bound parallel(ThreadPool* pool) @nogc nothrow {
		return Bound(pool);
	}

}

// ============================================================================
// Shared traits
// ============================================================================

/// The shape a whole system takes when it happens to be a plain function
/// pointer. The combinators accept any callable system, not just this - see
/// `isSystem` - but a lift written downstream commonly produces one, so the
/// alias stays named.
alias SystemFunction = bool function(ref Context) @nogc nothrow;

/// Whether `S` can be invoked as a whole system: `bool s(ref Context)`. Every
/// shape this module hands back is one - a `SystemFunction`, `&sequential!fn`,
/// `parallel!fn(pool)`'s `Bound`, `Sequential` below - as is anything
/// downstream that follows the same convention.
private enum isSystem(S) = __traits(compiles, (ref S system, ref Context context) {
	bool result = system(context);
});

/// Ditto, for every element of a tuple. Vacuously true for none, so the
/// combinators below still accept an empty system list.
private template allSystems(Systems...) {
	static if (Systems.length == 0)
		enum allSystems = true;
	else
		enum allSystems = isSystem!(Systems[0]) && allSystems!(Systems[1 .. $]);
}

/// Whether `T` owns the `Context` a system should run against, as a `ctx`
/// member - the shape a downstream "context plus payload" type takes (DOIR's
/// `module` is one). Lets a bound schedule be invoked with that type directly
/// instead of making every call site reach for `.ctx`.
private enum isContextLike(T) = !is(immutable T == immutable Context)
	&& __traits(hasMember, T, "ctx")
	&& is(typeof(T.ctx) == Context);

// ============================================================================
// Sequential whole-system combinator
// ============================================================================

/// Combines whole systems into one pass that runs them in order, stopping at
/// the first one that fails.
///
/// Note that this is deliberately *not* what the whole-system `parallel`
/// combinator does: a `parallel` schedule has no first failure to stop at, so
/// it runs everything and ANDs. Reach for `sequential` when a later system
/// would be working on what an earlier one failed to produce (a compiler
/// schedule, say); when the systems are independent, the two are
/// interchangeable.
bool sequential(Systems...)(ref Context context, Systems systems) {
	static foreach (system; systems)
		if(!system(context))
			return false;
	return true;
}

/// Runs every one of `systems` in order and ANDs their results - `sequential`
/// without the short circuit.
///
/// This is what the whole-system `parallel` combinator degrades to when it
/// cannot actually run anything concurrently. Using `sequential` there would
/// make "does a failing system stop the ones behind it" depend on how many
/// workers the pool happened to have.
private bool andAll(Systems...)(ref Context context, Systems systems) {
	bool valid = true;
	static foreach (system; systems)
		valid &= system(context);
	return valid;
}

/// `sequential(Systems...)` with its systems bound up front: a savable,
/// copyable callable (`bool opCall(ref Context) @nogc nothrow`), so a composed
/// schedule is itself a system - storable, nestable inside another combinator,
/// or simply called as `sequential(a, b)(context)`. A plain struct is used
/// instead of a closure since capturing the systems in a delegate would need a
/// GC allocation, which isn't available under `-betterC`. The same trick
/// `parallel!fn(pool)` uses to bind its pool.
struct Sequential(Systems...) {
	private Systems systems;

	@nogc nothrow:
	this(Systems systems) { this.systems = systems; }

	bool opCall(ref Context context) { return .sequential(context, systems); }

	/// Ditto, for a type that owns its context as a `ctx` member. See
	/// `isContextLike`.
	bool opCall(ContextLike)(ref ContextLike contextLike)
	if (isContextLike!ContextLike) {
		return .sequential(contextLike.ctx, systems);
	}
}

/// Ditto.
Sequential!Systems sequential(Systems...)(Systems systems)
if (Systems.length > 0 && allSystems!Systems) {
	return Sequential!Systems(systems);
}


// ============================================================================
// Parallel whole-system combinator
// ============================================================================

/// One system queued onto the pool.
///
/// The callable is type-erased behind `invoke` rather than stored as a
/// `SystemFunction`, so a single schedule can mix plain function pointers with
/// the savable structs the combinators hand back (`Sequential`, `Parallel`,
/// `parallel!fn(pool)`'s `Bound`) - which are all systems, but share no
/// function-pointer type to be stored as.
private struct SystemJob {
	void* system;
	bool function(void*, ref Context) @nogc nothrow invoke;
	Context* context;
	bool result;
}

/// The trampoline `SystemJob.invoke` points at; one instantiation per system
/// type recovers that type and calls through it.
private template invokeSystem(System) {
	bool invokeSystem(void* system, ref Context context) @nogc nothrow {
		return (*cast(System*) system)(context);
	}
}

private void runSystem(void* arg) {
	auto job = cast(SystemJob*) arg;
	job.result = job.invoke(job.system, *job.context);
}

/// Combines whole systems (anything callable as `bool system(ref Context)`:
/// `&sequential!fn`, `parallel!fn(pool)`, another combinator's result) into one
/// that runs them concurrently via `pool` - queuing all of them at once and
/// letting workers pull the next as they finish, even if there are more
/// systems than workers - and ANDs their results together. Takes the same as
/// `ecrs.system.sequential(Systems...)`, but always runs all of them: see the
/// note there on the short circuit.
bool parallel(Systems...)(ref Context context, ThreadPool* pool, Systems systems) @trusted {
	static if (Systems.length <= 1)
		return andAll(context, systems);
	else {
		if (pool.workerCount() <= 1)
			return andAll(context, systems);

		SystemJob[Systems.length] systemJobs;
		Job[Systems.length] jobs;

		// `systems` outlives the jobs: `pool.run` below blocks until every
		// one of them has finished.
		static foreach (i, System; Systems) {
			systemJobs[i] = SystemJob(&systems[i], &invokeSystem!System, &context);
			jobs[i] = Job(&runSystem, &systemJobs[i]);
		}

		pool.run(jobs[]);

		bool valid = true;
		foreach (i; 0 .. Systems.length)
			valid &= systemJobs[i].result;

		return valid;
	}

}

/// `parallel(Systems...)` with its pool and systems bound up front: a savable,
/// copyable callable (`bool opCall(ref Context) @nogc nothrow`), so a
/// concurrent schedule is itself a system - storable, nestable inside another
/// combinator, or simply called as `parallel(pool, a, b)(context)`. The bound
/// counterpart to `sequential(Systems...)`, and the whole-system counterpart to
/// `parallel!fn(pool)`.
///
/// It runs every system it was given, however it is invoked; see the note on
/// `sequential`'s short circuit.
struct Parallel(Systems...) {
	private ThreadPool* pool;
	private Systems systems;

	@nogc nothrow:
	this(ThreadPool* pool, Systems systems) {
		this.pool = pool;
		this.systems = systems;
	}

	bool opCall(ref Context context) { return .parallel(context, pool, systems); }

	/// Ditto, for a type that owns its context as a `ctx` member. See
	/// `isContextLike`.
	bool opCall(ContextLike)(ref ContextLike contextLike)
	if (isContextLike!ContextLike) {
		return .parallel(contextLike.ctx, pool, systems);
	}
}

/// Ditto.
Parallel!Systems parallel(Systems...)(ThreadPool* pool, Systems systems)
if (Systems.length > 0 && allSystems!Systems) {
	return Parallel!Systems(pool, systems);
}

// ============================================================================
// Tests
// ============================================================================

unittest {
	struct Counter { int value; }

	static bool bump(ref Context ctx, EntityId e) @nogc nothrow {
		if (!ctx.hasComponent!Counter(e))
			return true;

		ctx.getComponent!Counter(e).value++;
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	EntityId a = ctx.addEntity();
	ctx.addComponent!Counter(a).value = 1;

	EntityId b = ctx.addEntity();
	ctx.addComponent!Counter(b).value = 10;

	assert(sequential!bump(ctx));
	assert(ctx.getComponent!Counter(a).value == 2);
	assert(ctx.getComponent!Counter(b).value == 11);
}

unittest {
	struct Counter { int value; }

	static bool bump(ref Context ctx, EntityId e) @nogc nothrow {
		if (!ctx.hasComponent!Counter(e))
			return true;

		ctx.getComponent!Counter(e).value++;
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	foreach (i; 0 .. 50) {
		EntityId e = ctx.addEntity();
		ctx.addComponent!Counter(e).value = cast(int) i;
	}

	auto pool = bc.threadpool.create(4);
	scope(exit)
		bc.threadpool.free(pool);

	assert(parallel!bump(ctx, pool));
	foreach (i; 0 .. 50)
		assert(ctx.getComponent!Counter(cast(EntityId)(i + 1)).value == cast(int) i + 1);

	// Reusing the same pool for a second call works too.
	assert(parallel!bump(ctx, pool));
	foreach (i; 0 .. 50)
		assert(ctx.getComponent!Counter(cast(EntityId)(i + 1)).value == cast(int) i + 2);

}

unittest {
	// Whole-systems combinator: each system touches a disjoint component
	// type, so running them concurrently is safe. Systems here are plain
	// `sequential!fn` instances, per the combinator's own doc comment.
	struct A { int value; }
	struct B { int value; }
	struct C { int value; }

	static bool bumpA(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!A(e))
			ctx.getComponent!A(e).value++;
		return true;
	}

	static bool bumpB(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!B(e))
			ctx.getComponent!B(e).value++;
		return true;
	}

	static bool bumpC(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!C(e))
			ctx.getComponent!C(e).value++;
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	EntityId e = ctx.addEntity();
	ctx.addComponent!A(e).value = 1;
	ctx.addComponent!B(e).value = 10;
	ctx.addComponent!C(e).value = 100;

	auto pool = bc.threadpool.create(4);
	scope(exit) bc.threadpool.free(pool);

	assert(parallel(ctx, pool, &sequential!bumpA, &sequential!bumpB, &sequential!bumpC));

	assert(ctx.getComponent!A(e).value == 2);
	assert(ctx.getComponent!B(e).value == 11);
	assert(ctx.getComponent!C(e).value == 101);

}

unittest {
	// The `sequential(Systems...)` combinator can also compose systems that
	// are themselves `parallel!fn` calls, bound to a pool via `parallel!fn(pool)`,
	// so each parallel pass fully completes before the next one starts.
	struct Counter { int value; }

	static bool bump(ref Context ctx, EntityId e) @nogc nothrow {
		if (!ctx.hasComponent!Counter(e))
			return true;

		ctx.getComponent!Counter(e).value++;
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	foreach (i; 0 .. 50) {
		EntityId e = ctx.addEntity();
		ctx.addComponent!Counter(e).value = cast(int) i;
	}

	auto pool = bc.threadpool.create(4);
	scope(exit) bc.threadpool.free(pool);

	auto runBump = parallel!bump(pool);
	assert(runBump(ctx));
	foreach (i; 0 .. 50)
		assert(ctx.getComponent!Counter(cast(EntityId)(i + 1)).value == cast(int) i + 1);

	assert(sequential(ctx, runBump, parallel!bump(pool)));
	foreach (i; 0 .. 50)
		assert(ctx.getComponent!Counter(cast(EntityId)(i + 1)).value == cast(int) i + 3);
}
unittest {
	// A pool with a single worker has nothing to spread the entities
	// across, so `parallel!fn` hands the pass to `sequential!fn` rather
	// than paying to queue one job per entity. The observable result has
	// to be the same either way.
	struct Counter { int value; }

	static bool bump(ref Context ctx, EntityId e) @nogc nothrow {
		if (!ctx.hasComponent!Counter(e))
			return true;

		ctx.getComponent!Counter(e).value++;
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	foreach (i; 0 .. 8) {
		EntityId e = ctx.addEntity();
		ctx.addComponent!Counter(e).value = cast(int) i;
	}

	auto pool = bc.threadpool.create(1);
	scope(exit) bc.threadpool.free(pool);

	assert(parallel!bump(ctx, pool));
	foreach (i; 0 .. 8)
		assert(ctx.getComponent!Counter(cast(EntityId)(i + 1)).value == cast(int) i + 1);

	// The bound form shares the same `dispatch`, so it falls back too.
	assert(parallel!bump(pool)(ctx));
	foreach (i; 0 .. 8)
		assert(ctx.getComponent!Counter(cast(EntityId)(i + 1)).value == cast(int) i + 2);
}

unittest {
	// The whole-system combinator degrades the same way: with a single
	// worker the systems run one after another, in the order given, so a
	// later system sees what an earlier one wrote.
	struct A { int value; }
	struct B { int value; }

	static bool bumpA(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!A(e))
			ctx.getComponent!A(e).value++;
		return true;
	}

	static bool copyAToB(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!A(e) && ctx.hasComponent!B(e))
			ctx.getComponent!B(e).value = ctx.getComponent!A(e).value;
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	EntityId e = ctx.addEntity();
	ctx.addComponent!A(e).value = 1;
	ctx.addComponent!B(e).value = 0;

	auto pool = bc.threadpool.create(1);
	scope(exit) bc.threadpool.free(pool);

	assert(parallel(ctx, pool, &sequential!bumpA, &sequential!copyAToB));

	assert(ctx.getComponent!A(e).value == 2);
	assert(ctx.getComponent!B(e).value == 2);
}

unittest {
	// Fewer than two systems cannot be run concurrently with anything, so
	// the whole-system combinator short-circuits to `sequential` without
	// touching the pool at all - even a pool with workers to spare. Zero
	// systems is vacuously true.
	struct A { int value; }

	static bool bumpA(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!A(e))
			ctx.getComponent!A(e).value++;
		return true;
	}

	static bool fails(ref Context) @nogc nothrow { return false; }

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	EntityId e = ctx.addEntity();
	ctx.addComponent!A(e).value = 1;

	auto pool = bc.threadpool.create(4);
	scope(exit) bc.threadpool.free(pool);

	assert(parallel(ctx, pool));

	assert(parallel(ctx, pool, &sequential!bumpA));
	assert(ctx.getComponent!A(e).value == 2);

	// A single failing system still reports the failure through.
	assert(!parallel(ctx, pool, &fails));
}

unittest {
	// The bound form of the whole-system combinator: `sequential(a, b)` with
	// no context composes the systems into one savable system, which can then
	// be run, stored, passed to another combinator, or nested in itself.
	struct A { int value; }

	static bool bumpA(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!A(e))
			ctx.getComponent!A(e).value++;
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	EntityId e = ctx.addEntity();
	ctx.addComponent!A(e).value = 0;

	auto twice = sequential(&sequential!bumpA, &sequential!bumpA);
	assert(twice(ctx));
	assert(ctx.getComponent!A(e).value == 2);

	// Savable and copyable, so it survives being stored and re-run...
	auto copy = twice;
	assert(copy(ctx));
	assert(ctx.getComponent!A(e).value == 4);

	// ... and it is itself a system, so it nests.
	assert(sequential(twice, copy)(ctx));
	assert(ctx.getComponent!A(e).value == 8);

	// A bound schedule can also be run against a type that owns its context as
	// a `ctx` member, rather than making the call site reach for `.ctx`.
	static struct Wrapper {
		Context ctx;
		int payload;
	}
	auto wrapper = Wrapper(ctx, 7);
	assert(twice(wrapper));
	assert(ctx.getComponent!A(e).value == 10);
}

unittest {
	// `sequential` stops at the first failing system; the bound form agrees
	// with it. The whole-system `parallel` combinator never does - and, since
	// it degrades to running in order when it cannot use the pool, that must
	// not depend on how many workers the pool has.
	import core.atomic : atomicLoad, atomicOp, atomicStore;

	// Shared, not `static`: the dispatched path runs systems on worker
	// threads, whose thread-local copies of a `static` counter this test would
	// never see.
	static shared int runs;

	static bool fails(ref Context) @nogc nothrow { runs.atomicOp!"+="(1); return false; }
	static bool succeeds(ref Context) @nogc nothrow { runs.atomicOp!"+="(1); return true; }

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	runs.atomicStore(0);
	assert(!sequential(ctx, &fails, &succeeds));
	assert(runs.atomicLoad() == 1);

	runs.atomicStore(0);
	assert(!sequential(&fails, &succeeds)(ctx));
	assert(runs.atomicLoad() == 1);

	// One worker: no concurrency available, so the systems run in order - but
	// all of them, exactly as the dispatched path would.
	auto serial = bc.threadpool.create(1);
	scope(exit) bc.threadpool.free(serial);
	runs.atomicStore(0);
	assert(!parallel(ctx, serial, &fails, &succeeds));
	assert(runs.atomicLoad() == 2);

	// Fewer than two systems skips the pool entirely, and likewise still runs.
	runs.atomicStore(0);
	assert(!parallel(ctx, serial, &fails));
	assert(runs.atomicLoad() == 1);

	// And with workers to spare the count is the same.
	auto pool = bc.threadpool.create(4);
	scope(exit) bc.threadpool.free(pool);
	runs.atomicStore(0);
	assert(!parallel(ctx, pool, &fails, &succeeds));
	assert(runs.atomicLoad() == 2);
}

unittest {
	// The bound form of the whole-system parallel combinator - and the thing
	// type-erasing the job record unlocked: one schedule can mix a plain
	// function pointer with the savable structs the combinators return, which
	// share no function-pointer type to have been stored as.
	struct A { int value; }
	struct B { int value; }

	static bool bumpA(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!A(e))
			ctx.getComponent!A(e).value++;
		return true;
	}

	static bool bumpB(ref Context ctx, EntityId e) @nogc nothrow {
		if (ctx.hasComponent!B(e))
			ctx.getComponent!B(e).value++;
		return true;
	}

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	EntityId e = ctx.addEntity();
	ctx.addComponent!A(e).value = 0;
	ctx.addComponent!B(e).value = 0;

	auto pool = bc.threadpool.create(4);
	scope(exit) bc.threadpool.free(pool);

	// Each system writes only its own component, so they are safe to run at
	// once. One is a function pointer, the other a `Sequential`.
	auto schedule = parallel(pool, &sequential!bumpA, sequential(&sequential!bumpB));
	assert(schedule(ctx));
	assert(ctx.getComponent!A(e).value == 1);
	assert(ctx.getComponent!B(e).value == 1);

	// Savable and copyable, and itself a system, so it nests in the others.
	auto copy = schedule;
	assert(sequential(schedule, copy)(ctx));
	assert(ctx.getComponent!A(e).value == 3);
	assert(ctx.getComponent!B(e).value == 3);

	// A `parallel!fn(pool)` per-entity walker is a system too, so it composes
	// into a whole-system schedule without being lifted to a function pointer.
	assert(parallel(pool, parallel!bumpA(pool), parallel!bumpB(pool))(ctx));
	assert(ctx.getComponent!A(e).value == 4);
	assert(ctx.getComponent!B(e).value == 4);

	// Both bound forms take a type that owns its context as a `ctx` member,
	// rather than making the call site reach for `.ctx`.
	static struct Wrapper {
		Context ctx;
		int payload;
	}
	auto wrapper = Wrapper(ctx, 7);

	assert(schedule(wrapper));
	assert(ctx.getComponent!A(e).value == 5);

	assert(parallel!bumpA(pool)(wrapper));
	assert(ctx.getComponent!A(e).value == 6);
}
