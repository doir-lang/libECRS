module ecrs.system;

import ecrs.context;
import ecrs.storage : EntityId;
import bc.threadpool;

import fp.dynarray;

import std.algorithm.searching : all;

@nogc nothrow:


template sequential(alias fn) {
	bool sequential(ref Context context) {
		foreach (e; context.entities())
			if(!fn(context, cast(EntityId) e))
				return false;
		return true;
	}

}

bool sequential(Systems...)(ref Context context, Systems systems) {
	static foreach (system; systems)
		if(!system(context)) 
			return false;
	return true;
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

	private bool dispatch(ref Context context, ThreadPool* pool) @trusted @nogc nothrow {
		if (pool.workerCount() <= 1)
			return sequential!fn(context);

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
	}
	Bound parallel(ThreadPool* pool) @nogc nothrow {
		return Bound(pool);
	}

}

// ============================================================================
// Parallel whole-system combinator
// ============================================================================

private alias SystemFunction = bool function(ref Context) @nogc nothrow;

private struct SystemJob {
	SystemFunction fn;
	Context* context;
	bool result;

}

private void runSystem(void* arg) @nogc nothrow {
	auto job = cast(SystemJob*) arg;
	job.result = job.fn(*job.context);
}

/// Combines whole systems (each `bool function(ref Context) @nogc nothrow`,
/// e.g. the result of `&parallel!fn` or `&sequential!fn`) into one that runs
/// them concurrently via `pool` - queuing all of them at once and letting
/// workers pull the next as they finish, even if there are more systems
/// than workers - and ANDs their results together. Mirrors
/// `ecrs.system.sequential(Systems...)`.
bool parallel(Systems...)(ref Context context, ThreadPool* pool, Systems systems) @trusted @nogc nothrow {
	static if (Systems.length <= 1)
		return sequential(context, systems);
	else {
		if (pool.workerCount() <= 1)
			return sequential(context, systems);

		SystemJob[Systems.length] systemJobs;
		Job[Systems.length] jobs;

		static foreach (i, system; systems) {
			systemJobs[i] = SystemJob(system, &context);
			jobs[i] = Job(&runSystem, &systemJobs[i]);
		}

		pool.run(jobs[]);

		bool valid = true;
		foreach (i; 0 .. Systems.length)
			valid &= systemJobs[i].result;

		return valid;
	}

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