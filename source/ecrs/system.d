module ecrs.system;

import ecrs.context : Context;
import ecrs.storage : EntityId;
import bct.threadpool;

import fp.dynarray;

import std.algorithm.searching : all;

@nogc nothrow:


template sequential(alias fn) {
	bool sequential(ref Context context) {
		import fp.dynarray : length;

		bool valid = true;
		foreach (e; context.entities())
			valid &= fn(context, cast(EntityId) e);
		return valid;
	}

}

bool sequential(Systems...)(ref Context context, Systems systems) {
	bool valid = true;
	static foreach (system; systems)
		valid &= system(context);
	return valid;
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

	bool parallel(ref Context context, ThreadPool* pool) @trusted @nogc nothrow {
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
	import ecrs.context : Entity;

	struct Counter { int value; }

	static bool bump(ref Context ctx, EntityId e) @nogc nothrow {
		if (!ctx.hasComponent!Counter(e))
			return true;

		ctx.getComponent!Counter(e).value++;
		return true;
	}

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	Entity a = ctx.addEntity();
	a.addComponent!Counter().value = 1;

	Entity b = ctx.addEntity();
	b.addComponent!Counter().value = 10;

	assert(sequential!bump(ctx));
	assert(a.getComponent!Counter().value == 2);
	assert(b.getComponent!Counter().value == 11);
}

unittest {
	import ecrs.context : Entity;

	struct Counter { int value; }

	static bool bump(ref Context ctx, EntityId e) @nogc nothrow {
		if (!ctx.hasComponent!Counter(e))
			return true;

		ctx.getComponent!Counter(e).value++;
		return true;
	}

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	foreach (i; 0 .. 50) {
		Entity e = ctx.addEntity();
		e.addComponent!Counter().value = cast(int) i;
	}

	auto pool = bct.threadpool.create(4);
	scope(exit)
		bct.threadpool.free(pool);

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
	import ecrs.context : Entity;

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

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	Entity e = ctx.addEntity();
	e.addComponent!A().value = 1;
	e.addComponent!B().value = 10;
	e.addComponent!C().value = 100;

	auto pool = bct.threadpool.create(4);
	scope(exit) bct.threadpool.free(pool);

	assert(parallel(ctx, pool, &sequential!bumpA, &sequential!bumpB, &sequential!bumpC));

	assert(e.getComponent!A().value == 2);
	assert(e.getComponent!B().value == 11);
	assert(e.getComponent!C().value == 101);

}