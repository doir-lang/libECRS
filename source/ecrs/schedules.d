/// Schedules, and the combinators that build them, run over a `Context` one after another or concurrently on a `bc.threadpool`.
///
/// A schedule is anything callable as `bool schedule(ref Context)`, or as `bool schedule(ref Owner)` for an owner: a type holding the context it runs against as a `context` member, such as a compiler's store alongside its query engine. `sequential!step` and `parallel!step` make a system, a schedule that runs a function over every entity, `bool step(ref Context, EntityId)`, or over every element of a slice, `bool step(ref Context, ref T)`. The other combinators, `sequential`, `parallel`, `untilStable`, `whenChanged` and `concurrentWrites`, take schedules and return one, so schedules nest. Each reports failure by returning false.
///
/// Every combinator runs over a `Context` or an owner, and passes it through: a function or schedule it runs receives the owner if it can be called with it, and the owner's `context` otherwise, so one taking `ref Context` runs under any owner. Combinators run the schedules they are given, and those bound into them, in place rather than on copies, so a schedule that keeps state, such as `whenChanged`'s, keeps it when nested.
module ecrs.schedules;

static import bc.threadpool;
static import ecrs.context;
static import ecrs.registry;
static import fp.dynarray;
static import std.traits;

@nogc nothrow:


/// The shape a schedule takes as a plain function pointer. The combinators accept any callable schedule, as `isSchedule` describes, not just this.
alias ScheduleFunction = bool function(ref ecrs.context.Context) @nogc nothrow;

/// Whether `T` is an owner: a type holding the context a schedule should run against as a `context` member, the context itself or a pointer to it, so the combinators pass it through to the functions and schedules that take it. A type naming its context otherwise can declare `alias context = store;`.
///
/// Examples:
/// ---
/// static struct Game { ecrs.context.Context context; }
/// static struct Engine { ecrs.context.Context* store; alias context = store; }
/// static assert(isContextLike!Game && isContextLike!Engine && !isContextLike!int);
/// ---
enum isContextLike(T) = !is(immutable T == immutable ecrs.context.Context)
	&& __traits(hasMember, T, "context")
	&& (is(typeof(T.context) == ecrs.context.Context) || is(typeof(T.context) == ecrs.context.Context*));

/// Whether a schedule can run over a `C`: the context itself, or an owner of one (`isContextLike`).
///
/// Examples:
/// ---
/// static struct Game { ecrs.context.Context context; }
/// static assert(isOwner!(ecrs.context.Context) && isOwner!Game && !isOwner!int);
/// ---
enum isOwner(C) = is(C == ecrs.context.Context) || isContextLike!C;

/// The context `owner` is, or holds as its `context`.
///
/// Examples:
/// ---
/// static struct Engine { ecrs.context.Context* store; alias context = store; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// auto engine = Engine(&context);
/// assert(&contextOf(engine) is &context && &contextOf(context) is &context);
/// ---
ref ecrs.context.Context contextOf(C)(return ref C owner) if (isOwner!C) {
	static if (is(C == ecrs.context.Context)) return owner;
	else static if (is(typeof(owner.context) == ecrs.context.Context*)) return *owner.context;
	else return owner.context;
}

/// Whether `S` can be invoked as a schedule: `bool s(ref Context)`, `bool s(ref Owner)`, or a struct whose `opCall` may take only owners.
///
/// Examples:
/// ---
/// static bool step(ref ecrs.context.Context) @nogc nothrow { return true; }
/// static assert(isSchedule!(typeof(&step)) && !isSchedule!int);
/// ---
template isSchedule(S) {
	static if (__traits(compiles, (ref S schedule, ref ecrs.context.Context context) { bool result = schedule(context); }))
		enum isSchedule = true;
	else static if (is(S == struct) && __traits(hasMember, S, "opCall"))
		enum isSchedule = true;
	else static if (std.traits.isCallable!S && __traits(compiles, std.traits.Parameters!S))
		enum isSchedule = is(std.traits.ReturnType!S == bool) && std.traits.Parameters!S.length == 1 && isContextLike!(std.traits.Parameters!S[0]);
	else
		enum isSchedule = false;
}

private template allSchedules(Schedules...) {
	static if (Schedules.length == 0)
		enum allSchedules = true;
	else
		enum allSchedules = isSchedule!(Schedules[0]) && allSchedules!(Schedules[1 .. $]);
}

// Runs `schedule` over `owner`, or over the context it holds if `schedule` does not take it.
private bool runOver(S, C)(ref S schedule, ref C owner) {
	static if (__traits(compiles, schedule(owner))) return schedule(owner);
	else return schedule(contextOf(owner));
}

// Calls `step` with `owner` and `arg`, or with the context `owner` holds if `step` does not take it.
private bool callOver(alias step, C, A)(ref C owner, ref A arg) {
	static if (__traits(compiles, step(owner, arg))) return step(owner, arg);
	else return step(contextOf(owner), arg);
}


/// Systems that run `step` in order, stopping at the first call that fails, and return whether every visited call succeeded:
///
/// - `sequential!step(owner)` calls `step` on every live entity, as `bool step(ref Context, EntityId)`;
/// - `sequential!step(owner, items)` on every element of `items`, as `bool step(ref Context, ref T)`, so a pass can fan out over work items rather than entities;
/// - `sequential!step()` and `sequential!step(items)` return those systems as copyable structs, schedules in their own right; `items` must outlive its system.
///
/// `owner` is a `Context` or an owner, and `step` may take either, as the module documentation says.
///
/// Examples:
/// ---
/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
/// static bool positive(ref ecrs.context.Context, ref int item) @nogc nothrow { return item > 0; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// int[3] items = [1, 2, -3];
/// assert(sequential!visit(context) && sequential!visit()(context));
/// assert(sequential!positive(context, items[0 .. 2]) && !sequential!positive(context, items[]));
/// assert(sequential!positive(items[0 .. 2])(context));
/// ---
template sequential(alias step) {
	bool sequential(C)(ref C owner) if (isOwner!C) {
		foreach (e; ecrs.context.entities(contextOf(owner)))
			if (!callOver!step(owner, e))
				return false;
		return true;
	}

	bool sequential(C, T)(ref C owner, T[] items) if (isOwner!C) {
		foreach (ref item; items)
			if (!callOver!step(owner, item))
				return false;
		return true;
	}

	SequentialEntities!step sequential()() {
		return SequentialEntities!step();
	}

	SequentialItems!(step, T) sequential(T)(T[] items) {
		return SequentialItems!(step, T)(items);
	}
}

/// `sequential!step` over every entity as a copyable struct, from `sequential!step()`.
///
/// Examples:
/// ---
/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
/// SequentialEntities!visit pass = sequential!visit();
/// auto copy = pass;
/// ---
struct SequentialEntities(alias step) {
	@nogc nothrow:
	/// Runs the pass over `owner`, a `Context` or an owner.
	///
	/// Examples:
	/// ---
	/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// assert(sequential!visit()(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .sequential!step(owner); }
}

/// `sequential!step` over a slice as a copyable struct, from `sequential!step(items)`; the slice must outlive it.
///
/// Examples:
/// ---
/// static bool positive(ref ecrs.context.Context, ref int item) @nogc nothrow { return item > 0; }
/// int[2] items = [1, 2];
/// SequentialItems!(positive, int) pass = sequential!positive(items[]);
/// auto copy = pass;
/// ---
struct SequentialItems(alias step, T) {
	private T[] items;

	@nogc nothrow:
	/// Runs the pass over `owner`, a `Context` or an owner.
	///
	/// Examples:
	/// ---
	/// static bool positive(ref ecrs.context.Context, ref int item) @nogc nothrow { return item > 0; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// int[2] items = [1, 2];
	/// assert(sequential!positive(items[])(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .sequential!step(owner, items); }
}


// The pool whose job this thread runs, if any; a job may not wait on its own pool, so passes nested in one run inline.
private bc.threadpool.ThreadPool* runningPool = null;

private bool canDispatch(bc.threadpool.ThreadPool* pool) {
	return pool !is null && bc.threadpool.workerCount(pool) > 1 && runningPool !is pool;
}

// One element of a slice pass queued onto the pool.
private struct ItemJob(C, T) {
	C* owner;
	bc.threadpool.ThreadPool* pool;
	T* item;
	bool result = true;
}

private void runItem(alias step, C, T)(void* arg) {
	auto job = cast(ItemJob!(C, T)*) arg;
	auto outer = runningPool;
	runningPool = job.pool;
	scope(exit) runningPool = outer;
	job.result = callOver!step(*job.owner, *job.item);
}

// Runs `step` over every element in order and ANDs the results: what a parallel pass does when it cannot run anything concurrently.
private bool andAllItems(alias step, C, T)(ref C owner, T[] items) {
	bool valid = true;
	foreach (ref item; items)
		valid &= callOver!step(owner, item);
	return valid;
}

// `parallel!step` over `items`; the caller has marked the context as in parallel.
private bool dispatchItems(alias step, C, T)(ref C owner, bc.threadpool.ThreadPool* pool, T[] items) @trusted {
	immutable n = items.length;
	if (n <= 1 || !canDispatch(pool))
		return andAllItems!step(owner, items);

	ItemJob!(C, T)* itemJobs = fp.dynarray.create!(ItemJob!(C, T))(n);
	scope(exit) fp.dynarray.free(itemJobs);
	bc.threadpool.Job* jobs = fp.dynarray.create!(bc.threadpool.Job)(n);
	scope(exit) fp.dynarray.free(jobs);
	if (itemJobs is null || jobs is null)
		return andAllItems!step(owner, items);

	foreach (i, ref item; items) {
		itemJobs[i] = ItemJob!(C, T)(&owner, pool, &item);
		jobs[i] = bc.threadpool.Job(&runItem!(step, C, T), &itemJobs[i]);
	}
	if (!bc.threadpool.run(pool, jobs[0 .. n]))
		return andAllItems!step(owner, items);

	bool valid = true;
	foreach (j; 0 .. n) valid &= itemJobs[j].result;
	return valid;
}

/// Systems that run `step` concurrently on `pool`, one job per call, and return whether every call succeeded:
///
/// - `parallel!step(owner, pool)` calls `step` on every live entity, as `bool step(ref Context, EntityId)`;
/// - `parallel!step(owner, pool, items)` on every element of `items`, as `bool step(ref Context, ref T)`; each job has its element to itself, so it may write it;
/// - `parallel!step(pool)` and `parallel!step(pool, items)` return those systems as copyable structs; `items` must outlive its system.
///
/// Unlike `sequential!step` it never stops early, so running inline makes exactly the calls the pool would; it runs inline with fewer than two calls, a null or single-worker pool, inside one of `pool`'s own jobs, which may not wait on it, and when allocating or submitting the jobs fails. `owner` is a `Context` or an owner, and `step` may take either, as the module documentation says.
///
/// Examples:
/// ---
/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
/// static bool double_(ref ecrs.context.Context, ref int item) @nogc nothrow { item *= 2; return true; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// assert(parallel!visit(context, pool) && parallel!visit(pool)(context));
/// int[3] items = [1, 2, 3];
/// assert(parallel!double_(context, pool, items[]) && parallel!double_(pool, items[1 .. 2])(context));
/// assert(items == [2, 8, 6]);
/// ---
template parallel(alias step) {
	private bool andAllEntities(C)(ref C owner) {
		bool valid = true;
		foreach (e; ecrs.context.entities(contextOf(owner)))
			valid &= callOver!step(owner, e);
		return valid;
	}

	bool parallel(C)(ref C owner, bc.threadpool.ThreadPool* pool) @trusted if (isOwner!C) {
		// Marked even when it runs inline, so a structural change fails the same way whatever the pool size.
		ecrs.context.enterParallel(contextOf(owner));
		scope(exit) ecrs.context.exitParallel(contextOf(owner));
		if (!canDispatch(pool))
			return andAllEntities(owner);
		ecrs.registry.EntityId* ids = fp.dynarray.create!(ecrs.registry.EntityId)(ecrs.context.entityCount(contextOf(owner)));
		scope(exit) fp.dynarray.free(ids);
		if (ids is null)
			return andAllEntities(owner);
		size_t n = 0;
		foreach (e; ecrs.context.entities(contextOf(owner))) ids[n++] = e;
		return dispatchItems!step(owner, pool, ids[0 .. n]);
	}

	bool parallel(C, T)(ref C owner, bc.threadpool.ThreadPool* pool, T[] items) if (isOwner!C) {
		ecrs.context.enterParallel(contextOf(owner));
		scope(exit) ecrs.context.exitParallel(contextOf(owner));
		return dispatchItems!step(owner, pool, items);
	}

	ParallelEntities!step parallel(bc.threadpool.ThreadPool* pool) {
		return ParallelEntities!step(pool);
	}

	ParallelItems!(step, T) parallel(T)(bc.threadpool.ThreadPool* pool, T[] items) {
		return ParallelItems!(step, T)(pool, items);
	}
}

/// `parallel!step` over every entity as a copyable struct, with its pool bound, from `parallel!step(pool)`.
///
/// Examples:
/// ---
/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
/// ParallelEntities!visit pass = parallel!visit(null);
/// auto copy = pass;
/// ---
struct ParallelEntities(alias step) {
	private bc.threadpool.ThreadPool* pool;

	@nogc nothrow:
	/// Runs the pass over `owner`, a `Context` or an owner.
	///
	/// Examples:
	/// ---
	/// static bool visit(ref ecrs.context.Context, ecrs.registry.EntityId) @nogc nothrow { return true; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// auto pool = bc.threadpool.create(2);
	/// scope(exit) bc.threadpool.free(pool);
	/// assert(parallel!visit(pool)(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .parallel!step(owner, pool); }
}

/// `parallel!step` over a slice as a copyable struct, with its pool and the slice bound, from `parallel!step(pool, items)`; the slice must outlive it.
///
/// Examples:
/// ---
/// static bool positive(ref ecrs.context.Context, ref int item) @nogc nothrow { return item > 0; }
/// int[2] items = [1, 2];
/// ParallelItems!(positive, int) pass = parallel!positive(null, items[]);
/// auto copy = pass;
/// ---
struct ParallelItems(alias step, T) {
	private bc.threadpool.ThreadPool* pool;
	private T[] items;

	@nogc nothrow:
	/// Runs the pass over `owner`, a `Context` or an owner.
	///
	/// Examples:
	/// ---
	/// static bool positive(ref ecrs.context.Context, ref int item) @nogc nothrow { return item > 0; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// auto pool = bc.threadpool.create(2);
	/// scope(exit) bc.threadpool.free(pool);
	/// int[2] items = [1, 2];
	/// assert(parallel!positive(pool, items[])(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .parallel!step(owner, pool, items); }
}


/// Runs schedules over `owner`, a `Context` or an owner, in order, stopping at the first that fails, and returns whether all of them succeeded. Unlike the schedule-taking `parallel`, which has no first failure to stop at, it suits schedules that work on what earlier ones produce.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// static bool fails(ref ecrs.context.Context) @nogc nothrow { return false; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// assert(sequential(context, &succeeds, &succeeds));
/// assert(!sequential(context, &fails, &succeeds));
/// ---
bool sequential(C, Schedules...)(ref C owner, auto ref Schedules schedules) if (isOwner!C) {
	static foreach (schedule; schedules)
		if (!runOver(schedule, owner))
			return false;
	return true;
}

// Runs every schedule in order and ANDs the results: what `parallel` does when it cannot run anything concurrently.
private bool andAll(C, Schedules...)(ref C owner, auto ref Schedules schedules) {
	bool valid = true;
	static foreach (schedule; schedules)
		valid &= runOver(schedule, owner);
	return valid;
}

/// `sequential(Schedules...)` with its schedules bound, from `sequential(schedules)`: a copyable struct that is itself a schedule, so it can be stored, nested in another combinator, or run over an owner.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// Sequential!(typeof(&succeeds)) schedule = sequential(&succeeds);
/// auto copy = schedule;
/// ---
struct Sequential(Schedules...) {
	private Schedules schedules;

	@nogc nothrow:
	/// Runs the schedules over `owner`, a `Context` or an owner.
	///
	/// Examples:
	/// ---
	/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// assert(sequential(&succeeds)(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .sequential(owner, schedules); }
}

/// Ditto
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// auto schedule = sequential(&succeeds, &succeeds);
/// assert(schedule(context));
/// ---
Sequential!Schedules sequential(Schedules...)(Schedules schedules) if (Schedules.length > 0 && allSchedules!Schedules) {
	return Sequential!Schedules(schedules);
}


// One schedule queued onto the pool, its callable type-erased so a schedule can combine function pointers with the combinators' structs.
private struct ScheduleJob(C) {
	void* schedule;
	bool function(void*, ref C) @nogc nothrow invoke;
	C* owner;
	bc.threadpool.ThreadPool* pool;
	bool result;
}

// wrapper: adapts a call to the function-pointer type a hook slot requires
private bool invokeSchedule(S, C)(void* schedule, ref C owner) {
	return runOver(*cast(S*) schedule, owner);
}

private void runSchedule(C)(void* arg) {
	auto job = cast(ScheduleJob!C*) arg;
	auto outer = runningPool;
	runningPool = job.pool;
	scope(exit) runningPool = outer;
	job.result = job.invoke(job.schedule, *job.owner);
}

/// Runs schedules over `owner`, a `Context` or an owner, concurrently on `pool`, queuing all of them at once, and returns whether every one succeeded. Every schedule runs, however many fail; with fewer than two schedules, a single-worker pool, a call from inside one of `pool`'s own jobs, or a pool that cannot take the jobs, they run inline, in the order given.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// assert(parallel(context, pool, &succeeds, &succeeds));
/// ---
bool parallel(C, Schedules...)(ref C owner, bc.threadpool.ThreadPool* pool, auto ref Schedules schedules) @trusted if (isOwner!C) {
	ecrs.context.enterParallel(contextOf(owner));
	scope(exit) ecrs.context.exitParallel(contextOf(owner));
	static if (Schedules.length <= 1)
		return andAll(owner, schedules);
	else {
		if (!canDispatch(pool))
			return andAll(owner, schedules);

		ScheduleJob!C[Schedules.length] scheduleJobs;
		bc.threadpool.Job[Schedules.length] jobs;
		static foreach (i, Schedule; Schedules) {
			scheduleJobs[i] = ScheduleJob!C(&schedules[i], &invokeSchedule!(Schedule, C), &owner, pool);
			jobs[i] = bc.threadpool.Job(&runSchedule!C, &scheduleJobs[i]);
		}
		// `run` blocks until every job finishes, so `schedules` outlives them.
		if (!bc.threadpool.run(pool, jobs[]))
			return andAll(owner, schedules);

		bool valid = true;
		foreach (i; 0 .. Schedules.length)
			valid &= scheduleJobs[i].result;
		return valid;
	}
}

/// `parallel(Schedules...)` with its pool and schedules bound, from `parallel(pool, schedules)`: a copyable struct that is itself a schedule, as `Sequential` is.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// Parallel!(typeof(&succeeds)) schedule = parallel(pool, &succeeds);
/// auto copy = schedule;
/// ---
struct Parallel(Schedules...) {
	private bc.threadpool.ThreadPool* pool;
	private Schedules schedules;

	@nogc nothrow:
	/// Runs the schedules over `owner`, a `Context` or an owner.
	///
	/// Examples:
	/// ---
	/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// auto pool = bc.threadpool.create(2);
	/// scope(exit) bc.threadpool.free(pool);
	/// assert(parallel(pool, &succeeds, &succeeds)(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .parallel(owner, pool, schedules); }
}

/// Ditto
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// auto schedule = parallel(pool, &succeeds, &succeeds);
/// assert(schedule(context));
/// ---
Parallel!Schedules parallel(Schedules...)(bc.threadpool.ThreadPool* pool, Schedules schedules) if (Schedules.length > 0 && allSchedules!Schedules) {
	return Parallel!Schedules(pool, schedules);
}


// Generations only advance, so their sum is unchanged exactly when every one is.
private size_t watchedGeneration(const ref ecrs.context.Context context, const(size_t)[] watched) {
	if (watched is null) return ecrs.context.generation(context);
	size_t sum = 0;
	foreach (id; watched) sum += ecrs.context.generation(context, id);
	return sum;
}

/// Runs `schedule` over `owner`, a `Context` or an owner, until a run changes no component `watched` names, or with `watched` null, no component at all, as `ecrs.context.generation` sees it. Returns false as soon as a run fails, and true once one changes nothing; it runs at least once, and never stops if the schedule changes something every run. A mutable access counts as a change, so a schedule meant to settle should read through a `const` context.
///
/// Examples:
/// ---
/// static bool countToThree(ref ecrs.context.Context context) @nogc nothrow {
/// 	auto e = cast(ecrs.registry.EntityId) 1;
/// 	if (ecrs.context.getComponent!int(cast(const) context, e) < 3) ++ecrs.context.getForWriting!int(context, e);
/// 	return true;
/// }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// assert(ecrs.context.addComponent!int(context, ecrs.context.addEntity(context)) !is null);
/// assert(untilStable(context, &countToThree));
/// assert(ecrs.context.getComponent!int(context, 1) == 3);
/// ---
bool untilStable(C, Schedule)(ref C owner, auto ref Schedule schedule, const(size_t)[] watched = null) if (isOwner!C && isSchedule!Schedule) {
	while (true) {
		immutable before = watchedGeneration(contextOf(owner), watched);
		if (!runOver(schedule, owner)) return false;
		if (watchedGeneration(contextOf(owner), watched) == before) return true;
	}
}

/// `untilStable` with its schedule and watched components bound, from `untilStable(schedule, watched)`: a copyable struct that is itself a schedule, as `Sequential` is. `watched` must outlive it.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// UntilStable!(typeof(&succeeds)) settle = untilStable(&succeeds);
/// auto copy = settle;
/// ---
struct UntilStable(Schedule) {
	private Schedule schedule;
	private const(size_t)[] watched;

	@nogc nothrow:
	/// Runs the schedule over `owner`, a `Context` or an owner, until it settles.
	///
	/// Examples:
	/// ---
	/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// assert(untilStable(&succeeds)(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .untilStable(owner, schedule, watched); }
}

/// Ditto
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// immutable size_t[1] watched = [ecrs.registry.componentId!int()];
/// auto settle = untilStable(sequential(&succeeds), watched[]);
/// assert(settle(context));
/// ---
UntilStable!Schedule untilStable(Schedule)(Schedule schedule, const(size_t)[] watched = null) if (isSchedule!Schedule) {
	return UntilStable!Schedule(schedule, watched);
}


/// The `seen` a `whenChanged` schedule starts from, so its first call runs.
enum size_t neverRan = size_t.max;

/// Runs `schedule` over `owner`, a `Context` or an owner, unless no component `watched` names, or with `watched` null, no component at all, has changed, as `ecrs.context.generation` sees it, since the run that left `seen`. A run that succeeds sets `seen` after it, so the schedule's own writes do not count as changes; start `seen` at `neverRan`. Returns true when it skips, and otherwise what the schedule returns, leaving `seen` as it was when that is false, so the next call runs it again.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// size_t seen = neverRan;
/// assert(whenChanged(context, &succeeds, seen) && seen != neverRan);
/// assert(whenChanged(context, &succeeds, seen)); // skipped: nothing changed
/// ---
bool whenChanged(C, Schedule)(ref C owner, auto ref Schedule schedule, ref size_t seen, const(size_t)[] watched = null) if (isOwner!C && isSchedule!Schedule) {
	if (seen != neverRan && watchedGeneration(contextOf(owner), watched) == seen) return true;
	if (!runOver(schedule, owner)) return false;
	seen = watchedGeneration(contextOf(owner), watched);
	return true;
}

/// `whenChanged` with its schedule and watched components bound, from `whenChanged(schedule, watched)`: a copyable struct that is itself a schedule, as `Sequential` is, remembering its own last run, so each copy tracks changes separately. `watched` must outlive it.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// WhenChanged!(typeof(&succeeds)) onChange = whenChanged(&succeeds);
/// auto copy = onChange;
/// ---
struct WhenChanged(Schedule) {
	private Schedule schedule;
	private const(size_t)[] watched;
	private size_t seen = neverRan;

	@nogc nothrow:
	/// Runs the schedule over `owner`, a `Context` or an owner, if what it watches changed since it last ran.
	///
	/// Examples:
	/// ---
	/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// auto onChange = whenChanged(&succeeds);
	/// assert(onChange(context) && onChange(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .whenChanged(owner, schedule, seen, watched); }
}

/// Ditto
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// immutable size_t[1] watched = [ecrs.registry.componentId!int()];
/// auto schedule = sequential(whenChanged(&succeeds, watched[]), &succeeds);
/// assert(schedule(context));
/// ---
WhenChanged!Schedule whenChanged(Schedule)(Schedule schedule, const(size_t)[] watched = null) if (isSchedule!Schedule) {
	return WhenChanged!Schedule(schedule, watched);
}


/// Runs `schedule` over `owner`, a `Context` or an owner, between `ecrs.context.beginConcurrentWrites` and `endConcurrentWrites`, so the parallel combinators inside it may add, set and remove components of the entities each job owns; ready every storage they add to with `ecrs.context.reserveConcurrentAdds` first. Returns what the schedule returns. Like the phase it opens, it must not run inside a parallel combinator, nor inside another of its kind.
///
/// Examples:
/// ---
/// static bool tag(ref ecrs.context.Context context, ref ecrs.registry.EntityId e) @nogc nothrow { return ecrs.context.addComponent!int(context, e) !is null; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// ecrs.registry.EntityId[2] owned = [ecrs.context.addEntity(context), ecrs.context.addEntity(context)];
/// auto pool = bc.threadpool.create(2);
/// scope(exit) bc.threadpool.free(pool);
/// assert(ecrs.context.reserveConcurrentAdds!int(context, owned.length));
/// assert(concurrentWrites(context, parallel!tag(pool, owned[])));
/// assert(ecrs.context.hasComponent!int(context, owned[1]));
/// ---
bool concurrentWrites(C, Schedule)(ref C owner, auto ref Schedule schedule) if (isOwner!C && isSchedule!Schedule) {
	ecrs.context.beginConcurrentWrites(contextOf(owner));
	scope(exit) ecrs.context.endConcurrentWrites(contextOf(owner));
	return runOver(schedule, owner);
}

/// `concurrentWrites` with its schedule bound, from `concurrentWrites(schedule)`: a copyable struct that is itself a schedule, as `Sequential` is.
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// ConcurrentWrites!(typeof(&succeeds)) phase = concurrentWrites(&succeeds);
/// auto copy = phase;
/// ---
struct ConcurrentWrites(Schedule) {
	private Schedule schedule;

	@nogc nothrow:
	/// Runs the schedule over `owner`, a `Context` or an owner, within a concurrent-writes phase.
	///
	/// Examples:
	/// ---
	/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
	/// auto context = ecrs.context.create();
	/// scope(exit) ecrs.context.free(context);
	/// assert(concurrentWrites(&succeeds)(context));
	/// ---
	bool opCall(C)(ref C owner) if (isOwner!C) { return .concurrentWrites(owner, schedule); }
}

/// Ditto
///
/// Examples:
/// ---
/// static bool succeeds(ref ecrs.context.Context) @nogc nothrow { return true; }
/// auto context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// auto schedule = sequential(&succeeds, concurrentWrites(&succeeds));
/// assert(schedule(context));
/// ---
ConcurrentWrites!Schedule concurrentWrites(Schedule)(Schedule schedule) if (isSchedule!Schedule) {
	return ConcurrentWrites!Schedule(schedule);
}


version(unittest) {
	private struct Counter(int tag) { int value; }

	// Increments the entity's `C`, if it has one.
	private bool bump(C = Counter!0)(ref ecrs.context.Context context, ecrs.registry.EntityId e) {
		if (ecrs.context.hasComponent!C(context, e))
			++ecrs.context.getForWriting!C(context, e).value;
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
	// Systems over entities, sequential and on pools of one and several workers, bound or not.
	auto context = countedContext(50);
	scope(exit) ecrs.context.free(context);

	assert(sequential!bump(context));
	foreach (i; 0 .. 50) assert(valueOf(context, i + 1) == i + 1);

	// sequential!step stops at the first entity that fails.
	static size_t visited;
	static bool failsAtTwo(ref ecrs.context.Context, ecrs.registry.EntityId e) @nogc nothrow {
		++visited;
		return e != 2;
	}
	visited = 0;
	assert(!sequential!failsAtTwo(context));
	assert(visited == 3);

	foreach (workers; [1, 4]) {
		auto pool = makePool(workers);
		scope(exit) bc.threadpool.free(pool);
		immutable before = valueOf(context, 1);
		assert(parallel!bump(context, pool));
		assert(parallel!bump(pool)(context));
		foreach (i; 0 .. 50) assert(valueOf(context, i + 1) == i + before + 2);
	}

	// Bound per-entity passes compose sequentially, each finishing before the next starts.
	auto pool = makePool(4);
	scope(exit) bc.threadpool.free(pool);
	immutable before = valueOf(context, 1);
	auto runBump = parallel!bump(pool);
	assert(sequential(context, runBump, parallel!bump(pool)));
	assert(valueOf(context, 1) == before + 2);

	// Failing to allocate the jobs runs the pass inline instead.
	ecrs.registry.failAllocationsAfter(0);
	immutable passed = parallel!bump(context, pool);
	ecrs.registry.restoreAllocations();
	assert(passed && valueOf(context, 1) == before + 3);

	// A fresh pool's job stack must grow, so failing that allocation makes the pool refuse the jobs, and the pass runs inline.
	auto fresh = makePool(4);
	scope(exit) bc.threadpool.free(fresh);
	ecrs.registry.failAllocationsAfter(3);
	immutable refused = parallel!bump(context, fresh);
	ecrs.registry.restoreAllocations();
	assert(refused && valueOf(context, 1) == before + 4);

	// Run over an owner, a function taking it receives it, and one taking a `Context` receives its `context`.
	import core.atomic : atomicLoad, atomicOp;
	static struct Owner { ecrs.context.Context context; shared size_t visits; }
	static bool visitOwner(ref Owner owner, ecrs.registry.EntityId e) @nogc nothrow {
		owner.visits.atomicOp!"+="(1);
		return bump(owner.context, e);
	}
	auto owner = Owner(context);
	assert(sequential!visitOwner(owner) && sequential!visitOwner()(owner) && sequential!bump(owner));
	assert(parallel!visitOwner(owner, pool) && parallel!visitOwner(pool)(owner) && parallel!bump(pool)(owner));
	assert(owner.visits.atomicLoad() == 4 * ecrs.context.entityCount(context) && valueOf(context, 1) == before + 10);
}

unittest {
	// Slice passes: sequential stops at the first failure, parallel runs every element, on null, one- and several-worker pools, bound or not.
	import core.atomic : atomicLoad, atomicOp, atomicStore;
	static shared int runs;
	static bool bumpItem(ref ecrs.context.Context, ref int item) @nogc nothrow { runs.atomicOp!"+="(1); return ++item != 3; }

	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);
	int[64] items = 0;
	items[1] = 2;

	runs.atomicStore(0);
	assert(!sequential!bumpItem(context, items[]));
	assert(runs.atomicLoad() == 2 && items[0] == 1 && items[1] == 3 && items[2] == 0);
	assert(sequential!bumpItem(context, items[2 .. 4]));
	assert(sequential!bumpItem(context, items[0 .. 0]));
	assert(sequential!bumpItem(items[4 .. 6])(context));
	assert(items[2] == 1 && items[4] == 1 && items[6] == 0);

	foreach (workers; [0, 1, 4]) {
		auto pool = workers ? makePool(workers) : null;
		scope(exit) if (pool) bc.threadpool.free(pool);
		items[] = 0;
		items[7] = 2;
		runs.atomicStore(0);
		assert(!parallel!bumpItem(context, pool, items[]));
		assert(runs.atomicLoad() == items.length);
		foreach (i, item; items) assert(item == (i == 7 ? 3 : 1));
		assert(parallel!bumpItem(pool, items[8 .. $])(context));
		assert(items[8] == 2 && items[6] == 1);
		assert(parallel!bumpItem(context, pool, items[0 .. 0]));
	}

	// Failing to allocate the jobs, or a fresh pool refusing them, runs the pass inline.
	auto fresh = makePool(4);
	scope(exit) bc.threadpool.free(fresh);
	items[] = 0;
	foreach (after; [0, 2]) {
		ecrs.registry.failAllocationsAfter(after);
		immutable passed = parallel!bumpItem(context, fresh, items[]);
		ecrs.registry.restoreAllocations();
		assert(passed);
	}
	foreach (item; items) assert(item == 2);

	// Run over an owner, a function taking it receives it, sequentially and on the pool, bound or not.
	static struct Tally { ecrs.context.Context context; shared int total; }
	static bool addItem(ref Tally tally, ref int item) @nogc nothrow {
		tally.total.atomicOp!"+="(item);
		return true;
	}
	auto tally = Tally(context);
	int[4] some = [10, 20, 30, 40];
	assert(sequential!addItem(tally, some[]) && sequential!addItem(some[])(tally));
	assert(parallel!addItem(tally, fresh, some[]) && parallel!addItem(fresh, some[])(tally) && parallel!bumpItem(fresh, some[])(tally));
	assert(tally.total.atomicLoad() == 400 && some == [11, 21, 31, 41]);
}

unittest {
	// Schedule combinators: concurrent schedules touching disjoint components, and in-order fallbacks.
	alias A = Counter!1, B = Counter!2, C = Counter!3;
	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);
	immutable e = ecrs.context.addEntity(context);
	ecrs.context.addComponent!A(context, e).value = 1;
	ecrs.context.addComponent!B(context, e).value = 10;
	ecrs.context.addComponent!C(context, e).value = 100;

	auto pool = makePool(4);
	scope(exit) bc.threadpool.free(pool);
	assert(parallel(context, pool, sequential!(bump!A)(), sequential!(bump!B)(), sequential!(bump!C)()));
	assert(valueOf!A(context, e) == 2 && valueOf!B(context, e) == 11 && valueOf!C(context, e) == 101);

	// With one worker the schedules run in the order given, so a later one sees what an earlier one wrote.
	static bool copyAToB(ref ecrs.context.Context context, ecrs.registry.EntityId e) @nogc nothrow {
		if (ecrs.context.hasComponent!A(context, e) && ecrs.context.hasComponent!B(context, e))
			if (ecrs.context.hasComponent!A(context, e) && ecrs.context.hasComponent!B(context, e))
			ecrs.context.getForWriting!B(context, e).value = ecrs.context.getForWriting!A(context, e).value;
		return true;
	}
	auto serial = makePool(1);
	scope(exit) bc.threadpool.free(serial);
	assert(parallel(context, serial, sequential!(bump!A)(), sequential!copyAToB()));
	assert(valueOf!A(context, e) == 3 && valueOf!B(context, e) == 3);

	// Fewer than two schedules skip the pool; none is vacuously true, and one failure still reports through.
	static bool fails(ref ecrs.context.Context) @nogc nothrow { return false; }
	assert(parallel(context, pool));
	assert(parallel(context, pool, sequential!(bump!A)()));
	assert(valueOf!A(context, e) == 4);
	assert(!parallel(context, pool, &fails));

	// A pool that cannot take the jobs runs the schedules inline.
	auto fresh = makePool(4);
	scope(exit) bc.threadpool.free(fresh);
	ecrs.registry.failAllocationsAfter(0);
	immutable refused = parallel(context, fresh, sequential!(bump!A)(), sequential!(bump!A)());
	ecrs.registry.restoreAllocations();
	assert(refused && valueOf!A(context, e) == 6);
}

unittest {
	// sequential stops at the first failure, bound or not; parallel never does, whatever the pool.
	import core.atomic : atomicLoad, atomicOp, atomicStore;

	// Shared, since worker threads would bump their own thread-local copies of a static.
	static shared int runs;
	static bool fails(ref ecrs.context.Context) @nogc nothrow { runs.atomicOp!"+="(1); return false; }
	static bool succeeds(ref ecrs.context.Context) @nogc nothrow { runs.atomicOp!"+="(1); return true; }

	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);

	runs.atomicStore(0);
	assert(!sequential(context, &fails, &succeeds));
	assert(runs.atomicLoad() == 1);

	runs.atomicStore(0);
	assert(!sequential(&fails, &succeeds)(context));
	assert(runs.atomicLoad() == 1);

	foreach (workers; [1, 4]) {
		auto pool = makePool(workers);
		scope(exit) bc.threadpool.free(pool);
		runs.atomicStore(0);
		assert(!parallel(context, pool, &fails, &succeeds));
		assert(runs.atomicLoad() == 2);
		runs.atomicStore(0);
		assert(!parallel(context, pool, &fails));
		assert(runs.atomicLoad() == 1);
	}
}

unittest {
	// Bound schedules are copyable, and nest, combine function pointers with structs, and take a context owner.
	alias A = Counter!1, B = Counter!2;
	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);
	immutable e = ecrs.context.addEntity(context);
	ecrs.context.addComponent!A(context, e).value = 0;
	ecrs.context.addComponent!B(context, e).value = 0;

	auto twice = sequential(sequential!(bump!A)(), sequential!(bump!A)());
	assert(twice(context));
	auto copy = twice;
	assert(copy(context));
	assert(sequential(twice, copy)(context));
	assert(valueOf!A(context, e) == 8);

	auto pool = makePool(4);
	scope(exit) bc.threadpool.free(pool);
	auto schedule = parallel(pool, sequential!(bump!A)(), sequential(sequential!(bump!B)()));
	assert(schedule(context));
	auto scheduleCopy = schedule;
	assert(sequential(schedule, scheduleCopy)(context));
	assert(valueOf!A(context, e) == 11 && valueOf!B(context, e) == 3);

	assert(parallel(pool, parallel!(bump!A)(pool), parallel!(bump!B)(pool))(context));
	assert(valueOf!A(context, e) == 12 && valueOf!B(context, e) == 4);

	static struct Wrapper {
		ecrs.context.Context context;
		int payload;
	}
	auto wrapper = Wrapper(context, 7);
	assert(twice(wrapper));
	assert(schedule(wrapper));
	assert(parallel!(bump!A)(pool)(wrapper));
	assert(valueOf!A(context, e) == 16);

	// A schedule taking the owner receives it however deeply nested, beside ones taking a `Context`, as do the systems among them.
	// Atomic, since `parallel(game, pool, &tick, &tick)` ticks from two threads at once.
	import core.atomic : atomicLoad, atomicOp;
	static struct Game { ecrs.context.Context context; shared int ticks; }
	static bool tick(ref Game game) @nogc nothrow { game.ticks.atomicOp!"+="(1); return true; }
	static bool tickPer(ref Game game, ecrs.registry.EntityId) @nogc nothrow { game.ticks.atomicOp!"+="(1); return true; }
	auto game = Game(context);
	assert(sequential(game, &tick, sequential(&tick, sequential!tickPer(), sequential!(bump!A)()), parallel(pool, &tick)));
	assert(game.ticks.atomicLoad() == 3 + ecrs.context.entityCount(context) && valueOf!A(context, e) == 17);
	assert(parallel(game, pool, &tick, &tick) && sequential(&tick, twice)(game));
	assert(game.ticks.atomicLoad() == 6 + ecrs.context.entityCount(context) && valueOf!A(context, e) == 19);
}

unittest {
	// untilStable reruns until the watched components, or all of them, hold still, and stops at a failure; bound, it nests in other schedules.
	alias A = Counter!1, B = Counter!2;
	static bool raiseAToFive(ref ecrs.context.Context context, ecrs.registry.EntityId e) @nogc nothrow {
		if (ecrs.context.hasComponent!A(context, e) && ecrs.context.getComponent!A(cast(const) context, e).value < 5)
			++ecrs.context.getForWriting!A(context, e).value;
		return true;
	}
	static size_t calls;
	static bool counted(ref ecrs.context.Context context) @nogc nothrow {
		++calls;
		return sequential!raiseAToFive(context);
	}
	static bool touchB(ref ecrs.context.Context context) @nogc nothrow {
		++calls;
		++ecrs.context.getForWriting!B(context, 1).value;
		return true;
	}
	static bool fails(ref ecrs.context.Context) @nogc nothrow { ++calls; return false; }

	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);
	immutable e = ecrs.context.addEntity(context);
	assert(e == 1);
	ecrs.context.addComponent!A(context, e).value = 0;
	ecrs.context.addComponent!B(context, e).value = 0;

	calls = 0;
	assert(untilStable(context, &counted));
	assert(valueOf!A(context, e) == 5 && calls == 6);

	// Watching A alone, a schedule that only touches B settles after one run; watching everything, it never would.
	immutable size_t[1] watchA = [ecrs.registry.componentId!A()];
	calls = 0;
	assert(untilStable(context, &touchB, watchA[]));
	assert(calls == 1);

	calls = 0;
	assert(!untilStable(context, &fails));
	assert(calls == 1);

	ecrs.context.getForWriting!A(context, e).value = 2;
	auto pool = makePool(4);
	scope(exit) bc.threadpool.free(pool);
	auto settle = untilStable(parallel!raiseAToFive(pool), watchA[]);
	auto copy = settle;
	assert(sequential(copy, &touchB)(context));
	assert(valueOf!A(context, e) == 5);

	static struct Wrapper { ecrs.context.Context context; size_t runs; }
	auto wrapper = Wrapper(context);
	assert(untilStable(&counted)(wrapper));
	static bool run(ref Wrapper w) @nogc nothrow { ++w.runs; return true; }
	assert(untilStable(wrapper, &run) && untilStable(&run)(wrapper) && wrapper.runs == 2);
}

unittest {
	// whenChanged reruns on a watched change, absorbs its own writes, retries after failing, and keeps its state when nested.
	alias A = Counter!1, B = Counter!2;
	static size_t calls;
	static bool fail;
	static bool bumpA(ref ecrs.context.Context context) @nogc nothrow {
		++calls;
		++ecrs.context.getForWriting!A(context, 1).value;
		return !fail;
	}

	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);
	assert(ecrs.context.addEntity(context) == 1);
	ecrs.context.addComponent!A(context, 1).value = 0;
	ecrs.context.addComponent!B(context, 1).value = 0;
	immutable size_t[1] watchB = [ecrs.registry.componentId!B()];

	calls = 0;
	size_t seen = neverRan;
	assert(whenChanged(context, &bumpA, seen, watchB[]) && calls == 1);
	assert(whenChanged(context, &bumpA, seen, watchB[]) && calls == 1);
	++ecrs.context.getForWriting!B(context, 1).value;
	assert(whenChanged(context, &bumpA, seen, watchB[]) && calls == 2);

	// Watching everything, its own write to A is absorbed, but a later one is not.
	seen = neverRan;
	assert(whenChanged(context, &bumpA, seen) && whenChanged(context, &bumpA, seen) && calls == 3);
	++ecrs.context.getForWriting!A(context, 1).value;
	assert(whenChanged(context, &bumpA, seen) && calls == 4);

	fail = true;
	++ecrs.context.getForWriting!B(context, 1).value;
	immutable kept = seen;
	assert(!whenChanged(context, &bumpA, seen, watchB[]) && seen == kept && calls == 5);
	fail = false;
	assert(whenChanged(context, &bumpA, seen, watchB[]) && calls == 6);

	// Nested, it remembers its last run, and a copy keeps its own.
	auto schedule = sequential(whenChanged(&bumpA, watchB[]), untilStable(whenChanged(&bumpA, watchB[])));
	assert(schedule(context) && calls == 8);
	assert(schedule(context) && calls == 8);
	auto copy = schedule;
	++ecrs.context.getForWriting!B(context, 1).value;
	assert(copy(context) && calls == 10);
	assert(schedule(context) && calls == 12);
	assert(parallel(context, null, schedule, copy) && calls == 12);

	static struct Wrapper { ecrs.context.Context context; size_t runs; }
	auto wrapper = Wrapper(context);
	auto onChange = whenChanged(&bumpA, watchB[]);
	assert(onChange(wrapper) && onChange(wrapper) && calls == 13);
	static bool run(ref Wrapper w) @nogc nothrow { ++w.runs; return true; }
	seen = neverRan;
	auto onOwnerChange = whenChanged(&run, watchB[]);
	assert(whenChanged(wrapper, &run, seen, watchB[]) && whenChanged(wrapper, &run, seen, watchB[]));
	assert(onOwnerChange(wrapper) && onOwnerChange(wrapper) && wrapper.runs == 2);
}

unittest {
	// Both parallel combinators mark the context while they run, even inline, so structural changes inside fail an assert.
	import core.atomic : atomicOp, atomicStore;
	static shared int sawParallel;

	static bool observe(ref ecrs.context.Context context, ecrs.registry.EntityId) @nogc nothrow {
		if (ecrs.context.inParallel(context)) sawParallel.atomicOp!"+="(1);
		return true;
	}
	static bool observeWhole(ref ecrs.context.Context context) @nogc nothrow {
		if (ecrs.context.inParallel(context)) sawParallel.atomicOp!"+="(1);
		return true;
	}

	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);
	foreach (i; 0 .. 4) assert(ecrs.context.addEntity(context) != ecrs.registry.invalidEntity);

	foreach (workers; [1, 4]) {
		auto pool = makePool(workers);
		scope(exit) bc.threadpool.free(pool);

		sawParallel.atomicStore(0);
		assert(parallel!observe(context, pool));
		assert(sawParallel == ecrs.context.entityCount(context));
		assert(!ecrs.context.inParallel(context));

		sawParallel.atomicStore(0);
		assert(parallel(context, pool, &observeWhole));
		assert(parallel(context, pool, &observeWhole, &observeWhole));
		assert(sawParallel == 3);
		assert(!ecrs.context.inParallel(context));
	}

	assert(sequential!observe(context));
	assert(!ecrs.context.inParallel(context));

	// Slice passes mark the context too; inside concurrentWrites their jobs may add components to entities they own, and the phase closes even on failure.
	alias Mark = Counter!4, Other = Counter!5;
	static bool observeItem(C)(ref ecrs.context.Context context, ref ecrs.registry.EntityId e) @nogc nothrow {
		if (ecrs.context.inParallel(context)) sawParallel.atomicOp!"+="(1);
		return ecrs.context.addComponent!C(context, e) !is null;
	}
	ecrs.registry.EntityId[4] owned = [1, 2, 3, 4];
	auto pool = makePool(4);
	scope(exit) bc.threadpool.free(pool);
	sawParallel.atomicStore(0);
	assert(ecrs.context.reserveConcurrentAdds!Mark(context, owned.length));
	assert(concurrentWrites(context, parallel!(observeItem!Mark)(pool, owned[])));
	assert(sawParallel == owned.length && !ecrs.context.inParallel(context));
	foreach (o; owned) assert(ecrs.context.hasComponent!Mark(context, o));

	assert(ecrs.context.reserveConcurrentAdds!Other(context, owned.length));
	assert(sequential(concurrentWrites(parallel!(observeItem!Other)(pool, owned[])))(context));
	foreach (o; owned) assert(ecrs.context.hasComponent!Other(context, o));

	static bool fails(ref ecrs.context.Context) @nogc nothrow { return false; }
	assert(!concurrentWrites(context, &fails));
	assert(ecrs.context.addEntity(context) != ecrs.registry.invalidEntity); // a structural change, so the phase is closed

	// Over an owner, which holds the context itself so structural changes reach it, the jobs receive the owner.
	alias Owned = Counter!6;
	static struct Owner { ecrs.context.Context context; shared size_t adds; }
	static bool addOwned(ref Owner owner, ref ecrs.registry.EntityId e) @nogc nothrow {
		owner.adds.atomicOp!"+="(1);
		return ecrs.context.addComponent!Owned(owner.context, e) !is null;
	}
	Owner owner;
	owner.context = ecrs.context.create();
	scope(exit) ecrs.context.free(owner.context);
	foreach (i; 0 .. owned.length) assert(ecrs.context.addEntity(owner.context) != ecrs.registry.invalidEntity);
	assert(ecrs.context.reserveConcurrentAdds!Owned(owner.context, owned.length));
	assert(concurrentWrites(parallel!addOwned(pool, owned[]))(owner));
	assert(owner.adds == owned.length && !ecrs.context.inParallel(owner.context));
	foreach (o; owned) assert(ecrs.context.hasComponent!Owned(owner.context, o));

	// An owner may hold its context by pointer, and a job holding the store to itself may change its structure inside a parallel pass.
	static struct Engine { ecrs.context.Context* store; alias context = store; }
	static bool spawn(ref Engine engine, ref ecrs.registry.EntityId e) @nogc nothrow {
		ecrs.context.beginExclusive(*engine.store);
		scope(exit) ecrs.context.endExclusive(*engine.store);
		e = ecrs.context.addEntity(*engine.store);
		return e != ecrs.registry.invalidEntity && ecrs.context.addComponent!Owned(*engine.store, e) !is null;
	}
	auto engine = Engine(&owner.context);
	ecrs.registry.EntityId[1] spawned;
	assert(parallel!spawn(engine, pool, spawned[]) && ecrs.context.hasComponent!Owned(owner.context, spawned[0]));
	assert(sequential(engine, parallel!spawn(null, spawned[])) && !ecrs.context.inExclusive(owner.context));
}
