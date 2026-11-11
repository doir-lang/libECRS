/// Trees of entities as views for `fp.tree`: each entity lists its children in a component mixing in a dynamic `Relates`, and may name its parent in one mixing in `Relates!1`.
/// The views only read, so building and editing the tree stays with whoever owns the components.
///
/// Examples:
/// ---
/// static import ecrs.context;
/// static import ecrs.relation;
/// static import fp.dynarray;
/// static import fp.tree;
/// static struct Kids { mixin ecrs.relation.Relates; }
/// auto store = ecrs.context.create();
/// scope(exit) ecrs.context.free(store);
/// immutable root = ecrs.context.addEntity(store), leaf = ecrs.context.addEntity(store);
/// assert(fp.dynarray.pushBack(ecrs.context.addComponent!Kids(store, root).related, leaf));
/// assert(fp.tree.count(View!(Kids, 8)(&store), root).get == 2);
/// ---
module ecrs.tree;

static import ecrs.context;
static import ecrs.registry;
static import fp.dynarray;
version(unittest) {
	static import ecrs.relation;
	static import fp.algorithms;
	static import fp.tree;
}

/// A view over `store`'s entities: an entity's children are the `related` of its `Children` component, none if it has none, and a walk goes at most `depth` below its root.
/// With `Parent`, an entity's parent is its `Parent` component's one slot, `noParent` if it has none.
///
/// Examples:
/// ---
/// static import ecrs.context;
/// static import ecrs.relation;
/// static struct Up { mixin ecrs.relation.Relates!"parent"; }
/// static struct Down { mixin ecrs.relation.Relates; }
/// auto store = ecrs.context.create();
/// scope(exit) ecrs.context.free(store);
/// immutable e = ecrs.context.addEntity(store);
/// auto view = View!(Down, 4, Up)(&store);
/// assert(view.children(e).length == 0 && view.parent(e) == view.noParent);
/// ---
struct View(Children, size_t depth, Parent = void) {
	static assert(Children.isDynamic, "ecrs.tree.View: children listed in a fixed relation");
	static assert(is(Parent == void) || Parent.init.related.length == 1, "ecrs.tree.View: a parent component without exactly one slot");

	const(ecrs.context.Context)* store; /// The store the entities are in.

	alias Index = ecrs.registry.EntityId; /// A node is an entity.
	enum size_t maxDepth = depth; /// The deepest a walk goes.

	/// Entity `e`'s children, in order.
	///
	/// Examples:
	/// ---
	/// static import ecrs.context;
	/// static import ecrs.relation;
	/// static struct Lists { mixin ecrs.relation.Relates; }
	/// auto store = ecrs.context.create();
	/// scope(exit) ecrs.context.free(store);
	/// assert(View!(Lists, 4)(&store).children(ecrs.context.addEntity(store)).length == 0);
	/// ---
	const(Index)[] children(Index e) const {
		assert(store !is null, "ecrs.tree.View: a view of no store");
		const list = ecrs.context.findComponent!Children(*store, e);
		return list is null ? null : fp.dynarray.slice(list.related);
	}

	static if (!is(Parent == void)) {
		enum Index noParent = ecrs.registry.invalidEntity; /// What `parent` gives for an entity with no parent.

		/// Entity `e`'s parent, or `noParent`.
		///
		/// Examples:
		/// ---
		/// static import ecrs.context;
		/// static import ecrs.relation;
		/// static struct Owner { mixin ecrs.relation.Relates!"parent"; }
		/// static struct Owned { mixin ecrs.relation.Relates; }
		/// auto store = ecrs.context.create();
		/// scope(exit) ecrs.context.free(store);
		/// immutable a = ecrs.context.addEntity(store), b = ecrs.context.addEntity(store);
		/// assert(ecrs.context.setComponent!Owner(store, b, Owner([a])));
		/// assert(View!(Owned, 4, Owner)(&store).parent(b) == a);
		/// ---
		Index parent(Index e) const {
			assert(store !is null, "ecrs.tree.View: a view of no store");
			const up = ecrs.context.findComponent!Parent(*store, e);
			return up is null ? noParent : up.related[0];
		}
	}
}


version(unittest) {
	private struct TreeTestChildren { mixin ecrs.relation.Relates; }
	private struct TreeTestParent { mixin ecrs.relation.Relates!"parent"; }
}

@nogc nothrow:

unittest {
	// Random trees built as a parent table, then as entities, walked through the view and checked against the table.
	enum size_t deepest = 6;
	alias Tree = View!(TreeTestChildren, deepest, TreeTestParent);
	foreach (seed; 0 .. 100) {
		auto random = fp.algorithms.createRandom(seed);
		auto store = ecrs.context.create();
		scope(exit) ecrs.context.free(store);
		immutable size = 1 + fp.algorithms.randomBelow(random, 40);
		ecrs.registry.EntityId[40] entities;
		size_t[40] depths;
		auto view = Tree(&store);
		foreach (i; 0 .. size) {
			entities[i] = ecrs.context.addEntity(store);
			assert(entities[i] != ecrs.registry.invalidEntity);
			if (i == 0) continue;
			size_t parent = fp.algorithms.randomBelow(random, i);
			while (depths[parent] >= deepest) --parent;
			depths[i] = depths[parent] + 1;
			assert(ecrs.context.setComponent!TreeTestParent(store, entities[i], TreeTestParent([entities[parent]])));
			auto list = ecrs.context.ensureComponent!TreeTestChildren(store, entities[parent]);
			assert(list !is null && fp.dynarray.pushBack(list.related, entities[i]));
		}
		assert(fp.tree.validate(view, entities[0]) && fp.tree.count(view, entities[0]).get == size);
		foreach (i; 0 .. size) {
			assert(fp.tree.depthOf(view, entities[i]) == depths[i]);
			assert(i == 0 || fp.tree.isAncestor(view, entities[0], entities[i]));
		}
		size_t visited = 0;
		foreach (e; fp.tree.nodes!(fp.tree.Order.postorder)(view, entities[0])) {
			if (e == entities[0]) assert(visited == size - 1);
			++visited;
		}
		assert(visited == size);

		if (size > 1) {
			immutable moved = entities[1 + fp.algorithms.randomBelow(random, size - 1)];
			ecrs.context.getForWriting!TreeTestParent(store, moved).related[0] = moved;
			assert(!fp.tree.validate(view, entities[0]));
		}
	}
}
