/// Fixed- or dynamic-arity relation components (`Relation!N`), plus the
/// `Term` type used when a relation's slots may hold unbound logic
/// variables instead of concrete entities. Ported from relation.hpp.
module ecrs.relation;

import fp.dynarray;

import ecrs.storage : EntityId, invalidEntity, EntityComponentIndices;

@nogc nothrow:


/// Marker base for relation components (kept for symmetry with the C++
/// version's `relation_base`; D doesn't need it for dispatch, since
/// `hasSwapEntities`/component registration work structurally).
struct RelationBase {}

/// One relation slot: either a concrete entity, or (when the relation type
/// allows it) an unbound logic variable identified by `varId`.
struct Term {
	bool isVar = true;
	union {
		EntityId constant;
		size_t varId;
	}

	this(EntityId e) @nogc nothrow { isVar = false; constant = e; }
}

enum size_t dynamicExtent = size_t.max;

/// A component listing `N` related entities (or terms, if `canBeTerm`).
/// `N == dynamicExtent` switches `related` from a fixed-size array to a
/// growable dynarray.
struct Relation(size_t N = dynamicExtent, bool canBeTerm = false) {
	alias MaybeTerm = Ternary!canBeTerm;
	enum bool canBeTermValue = canBeTerm;
	enum bool isDynamic = (N == dynamicExtent);

	static if (isDynamic)
		MaybeTerm* related = null;
	else
		MaybeTerm[N] related;

	static void swapEntities(ref Relation self, ref EntityComponentIndices entityComponentIndices, EntityId a, EntityId b) @nogc nothrow {
		static if (isDynamic) {
			foreach (ref e; slice(self.related))
				swapTermEntity(e, a, b);
		} else {
			foreach (ref e; self.related)
				swapTermEntity(e, a, b);
		}
	}

	static if (isDynamic)
	/// Releases `related`'s backing dynarray. `ComponentStorage` is flat,
	/// relocatable bytes with no destructor support (see storage.d), so
	/// without this hook a dynamic relation's allocation would outlive
	/// `removeComponent`/`removeEntity`/`Context.free()` unfreed.
	static void finalize(ref Relation self) @nogc nothrow {
		if (self.related !is null) fp.dynarray.free(self.related);
	}
}

private template Ternary(bool canBeTerm) {
	static if (canBeTerm) alias Ternary = Term;
	else alias Ternary = EntityId;
}

private void swapTermEntity(ref EntityId e, EntityId a, EntityId b) @nogc nothrow {
	if (e == a) e = b;
	else if (e == b) e = a;
}
private void swapTermEntity(ref Term t, EntityId a, EntityId b) @nogc nothrow {
	if (t.isVar) return;
	if (t.constant == a) t.constant = b;
	else if (t.constant == b) t.constant = a;
}


unittest {
	import ecrs.storage : hasSwapEntities;

	struct Parent { }
	alias ParentRelation = Relation!3;
	static assert(hasSwapEntities!ParentRelation);

	ParentRelation rel;
	rel.related = [1, 2, 3];
	EntityComponentIndices dummy = null;
	ParentRelation.swapEntities(rel, dummy, 1, 5);
	assert(rel.related == [5, 2, 3]);
}

unittest {
	alias DynRelation = Relation!(dynamicExtent, false);
	static assert(is(DynRelation.MaybeTerm == EntityId));

	DynRelation rel;
	fp.dynarray.pushBack(rel.related, EntityId(1));
	fp.dynarray.pushBack(rel.related, EntityId(2));
	scope(exit) fp.dynarray.free(rel.related);

	EntityComponentIndices dummy = null;
	DynRelation.swapEntities(rel, dummy, 2, 9);
	assert(rel.related[0] == 1);
	assert(rel.related[1] == 9);
}

unittest {
	// A dynamic relation opts into the storage.d `hasFinalize` contract so
	// `Context.removeComponent`/`removeEntity`/`free` can release `related`
	// instead of leaking it (ComponentStorage is flat POD bytes with no
	// destructor support - see the note on it in storage.d). A fixed-size
	// relation owns no heap memory, so it doesn't need (and doesn't get) one.
	import ecrs.storage : hasFinalize;

	alias DynRelation = Relation!(dynamicExtent, false);
	alias FixedRelation = Relation!3;
	static assert(hasFinalize!DynRelation);
	static assert(!hasFinalize!FixedRelation);

	DynRelation rel;
	fp.dynarray.pushBack(rel.related, EntityId(1));
	assert(rel.related !is null);

	DynRelation.finalize(rel);
	assert(rel.related is null);

	DynRelation.finalize(rel); // finalizing an already-null relation is a no-op
}

unittest {
	alias TypedRelation = Relation!(1, true); // e.g. `type_of` - first slot may be an unbound var
	TypedRelation rel;
	rel.related[0] = Term(EntityId(7));
	assert(!rel.related[0].isVar);
	assert(rel.related[0].constant == 7);
}

unittest {
	// swapEntities() on a canBeTerm relation: unbound vars are left alone, and
	// constants matching either `a` or `b` are swapped.
	alias TermRelation = Relation!(3, true);
	TermRelation rel;
	rel.related[0] = Term(); // isVar == true -> early-return branch
	rel.related[1] = Term(EntityId(1)); // constant == a
	rel.related[2] = Term(EntityId(2)); // constant == b

	EntityComponentIndices dummy = null;
	TermRelation.swapEntities(rel, dummy, EntityId(1), EntityId(2));

	assert(rel.related[0].isVar);
	assert(!rel.related[1].isVar && rel.related[1].constant == 2);
	assert(!rel.related[2].isVar && rel.related[2].constant == 1);
}
