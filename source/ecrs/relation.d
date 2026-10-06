/// Fixed- or dynamic-arity relation components (`Relation!N`), plus the
/// `Term` type used when a relation's slots may hold unbound logic
/// variables instead of concrete entities. Ported from relation.hpp.
module ecrs.relation;

import fp.dynarray;

import ecrs.storage : EntityId, invalidEntity;

@nogc nothrow:


/// Marker base for relation components (kept for symmetry with the C++
/// version's `relation_base`; D doesn't need it for dispatch, since the
/// registry detects the hooks below structurally).
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

	/// The renumbering hook (`ecrs.registry.hasRemapEntities`): relabels every
	/// slot, `remap[old]` being the id `old` becomes.
	static void remapEntities(ref Relation self, const(EntityId)[] remap) @nogc nothrow {
		static if (isDynamic) auto slots = slice(self.related);
		else auto slots = self.related[];
		foreach (ref e; slots)
			remapTermEntity(e, remap);
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

// An id the permutation does not cover keeps its own: `invalidEntity` maps to
// itself as long as the caller's permutation holds index 0 fixed.
private void remapTermEntity(ref EntityId e, const(EntityId)[] remap) {
	if (e < remap.length) e = remap[e];
}
private void remapTermEntity(ref Term t, const(EntityId)[] remap) {
	if (t.isVar) return;
	if (t.constant < remap.length) t.constant = remap[t.constant];
}


unittest {
	import ecrs.registry : hasRemapEntities;

	alias ParentRelation = Relation!3;
	static assert(hasRemapEntities!ParentRelation);

	ParentRelation rel;
	rel.related = [1, 2, 3];
	immutable EntityId[6] remap = [0, 5, 2, 3, 4, 1];
	ParentRelation.remapEntities(rel, remap[]);
	assert(rel.related == [5, 2, 3]);
}

unittest {
	alias DynRelation = Relation!(dynamicExtent, false);
	static assert(is(DynRelation.MaybeTerm == EntityId));

	DynRelation rel;
	fp.dynarray.pushBack(rel.related, EntityId(1));
	fp.dynarray.pushBack(rel.related, EntityId(2));
	scope(exit) fp.dynarray.free(rel.related);

	immutable EntityId[3] remap = [0, 1, 9];
	DynRelation.remapEntities(rel, remap[]);
	assert(rel.related[0] == 1);
	assert(rel.related[1] == 9);
}

unittest {
	// A dynamic relation opts into the registry's `hasFinalize` contract so
	// `Context.removeComponent`/`removeEntity`/`free` can release `related`
	// instead of leaking it (ComponentStorage is flat POD bytes with no
	// destructor support - see the note on it in storage.d). A fixed-size
	// relation owns no heap memory, so it doesn't need (and doesn't get) one.
	import ecrs.registry : hasFinalize;

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
	// remapEntities(): every slot relabelled in one pass, vars left alone, and an
	// id past the end of the table (here 9) left as it was.
	import ecrs.registry : hasRemapEntities;

	alias TermRelation = Relation!(4, true);
	static assert(hasRemapEntities!TermRelation);

	TermRelation rel;
	rel.related[0] = Term();
	rel.related[1] = Term(EntityId(1));
	rel.related[2] = Term(EntityId(3));
	rel.related[3] = Term(EntityId(9));

	immutable EntityId[4] remap = [0, 3, 1, 2];
	TermRelation.remapEntities(rel, remap[]);

	assert(rel.related[0].isVar);
	assert(rel.related[1].constant == 3);
	assert(rel.related[2].constant == 2);
	assert(rel.related[3].constant == 9);
}
