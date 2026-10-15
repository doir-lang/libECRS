/// Fixed- or dynamic-arity relation components, `Relation!n`, and the `Term` a relation's slots hold when they may be unbound logic variables rather than entities.
module ecrs.relation;

static import ecrs.registry;
static import fp.dynarray;
static import fp.lifecycle;

@nogc nothrow:


/// One relation slot: a concrete entity, or, when the relation allows it, an unbound logic variable named by `varId`.
struct Term {
	bool isVar = true; /// Whether this is a variable rather than an entity.
	union {
		ecrs.registry.EntityId constant; /// The entity, when `isVar` is false.
		size_t varId; /// The variable, when `isVar` is true.
	}

	/// A term naming entity `e`.
	this(ecrs.registry.EntityId e) @nogc nothrow { isVar = false; constant = e; }
}

/// The `n` of a `Relation` whose slots are a growable dynarray rather than a fixed array.
enum size_t dynamicExtent = size_t.max;

private template Ternary(bool canBeTerm) {
	static if (canBeTerm) alias Ternary = Term;
	else alias Ternary = ecrs.registry.EntityId;
}

// An id the remap does not cover keeps its own, so `invalidEntity` maps to itself while index 0 stays fixed.
private void remapTermEntity(ref ecrs.registry.EntityId e, const(ecrs.registry.EntityId)[] remap) {
	if (e < remap.length) e = remap[e];
}
private void remapTermEntity(ref Term t, const(ecrs.registry.EntityId)[] remap) {
	if (t.isVar) return;
	if (t.constant < remap.length) t.constant = remap[t.constant];
}

/// A component listing `n` related entities, or terms if `canBeTerm`. With `n` as `dynamicExtent`, `related` is a growable dynarray the component owns, and its lifetime follows `fp.lifecycle`: removing the component frees the dynarray, and copying it with `fp.lifecycle.copyInto` copies the dynarray.
///
/// Examples:
/// ---
/// Relation!2 pair;
/// pair.related = [1, 2];
/// immutable ecrs.registry.EntityId[3] remap = [0, 2, 1];
/// Relation!2.remapEntities(pair, remap[]);
/// assert(pair.related == [2, 1]);
///
/// Relation!dynamicExtent many;
/// assert(fp.dynarray.pushBack(many.related, 1));
/// many.finalize();
/// assert(many.related is null);
/// ---
struct Relation(size_t n = dynamicExtent, bool canBeTerm = false) {
	alias MaybeTerm = Ternary!canBeTerm; /// What each slot holds.
	enum bool canBeTermValue = canBeTerm; /// Whether slots may hold variables.
	enum bool isDynamic = n == dynamicExtent; /// Whether `related` is a dynarray.

	static if (isDynamic)
		MaybeTerm* related = null; /// The related entities or terms.
	else
		MaybeTerm[n] related; /// Ditto

	/// The renumbering hook `ecrs.registry.hasRemapEntities` detects: relabels every slot, `remap[old]` being the id `old` becomes.
	///
	/// Examples:
	/// ---
	/// Relation!1 next;
	/// next.related[0] = 1;
	/// immutable ecrs.registry.EntityId[2] remap = [0, 3];
	/// Relation!1.remapEntities(next, remap[]);
	/// assert(next.related[0] == 3);
	/// ---
	static void remapEntities(ref Relation self, const(ecrs.registry.EntityId)[] remap) @nogc nothrow {
		static if (isDynamic) auto slots = fp.dynarray.slice(self.related);
		else auto slots = self.related[];
		foreach (ref e; slots)
			remapTermEntity(e, remap);
	}

	static if (isDynamic) {
		/// Ends the lifetime, as `fp.lifecycle` defines it, by freeing `related`. Safe on an empty relation.
		///
		/// Examples:
		/// ---
		/// Relation!dynamicExtent many;
		/// assert(fp.dynarray.pushBack(many.related, 1));
		/// many.finalize();
		/// assert(many.related is null);
		/// many.finalize();
		/// ---
		void finalize() @nogc nothrow {
			fp.dynarray.free(related);
			related = null;
		}

		/// Copies into the empty `dest`, as `fp.lifecycle` defines it, giving it a dynarray of its own. If that cannot be allocated, `dest` is left empty.
		///
		/// Examples:
		/// ---
		/// Relation!dynamicExtent original, copy;
		/// assert(fp.dynarray.pushBack(original.related, 1));
		/// original.copyTo(copy);
		/// assert(copy.related !is original.related && copy.related[0] == 1);
		/// copy.finalize();
		/// original.finalize();
		/// ---
		void copyTo(ref Relation dest) @nogc nothrow {
			dest.related = fp.dynarray.clone(related);
		}
	}
}


unittest {
	// Remapping fixed and dynamic relations of entities.
	alias Fixed = Relation!3;
	static assert(ecrs.registry.hasRemapEntities!Fixed);
	Fixed fixed;
	fixed.related = [1, 2, 3];
	immutable ecrs.registry.EntityId[6] remap = [0, 5, 2, 3, 4, 1];
	Fixed.remapEntities(fixed, remap[]);
	assert(fixed.related == [5, 2, 3]);

	alias Dynamic = Relation!(dynamicExtent, false);
	static assert(is(Dynamic.MaybeTerm == ecrs.registry.EntityId));
	Dynamic dynamic;
	assert(fp.dynarray.pushBack(dynamic.related, ecrs.registry.EntityId(1)));
	assert(fp.dynarray.pushBack(dynamic.related, ecrs.registry.EntityId(2)));
	scope(exit) dynamic.finalize();
	immutable ecrs.registry.EntityId[3] shortRemap = [0, 1, 9];
	Dynamic.remapEntities(dynamic, shortRemap[]);
	assert(dynamic.related[0] == 1);
	assert(dynamic.related[1] == 9);
}

unittest {
	// Remapping terms relabels every entity in one pass, leaves variables alone, and keeps an id past the remap's end.
	alias TermRelation = Relation!(4, true);
	static assert(ecrs.registry.hasRemapEntities!TermRelation);

	TermRelation rel;
	rel.related[0] = Term();
	rel.related[1] = Term(ecrs.registry.EntityId(1));
	rel.related[2] = Term(ecrs.registry.EntityId(3));
	rel.related[3] = Term(ecrs.registry.EntityId(9));
	assert(!rel.related[1].isVar && rel.related[1].constant == 1);

	immutable ecrs.registry.EntityId[4] remap = [0, 3, 1, 2];
	TermRelation.remapEntities(rel, remap[]);
	assert(rel.related[0].isVar);
	assert(rel.related[1].constant == 3);
	assert(rel.related[2].constant == 2);
	assert(rel.related[3].constant == 9);
}

unittest {
	// Only a dynamic relation owns memory, so only it declares a lifetime; its copies own their own dynarrays.
	alias Dynamic = Relation!(dynamicExtent, false);
	static assert(!fp.lifecycle.isBitMoveable!Dynamic);
	static assert(fp.lifecycle.isBitMoveable!(Relation!3));

	Dynamic original, copy;
	assert(fp.dynarray.pushBack(original.related, ecrs.registry.EntityId(1)));
	fp.lifecycle.copyInto(copy, original);
	assert(copy.related !is original.related && copy.related[0] == 1);

	copy.finalize();
	assert(copy.related is null);
	copy.finalize();
	original.finalize();

	// A container of relations frees each one's dynarray with itself.
	Dynamic* list = null;
	Dynamic element;
	assert(fp.dynarray.pushBack(element.related, ecrs.registry.EntityId(2)));
	assert(fp.dynarray.pushBack(list, element)); // hands the dynarray over, so `element` must not end it
	assert(list[0].related[0] == 2);
	fp.dynarray.free(list);
}
