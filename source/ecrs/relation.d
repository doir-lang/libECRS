/// Fixed- or dynamic-arity relation components, `Relation!n`, and the `Term` a relation's slots hold when they may be unbound logic variables rather than entities.
module ecrs.relation;

import core.stdc.string : memcpy;

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

/// A component listing `n` related entities, or terms if `canBeTerm`. With `n` as `dynamicExtent`, `related` is a growable dynarray the component owns, and its lifetime follows `fp.lifecycle`: removing the component frees the dynarray, and copying it with `fp.lifecycle.copyInto` copies the dynarray. It also encodes itself, so `ecrs.serialization` saves it despite the pointer.
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

		/// The encoding hooks `ecrs.registry.hasSerialize` detects: the slot count, then the slots' bytes. Returns false if allocation fails.
		///
		/// Examples:
		/// ---
		/// Relation!dynamicExtent many, copy;
		/// assert(fp.dynarray.pushBack(many.related, ecrs.registry.EntityId(7)));
		/// ubyte* bytes = null;
		/// assert(Relation!dynamicExtent.serialize(many, bytes));
		/// const(ubyte)[] data = fp.dynarray.slice(bytes);
		/// assert(Relation!dynamicExtent.deserialize(copy, data) && data.length == 0);
		/// assert(copy.related[0] == 7);
		/// fp.dynarray.free(bytes);
		/// copy.finalize();
		/// many.finalize();
		/// ---
		static bool serialize(const ref Relation self, ref ubyte* out_) @trusted {
			immutable ulong count = fp.dynarray.length(self.related);
			return fp.dynarray.concatenate(out_, (cast(const(ubyte)*) &count)[0 .. count.sizeof])
				&& fp.dynarray.concatenate(out_, (cast(const(ubyte)*) self.related)[0 .. cast(size_t) count * MaybeTerm.sizeof]);
		}

		/// Ditto, reading what `serialize` wrote into the empty `self` and advancing `data` past it. Returns false if `data` is too short or allocation fails, leaving `self` empty and `data` as it was.
		///
		/// Examples:
		/// ---
		/// Relation!dynamicExtent many;
		/// static immutable ubyte[2] bytes = [1, 0];
		/// const(ubyte)[] truncated = bytes[];
		/// assert(!Relation!dynamicExtent.deserialize(many, truncated));
		/// assert(many.related is null && truncated.length == 2);
		/// ---
		static bool deserialize(ref Relation self, ref const(ubyte)[] data) @trusted {
			ulong count;
			if (data.length < count.sizeof) return false;
			memcpy(&count, data.ptr, count.sizeof);
			if (count > (data.length - count.sizeof) / MaybeTerm.sizeof) return false;
			immutable bytes = cast(size_t) count * MaybeTerm.sizeof;
			if (count > 0) {
				if (fp.dynarray.growToSize(self.related, cast(size_t) count) is null) return false;
				memcpy(self.related, data.ptr + count.sizeof, bytes);
			}
			data = data[count.sizeof + bytes .. $];
			return true;
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

	// Encoding round-trips terms too, and an empty relation stays without a dynarray.
	alias Terms = Relation!(dynamicExtent, true);
	static assert(ecrs.registry.hasSerialize!Terms && !ecrs.registry.hasSerialize!(Relation!3));
	Terms terms, decoded, blank, decodedBlank;
	assert(fp.dynarray.pushBack(terms.related, Term()));
	assert(fp.dynarray.pushBack(terms.related, Term(ecrs.registry.EntityId(4))));
	scope(exit) terms.finalize();
	scope(exit) decoded.finalize();
	ubyte* bytes = null;
	scope(exit) fp.dynarray.free(bytes);
	assert(Terms.serialize(terms, bytes) && Terms.serialize(blank, bytes));
	const(ubyte)[] data = fp.dynarray.slice(bytes);
	assert(Terms.deserialize(decoded, data) && Terms.deserialize(decodedBlank, data) && data.length == 0);
	assert(fp.dynarray.length(decoded.related) == 2 && decoded.related[0].isVar && decoded.related[1].constant == 4);
	assert(decodedBlank.related is null);
	data = fp.dynarray.slice(bytes)[0 .. ulong.sizeof + Term.sizeof];
	assert(!Terms.deserialize(decodedBlank, data) && decodedBlank.related is null);

	// A container of relations frees each one's dynarray with itself.
	Dynamic* list = null;
	Dynamic element;
	assert(fp.dynarray.pushBack(element.related, ecrs.registry.EntityId(2)));
	assert(fp.dynarray.pushBack(list, element)); // hands the dynarray over, so `element` must not end it
	assert(list[0].related[0] == 2);
	fp.dynarray.free(list);
}
