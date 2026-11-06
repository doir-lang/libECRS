/// Fixed- or dynamic-arity relation components, `Relation!n`, the `Relates` mixin that makes any struct one, and the `Term` a relation's slots hold when they may be unbound logic variables rather than entities.
module ecrs.relation;

static import ecrs.registry;
static import fp.algorithms;
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
enum size_t dynamicArity = size_t.max;

/// What a relation's slots hold: `Term` if `canBeTerm`, otherwise `ecrs.registry.EntityId`.
///
/// Examples:
/// ---
/// static assert(is(Slot!true == Term) && is(Slot!false == ecrs.registry.EntityId));
/// ---
template Slot(bool canBeTerm) {
	static if (canBeTerm) alias Slot = Term;
	else alias Slot = ecrs.registry.EntityId;
}

// --- the fields besides a relation's own ------------------------------------

// Hooks `Relates` or `RelatesEach` declare cover the whole struct, as `fp.lifecycle` reads them; the `*Besides` helpers cover the fields beyond the mixin's `skip`.

/// Whether `a` and `b` agree on every field of `T` but `skip`, each compared through `fp.lifecycle.equal`: what `Relates` and `RelatesEach` compare besides their own field, so a struct mixing one in compares whole. It cannot fail.
///
/// Examples:
/// ---
/// static struct Weighted { mixin Relates!"to"; int weight; }
/// assert(equalBesides!"related"(Weighted([1], 2), Weighted([3], 2)));
/// assert(!equalBesides!"related"(Weighted([1], 2), Weighted([1], 4)));
/// ---
bool equalBesides(string skip, T)(auto ref const T a, auto ref const T b) {
	static foreach (i; 0 .. T.tupleof.length)
		static if (__traits(identifier, T.tupleof[i]) != skip)
			if (!fp.lifecycle.equal(a.tupleof[i], b.tupleof[i])) return false;
	return true;
}

/// `h` chained with the `fp.lifecycle.contentHash` of every field of `T` but `skip`, or `h` itself if there is none, so a relation of ids alone hashes as its slots do. It cannot fail.
///
/// Examples:
/// ---
/// static struct Weighted { mixin Relates!"to"; int weight; }
/// assert(hashBesides!"related"(7, Weighted([1], 2)) == hashBesides!"related"(7, Weighted([3], 2)));
/// assert(hashBesides!"related"(7, Relation!1([1])) == 7);
/// ---
size_t hashBesides(string skip, T)(size_t h, auto ref const T value) {
	static foreach (i; 0 .. T.tupleof.length)
		static if (__traits(identifier, T.tupleof[i]) != skip)
			h = cast(size_t) fp.algorithms.combine(h, fp.lifecycle.contentHash(value.tupleof[i]));
	return h;
}

/// Ends the lifetime of every field of `T` but `skip`, through `fp.lifecycle.endLifetime`.
///
/// Examples:
/// ---
/// static import fp.string;
/// static struct Named { mixin Relates; fp.lifecycle.Owned!char name; }
/// Named n;
/// n.name = fp.lifecycle.Owned!char(fp.string.clone("x"));
/// endLifetimeBesides!"related"(n);
/// assert(n.name.p is null);
/// ---
void endLifetimeBesides(string skip, T)(ref T value) {
	static foreach (i; 0 .. T.tupleof.length)
		static if (__traits(identifier, T.tupleof[i]) != skip)
			fp.lifecycle.endLifetime(value.tupleof[i]);
}

/// Copies every field of `T` but `skip` from `source` into the empty `dest`, through `fp.lifecycle.copyInto`.
///
/// Examples:
/// ---
/// static struct Weighted { mixin Relates; int weight; }
/// Weighted a, b;
/// a.weight = 3;
/// copyBesides!"related"(b, a);
/// assert(b.weight == 3);
/// ---
void copyBesides(string skip, T)(ref T dest, ref T source) {
	static foreach (i; 0 .. T.tupleof.length)
		static if (__traits(identifier, T.tupleof[i]) != skip)
			fp.lifecycle.copyInto(dest.tupleof[i], source.tupleof[i]);
}

/// Relabels the entity ids every field of `T` but `skip` holds, through `remapHeldIds`.
///
/// Examples:
/// ---
/// static struct Pair { mixin Relates; Relation!1 other; }
/// Pair p;
/// p.other.related[0] = 1;
/// immutable ecrs.registry.EntityId[2] remap = [0, 5];
/// remapBesides!"related"(p, remap[]);
/// assert(p.other.related[0] == 5);
/// ---
void remapBesides(string skip, T)(ref T value, const(ecrs.registry.EntityId)[] remap) {
	static foreach (i; 0 .. T.tupleof.length)
		static if (__traits(identifier, T.tupleof[i]) != skip)
			remapHeldIds(value.tupleof[i], remap);
}

/// Whether every field of `T` but `skip` can be encoded: it has encoding hooks of its own, as `ecrs.registry.hasSerialize` detects, or its lifetime is its bytes. A dynamic `Relates` declares its encoding hooks only then.
///
/// Examples:
/// ---
/// static struct Weighted { mixin Relates; int weight; }
/// static struct Named { mixin Relates; fp.lifecycle.Owned!char name; }
/// static assert(encodableBesides!("related", Weighted) && !encodableBesides!("related", Named));
/// static assert(ecrs.registry.hasSerialize!Weighted && !ecrs.registry.hasSerialize!Named);
/// ---
template encodableBesides(string skip, T) {
	enum bool encodableBesides = () {
		bool encodable = true;
		static foreach (i; 0 .. T.tupleof.length)
			static if (__traits(identifier, T.tupleof[i]) != skip)
				encodable = encodable && (ecrs.registry.hasSerialize!(typeof(T.tupleof[i])) || fp.lifecycle.isBitMoveable!(typeof(T.tupleof[i])));
		return encodable;
	}();
}

/// Appends the encoding of every field of `T` but `skip` to `out_`: a field's own encoding hooks if it has them, as `ecrs.registry.hasSerialize` detects, otherwise its bytes, which a field that owns memory without such hooks cannot be. Returns false if allocation fails, leaving `out_` longer by what was written.
///
/// Examples:
/// ---
/// static struct Weighted { mixin Relates; int weight; }
/// Weighted w;
/// w.weight = 9;
/// ubyte* bytes = null;
/// scope(exit) fp.dynarray.free(bytes);
/// assert(serializeBesides!"related"(w, bytes) && fp.dynarray.length(bytes) == int.sizeof);
/// ---
bool serializeBesides(string skip, T)(ref const T value, ref ubyte* out_) @trusted {
	static foreach (i; 0 .. T.tupleof.length)
		static if (__traits(identifier, T.tupleof[i]) != skip) {{
			alias F = typeof(T.tupleof[i]);
			static if (ecrs.registry.hasSerialize!F) {
				if (!F.serialize(value.tupleof[i], out_)) return false;
			} else {
				static assert(fp.lifecycle.isBitMoveable!F, T.stringof ~ "." ~ __traits(identifier, T.tupleof[i]) ~ " owns memory, so give it encoding hooks of its own");
				if (!fp.dynarray.concatenate(out_, (cast(const(ubyte)*) &value.tupleof[i])[0 .. F.sizeof])) return false;
			}
		}}
	return true;
}

/// Ditto, reading what `serializeBesides` wrote into `value`'s fields besides `skip`, which must be empty, and advancing `data` past it. Returns false if `data` is too short or allocation fails, leaving `data` as it was and the fields it read to be ended with `endLifetimeBesides`.
///
/// Examples:
/// ---
/// static struct Weighted { mixin Relates; int weight; }
/// static immutable ubyte[4] bytes = [9, 0, 0, 0];
/// const(ubyte)[] data = bytes[];
/// Weighted w;
/// assert(deserializeBesides!"related"(w, data) && data.length == 0);
/// version(LittleEndian) assert(w.weight == 9);
/// ---
bool deserializeBesides(string skip, T)(ref T value, ref const(ubyte)[] data) @trusted {
	auto rest = data;
	static foreach (i; 0 .. T.tupleof.length)
		static if (__traits(identifier, T.tupleof[i]) != skip) {{
			alias F = typeof(T.tupleof[i]);
			static if (ecrs.registry.hasSerialize!F) {
				if (!F.deserialize(value.tupleof[i], rest)) return false;
			} else {
				if (rest.length < F.sizeof) return false;
				(cast(ubyte*) &value.tupleof[i])[0 .. F.sizeof] = rest[0 .. F.sizeof];
				rest = rest[F.sizeof .. $];
			}
		}}
	data = rest;
	return true;
}


// --- relations ---------------------------------------------------------------

/// The body of a relation listing `n` related entities, or terms if `canBeTerm`: the `related` slots and every hook libECRS and `fp.lifecycle` find by name. Mixing it in as a struct's first member makes that struct a relation component of its own type, so two components of the same arity stay distinct. With `n` as `dynamicArity`, `related` is a growable dynarray the component owns: removing the component frees it, copying it with `fp.lifecycle.copyInto` copies it, and `ecrs.serialization` saves it through the encoding hooks.
///
/// `contentHash` and `equal` read the slots rather than the dynarray pointer, so two relations relating the same entities hash and compare alike. An id the remap does not cover keeps its own, so `invalidEntity` maps to itself.
///
/// A fixed relation may name its slots: each of `names` becomes a `@property` reading and writing its slot of `related`, so `mixin Relates!(1, false, "parent")` reads `self.parent` for `self.related[0]`. The overload `Relates!("file", "level")` names a fixed entity relation of that many slots.
///
/// Examples:
/// ---
/// static struct Children { mixin Relates; }
/// static struct Members { mixin Relates; }
/// static assert(ecrs.registry.componentName!Children != ecrs.registry.componentName!Members);
/// Children a, b;
/// scope(exit) a.finalize();
/// scope(exit) b.finalize();
/// assert(fp.dynarray.pushBack(a.related, 1) && fp.dynarray.pushBack(b.related, 1));
/// assert(Children.equal(a, b) && Children.contentHash(a) == Children.contentHash(b));
///
/// static struct Import { mixin Relates!("file", "level"); }
/// auto i = Import([1, 2]);
/// assert(i.file == 1 && i.level == 2);
/// i.level = 3;
/// assert(i.related[1] == 3);
/// ---
mixin template Relates(size_t n = ecrs.relation.dynamicArity, bool canBeTerm = false, names...) {
	static import core.stdc.string;
	static import ecrs.registry;
	static import ecrs.relation;
	static import fp.dynarray;
	static import fp.algorithms;
	static import fp.lifecycle;

	alias MaybeTerm = ecrs.relation.Slot!canBeTerm; /// What each slot holds.
	enum bool canBeTermValue = canBeTerm; /// Whether slots may hold variables.
	enum bool isDynamic = n == ecrs.relation.dynamicArity; /// Whether `related` is a dynarray.

	static assert(names.length == 0 || names.length == n, "Relates: name every slot of a fixed relation, or none");

	static if (isDynamic)
		MaybeTerm* related = null; /// The related entities or terms.
	else
		MaybeTerm[n] related; /// Ditto

	static foreach (i, name; names)
		mixin("@property ref inout(MaybeTerm) " ~ name ~ "() inout return @nogc nothrow { return related[" ~ i.stringof ~ "]; }");

	/// The slots, as a slice.
	///
	/// Examples:
	/// ---
	/// ecrs.relation.Relation!2 pair;
	/// pair.related = [1, 2];
	/// assert(ecrs.relation.Relation!2.slots(pair) == [1, 2]);
	/// ---
	static inout(MaybeTerm)[] slots(ref inout typeof(this) self) @nogc nothrow {
		static if (isDynamic) return fp.dynarray.slice(self.related);
		else return self.related[];
	}

	/// The renumbering hook `ecrs.registry.hasRemapEntities` detects: relabels every slot, `remap[old]` being the id `old` becomes.
	///
	/// Examples:
	/// ---
	/// ecrs.relation.Relation!1 next;
	/// next.related[0] = 1;
	/// immutable ecrs.registry.EntityId[2] remap = [0, 3];
	/// ecrs.relation.Relation!1.remapEntities(next, remap[]);
	/// assert(next.related[0] == 3);
	/// ---
	static void remapEntities(ref typeof(this) self, const(ecrs.registry.EntityId)[] remap) @nogc nothrow {
		foreach (ref e; slots(self)) {
			static if (canBeTerm) {
				if (!e.isVar && e.constant < remap.length) e.constant = remap[e.constant];
			} else if (e < remap.length) e = remap[e];
		}
		ecrs.relation.remapBesides!"related"(self, remap);
	}

	/// Hashes the slots, a variable by its `varId` and an entity by its id, so equal relations hash alike whatever their storage.
	///
	/// Examples:
	/// ---
	/// ecrs.relation.Relation!1 a, b;
	/// a.related[0] = b.related[0] = 4;
	/// assert(ecrs.relation.Relation!1.contentHash(a) == ecrs.relation.Relation!1.contentHash(b));
	/// ---
	static size_t contentHash(ref const typeof(this) self) @nogc nothrow {
		static if (canBeTerm) {
			ulong h = fp.algorithms.chainStart;
			foreach (ref t; slots(self)) {
				immutable size_t[2] word = [t.isVar, t.isVar ? t.varId : t.constant];
				h = fp.algorithms.combine(h, fp.algorithms.hashBytesFast(word[]));
			}
			return ecrs.relation.hashBesides!"related"(cast(size_t) h, self);
		} else return ecrs.relation.hashBesides!"related"(fp.algorithms.hashBytesFast(slots(self)), self);
	}

	/// Whether `a` and `b` hold the same slots in the same order.
	///
	/// Examples:
	/// ---
	/// ecrs.relation.Relation!1 a, b;
	/// a.related[0] = 4;
	/// assert(!ecrs.relation.Relation!1.equal(a, b));
	/// b.related[0] = 4;
	/// assert(ecrs.relation.Relation!1.equal(a, b));
	/// ---
	static bool equal(ref const typeof(this) a, ref const typeof(this) b) @nogc nothrow {
		auto x = slots(a), y = slots(b);
		if (x.length != y.length) return false;
		foreach (i; 0 .. x.length) {
			static if (canBeTerm) {
				if (x[i].isVar != y[i].isVar) return false;
				if (x[i].isVar ? x[i].varId != y[i].varId : x[i].constant != y[i].constant) return false;
			} else if (x[i] != y[i]) return false;
		}
		return ecrs.relation.equalBesides!"related"(a, b);
	}

	static if (isDynamic) {
		/// Ends the lifetime, as `fp.lifecycle` defines it, by freeing `related`. Safe on an empty relation.
		///
		/// Examples:
		/// ---
		/// ecrs.relation.Relation!(ecrs.relation.dynamicArity) many;
		/// assert(fp.dynarray.pushBack(many.related, 1));
		/// many.finalize();
		/// assert(many.related is null);
		/// many.finalize();
		/// ---
		void finalize() @nogc nothrow {
			fp.dynarray.free(related);
			related = null;
			ecrs.relation.endLifetimeBesides!"related"(this);
		}

		/// Copies into the empty `dest`, as `fp.lifecycle` defines it, giving it a dynarray of its own. If that cannot be allocated, `dest` is left empty.
		///
		/// Examples:
		/// ---
		/// ecrs.relation.Relation!(ecrs.relation.dynamicArity) original, copy;
		/// assert(fp.dynarray.pushBack(original.related, 1));
		/// original.copyTo(copy);
		/// assert(copy.related !is original.related && copy.related[0] == 1);
		/// copy.finalize();
		/// original.finalize();
		/// ---
		void copyTo(ref typeof(this) dest) @nogc nothrow {
			dest.related = fp.dynarray.clone(related);
			ecrs.relation.copyBesides!"related"(dest, this);
		}

		/// The encoding hooks `ecrs.registry.hasSerialize` detects: the slot count, the slots' bytes, then the other fields as `serializeBesides` writes them, declared when `encodableBesides` holds. Returns false if allocation fails.
		///
		/// Examples:
		/// ---
		/// alias Many = ecrs.relation.Relation!(ecrs.relation.dynamicArity);
		/// Many many, copy;
		/// assert(fp.dynarray.pushBack(many.related, ecrs.registry.EntityId(7)));
		/// ubyte* bytes = null;
		/// assert(Many.serialize(many, bytes));
		/// const(ubyte)[] data = fp.dynarray.slice(bytes);
		/// assert(Many.deserialize(copy, data) && data.length == 0);
		/// assert(copy.related[0] == 7);
		/// fp.dynarray.free(bytes);
		/// copy.finalize();
		/// many.finalize();
		/// ---
		static bool serialize()(const ref typeof(this) self, ref ubyte* out_) @trusted @nogc nothrow if (ecrs.relation.encodableBesides!("related", typeof(this))) {
			immutable ulong count = fp.dynarray.length(self.related);
			return fp.dynarray.concatenate(out_, (cast(const(ubyte)*) &count)[0 .. count.sizeof])
				&& fp.dynarray.concatenate(out_, (cast(const(ubyte)*) self.related)[0 .. cast(size_t) count * MaybeTerm.sizeof])
				&& ecrs.relation.serializeBesides!"related"(self, out_);
		}

		/// Ditto, reading what `serialize` wrote into the empty `self` and advancing `data` past it. Returns false if `data` is too short or allocation fails, leaving `self` empty and `data` as it was.
		///
		/// Examples:
		/// ---
		/// alias Many = ecrs.relation.Relation!(ecrs.relation.dynamicArity);
		/// Many many;
		/// static immutable ubyte[2] bytes = [1, 0];
		/// const(ubyte)[] truncated = bytes[];
		/// assert(!Many.deserialize(many, truncated));
		/// assert(many.related is null && truncated.length == 2);
		/// ---
		static bool deserialize()(ref typeof(this) self, ref const(ubyte)[] data) @trusted @nogc nothrow if (ecrs.relation.encodableBesides!("related", typeof(this))) {
			ulong count;
			if (data.length < count.sizeof) return false;
			core.stdc.string.memcpy(&count, data.ptr, count.sizeof);
			if (count > (data.length - count.sizeof) / MaybeTerm.sizeof) return false;
			immutable bytes = cast(size_t) count * MaybeTerm.sizeof;
			if (count > 0) {
				if (fp.dynarray.growToSize(self.related, cast(size_t) count) is null) return false;
				core.stdc.string.memcpy(self.related, data.ptr + count.sizeof, bytes);
			}
			auto rest = data[count.sizeof + bytes .. $];
			if (!ecrs.relation.deserializeBesides!"related"(self, rest)) {
				self.finalize();
				return false;
			}
			data = rest;
			return true;
		}
	}
}

/// A fixed entity relation whose slots are named by `names`, one field per slot; see the general `Relates`.
///
/// Examples:
/// ---
/// static struct Edge { mixin Relates!("from", "to"); }
/// auto e = Edge([4, 5]);
/// assert(e.from == 4 && e.to == 5 && ecrs.registry.shapeFor!Edge == ecrs.registry.RelationShape(2, false));
/// ---
mixin template Relates(names...) if (names.length > 0 && is(typeof(names[0]) : string)) {
	static import ecrs.relation;
	mixin ecrs.relation.Relates!(names.length, false, names);
}

/// A component listing `n` related entities, or terms if `canBeTerm`; see `Relates` for its hooks and lifetime. Mix `Relates` into a struct of your own instead when two components would otherwise share this type.
///
/// Examples:
/// ---
/// Relation!2 pair;
/// pair.related = [1, 2];
/// immutable ecrs.registry.EntityId[3] remap = [0, 2, 1];
/// Relation!2.remapEntities(pair, remap[]);
/// assert(pair.related == [2, 1]);
///
/// Relation!dynamicArity many;
/// assert(fp.dynarray.pushBack(many.related, 1));
/// many.finalize();
/// assert(many.related is null);
/// ---
struct Relation(size_t n = dynamicArity, bool canBeTerm = false) {
	mixin Relates!(n, canBeTerm);
}


/// Relabels every entity id `value` holds, `remap[old]` being the id `old` becomes: through its own `remapEntities` hook if it has one, which covers the whole value as a `Relates` does, otherwise through the hooks of each of its fields and static array elements, at any depth. So a struct whose fields mix in `Relates` needs no hook of its own to be remapped as an element of `RelatesEach`.
///
/// Examples:
/// ---
/// static struct Owner { mixin Relates!"owner"; }
/// static struct Entry { Owner by; Relation!1 target; int weight; }
/// Entry entry;
/// entry.by.owner = 1;
/// entry.target.related[0] = 2;
/// immutable ecrs.registry.EntityId[3] remap = [0, 2, 1];
/// remapHeldIds(entry, remap[]);
/// assert(entry.by.owner == 2 && entry.target.related[0] == 1);
/// ---
void remapHeldIds(T)(ref T value, const(ecrs.registry.EntityId)[] remap) {
	static if (ecrs.registry.hasRemapEntities!T) T.remapEntities(value, remap);
	else static if (is(T == struct)) {
		static foreach (i; 0 .. T.tupleof.length) remapHeldIds(value.tupleof[i], remap);
	} else static if (__traits(isStaticArray, T)) {
		foreach (ref element; value) remapHeldIds(element, remap);
	}
}

/// The body of a component listing elements of type `E`, each of which may hold entity ids through `Relates` fields, as a growable dynarray named `field` the component owns: the hooks libECRS and `fp.lifecycle` find by name, so such a list needs none written by hand. Renumbering relabels every element through `remapHeldIds`; removing the component ends each element's lifetime and frees the list; copying it copies each element; `contentHash` and `equal` read the elements through `fp.lifecycle`.
///
/// Examples:
/// ---
/// static struct Edge { mixin Relates!("from", "to"); }
/// static struct Edges { mixin RelatesEach!Edge; }
/// Edges graph;
/// scope(exit) graph.finalize();
/// assert(fp.dynarray.pushBack(graph.items, Edge([1, 2])));
/// immutable ecrs.registry.EntityId[3] remap = [0, 2, 1];
/// Edges.remapEntities(graph, remap[]);
/// assert(graph.items[0].from == 2 && graph.items[0].to == 1);
/// ---
mixin template RelatesEach(E, string field = "items") {
	static import ecrs.registry;
	static import ecrs.relation;
	static import fp.dynarray;
	static import fp.algorithms;
	static import fp.lifecycle;

	mixin("E* " ~ field ~ " = null; /// The elements, in order.");

	// Every element, as a slice.
	private static inout(E)[] elementsOf(ref inout typeof(this) self) @nogc nothrow {
		return fp.dynarray.slice(__traits(getMember, self, field));
	}

	/// The renumbering hook `ecrs.registry.hasRemapEntities` detects: relabels every id every element holds.
	///
	/// Examples:
	/// ---
	/// static struct Owners { mixin ecrs.relation.RelatesEach!(ecrs.relation.Relation!1); }
	/// Owners list;
	/// scope(exit) list.finalize();
	/// assert(fp.dynarray.pushBack(list.items, ecrs.relation.Relation!1([1])));
	/// immutable ecrs.registry.EntityId[2] remap = [0, 5];
	/// Owners.remapEntities(list, remap[]);
	/// assert(list.items[0].related[0] == 5);
	/// ---
	static void remapEntities(ref typeof(this) self, const(ecrs.registry.EntityId)[] remap) @nogc nothrow {
		foreach (ref element; elementsOf(self)) ecrs.relation.remapHeldIds(element, remap);
		ecrs.relation.remapBesides!field(self, remap);
	}

	/// Hashes the elements in order, each through `fp.lifecycle.contentHash`.
	///
	/// Examples:
	/// ---
	/// static struct Owners { mixin ecrs.relation.RelatesEach!(ecrs.relation.Relation!1); }
	/// Owners a, b;
	/// assert(Owners.contentHash(a) == Owners.contentHash(b));
	/// ---
	static size_t contentHash(ref const typeof(this) self) @nogc nothrow {
		ulong h = fp.algorithms.chainStart;
		foreach (ref element; elementsOf(self)) h = fp.algorithms.combine(h, fp.lifecycle.contentHash(element));
		return ecrs.relation.hashBesides!field(cast(size_t) h, self);
	}

	/// Whether `a` and `b` hold equal elements, by `fp.lifecycle.equal`, in the same order.
	///
	/// Examples:
	/// ---
	/// static struct Owners { mixin ecrs.relation.RelatesEach!(ecrs.relation.Relation!1); }
	/// Owners a, b;
	/// scope(exit) a.finalize();
	/// assert(Owners.equal(a, b));
	/// assert(fp.dynarray.pushBack(a.items, ecrs.relation.Relation!1([1])));
	/// assert(!Owners.equal(a, b));
	/// ---
	static bool equal(ref const typeof(this) a, ref const typeof(this) b) @nogc nothrow {
		auto x = elementsOf(a), y = elementsOf(b);
		if (x.length != y.length) return false;
		foreach (i; 0 .. x.length)
			if (!fp.lifecycle.equal(x[i], y[i])) return false;
		return ecrs.relation.equalBesides!field(a, b);
	}

	/// Ends the lifetime, as `fp.lifecycle` defines it: ends every element's and frees the list. Safe on an empty list.
	///
	/// Examples:
	/// ---
	/// static struct Owners { mixin ecrs.relation.RelatesEach!(ecrs.relation.Relation!1); }
	/// Owners list;
	/// assert(fp.dynarray.pushBack(list.items, ecrs.relation.Relation!1([1])));
	/// list.finalize();
	/// assert(list.items is null);
	/// ---
	void finalize() @nogc nothrow {
		fp.dynarray.free(__traits(getMember, this, field));
		ecrs.relation.endLifetimeBesides!field(this);
	}

	/// Copies into the empty `dest`, as `fp.lifecycle` defines it, copying each element. If that cannot be allocated, `dest` is left empty.
	///
	/// Examples:
	/// ---
	/// static struct Owners { mixin ecrs.relation.RelatesEach!(ecrs.relation.Relation!1); }
	/// Owners list, copy;
	/// scope(exit) list.finalize();
	/// scope(exit) copy.finalize();
	/// assert(fp.dynarray.pushBack(list.items, ecrs.relation.Relation!1([1])));
	/// list.copyTo(copy);
	/// assert(copy.items !is list.items && copy.items[0].related[0] == 1);
	/// ---
	void copyTo(ref typeof(this) dest) @nogc nothrow {
		__traits(getMember, dest, field) = fp.dynarray.clone(__traits(getMember, this, field));
		ecrs.relation.copyBesides!field(dest, this);
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

	alias Dynamic = Relation!(dynamicArity, false);
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
	alias Dynamic = Relation!(dynamicArity, false);
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
	alias Terms = Relation!(dynamicArity, true);
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

	// A struct mixing in `Relates` beside its own fields is whole to every hook: two relating alike but differing elsewhere are different values.
	static struct Weighted { mixin Relates!"to"; int weight; }
	assert(!fp.lifecycle.equal(Weighted([1], 2), Weighted([1], 3)) && fp.lifecycle.equal(Weighted([1], 2), Weighted([1], 2)));
	assert(fp.lifecycle.contentHash(Weighted([1], 2)) != fp.lifecycle.contentHash(Weighted([1], 3)));
	static import fp.string;
	static struct Labelled { mixin Relates; fp.lifecycle.Owned!char label; Relation!1 also; int weight; }
	Labelled labelled, copied, read;
	assert(fp.dynarray.pushBack(labelled.related, ecrs.registry.EntityId(1)));
	labelled.label = fp.lifecycle.Owned!char(fp.string.clone("x"));
	labelled.also.related[0] = 2;
	labelled.weight = 7;
	fp.lifecycle.copyInto(copied, labelled);
	assert(copied.label.p !is labelled.label.p && copied.label.p[0] == 'x' && copied.weight == 7 && fp.lifecycle.equal(copied, labelled));
	copied.finalize();
	assert(copied.label.p is null && copied.related is null);
	// A renumbering reaches ids in the other fields, once each, however it is reached.
	immutable ecrs.registry.EntityId[3] swap = [0, 2, 1];
	Labelled.remapEntities(labelled, swap[]);
	assert(labelled.related[0] == 2 && labelled.also.related[0] == 1);
	remapHeldIds(labelled, swap[]);
	assert(labelled.related[0] == 1 && labelled.also.related[0] == 2);
	// Encoding carries the other fields of bytes; an owned field needs hooks of its own.
	static struct Counted { mixin Relates; int weight; }
	static assert(!__traits(compiles, { ubyte* o; Labelled l; Labelled.serialize(l, o); }));
	Counted counted, decodedCount;
	assert(fp.dynarray.pushBack(counted.related, ecrs.registry.EntityId(3)));
	counted.weight = 5;
	scope(exit) counted.finalize();
	scope(exit) decodedCount.finalize();
	ubyte* encoded = null;
	scope(exit) fp.dynarray.free(encoded);
	assert(Counted.serialize(counted, encoded));
	const(ubyte)[] encoding = fp.dynarray.slice(encoded);
	assert(Counted.deserialize(decodedCount, encoding) && encoding.length == 0 && fp.lifecycle.equal(decodedCount, counted));
	encoding = fp.dynarray.slice(encoded)[0 .. $ - 1];
	Counted truncated;
	assert(!Counted.deserialize(truncated, encoding) && truncated.related is null && encoding.length == fp.dynarray.length(encoded) - 1);
	labelled.finalize();
}

unittest {
	// A struct mixing in `Relates` is a relation of its own type: same shape and hooks, a distinct component.
	static struct Members { mixin Relates; }
	static struct Owners { mixin Relates; }
	static assert(ecrs.registry.shapeFor!Members == ecrs.registry.RelationShape(1, true));
	static assert(ecrs.registry.hasRemapEntities!Members && ecrs.registry.hasSerialize!Members);
	static assert(!fp.lifecycle.isBitMoveable!Members);
	static assert(ecrs.registry.componentName!Members != ecrs.registry.componentName!Owners);

	// Content hash and equality read the slots, not the dynarray pointer.
	Members a, b, empty;
	scope(exit) a.finalize();
	scope(exit) b.finalize();
	assert(fp.dynarray.pushBack(a.related, ecrs.registry.EntityId(1)) && fp.dynarray.pushBack(a.related, ecrs.registry.EntityId(2)));
	fp.lifecycle.copyInto(b, a);
	assert(a.related !is b.related && Members.equal(a, b) && Members.contentHash(a) == Members.contentHash(b));
	assert(!Members.equal(a, empty));
	b.related[1] = 3;
	assert(!Members.equal(a, b) && Members.contentHash(a) != Members.contentHash(b));

	// Terms compare by the half of the union in use: a variable never equals an entity of the same number.
	alias Terms = Relation!(1, true);
	Terms v, c, v2;
	v.related[0] = Term();
	v.related[0].varId = 5;
	c.related[0] = Term(ecrs.registry.EntityId(5));
	v2.related[0] = Term();
	v2.related[0].varId = 5;
	assert(!Terms.equal(v, c) && Terms.contentHash(v) != Terms.contentHash(c));
	assert(Terms.equal(v, v2) && Terms.contentHash(v) == Terms.contentHash(v2));

	// Named slots read and write `related`, so the hooks and the relation shape still see them, and positional literals still reach later fields.
	static struct Edge { mixin Relates!("from", "to"); }
	static struct Typed { mixin Relates!(1, true, "subject"); }
	static assert(Edge.sizeof == 2 * ecrs.registry.EntityId.sizeof && ecrs.registry.shapeFor!Edge == ecrs.registry.RelationShape(2, false));
	static assert(!__traits(compiles, { static struct Partial { mixin Relates!(2, false, "only"); } }));
	Edge edge;
	assert(edge.from == ecrs.registry.invalidEntity);
	edge.from = 1;
	edge.to = 2;
	immutable ecrs.registry.EntityId[3] swap = [0, 2, 1];
	Edge.remapEntities(edge, swap[]);
	assert(edge.from == 2 && edge.to == 1 && edge.related == [2, 1]);
	static struct Tagged { mixin Relates!"owner"; int tag; }
	auto tagged = Tagged([7], 8);
	assert(tagged.owner == 7 && tagged.tag == 8 && Tagged.sizeof == ecrs.registry.EntityId.sizeof + int.sizeof);
	Typed typed;
	typed.subject = Term(ecrs.registry.EntityId(1));
	Typed.remapEntities(typed, swap[]);
	assert(typed.related[0].constant == 2);
}

unittest { // a RelatesEach list remaps, hashes, compares, copies and frees its elements, ids nested in fields included
	static struct Owner { mixin Relates!"owner"; }
	static struct Entry { Owner by; Relation!dynamicArity targets; uint position; }
	static struct Log { mixin RelatesEach!(Entry, "entries"); }
	static assert(ecrs.registry.hasRemapEntities!Log && !fp.lifecycle.isBitMoveable!Log);

	Log log, copy;
	scope(exit) log.finalize();
	scope(exit) copy.finalize();
	Entry entry;
	entry.by.owner = 1;
	entry.position = 5;
	assert(fp.dynarray.pushBack(entry.targets.related, ecrs.registry.EntityId(2)));
	assert(fp.dynarray.pushBack(log.entries, entry));

	log.copyTo(copy);
	assert(copy.entries !is log.entries && copy.entries[0].targets.related !is log.entries[0].targets.related);
	assert(Log.equal(log, copy) && Log.contentHash(log) == Log.contentHash(copy));

	immutable ecrs.registry.EntityId[3] remap = [0, 2, 1];
	Log.remapEntities(log, remap[]);
	assert(log.entries[0].by.owner == 2 && log.entries[0].targets.related[0] == 1 && log.entries[0].position == 5);
	assert(!Log.equal(log, copy));
}
