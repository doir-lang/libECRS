/// The simplest serialization there is: `serialize` copies out the entity table and every component whose bytes are its whole value, and `deserialize` copies them back into a fresh `Context`.
///
/// Entity ids round-trip exactly, freed ones included, so a component holding ids, such as an `ecrs.relation.Relation`, needs no remapping.
/// A type that encodes itself, as `ecrs.registry.hasSerialize` detects, such as a dynamic relation, is written through its hooks instead; one that holds pointers, as `ecrs.registry.Hooks.opaque` marks it, but does not encode itself is left out.
/// Components are matched by registered name, so the loading program must register every saved type first.
/// The bytes are native: they load only where endianness and struct layout match.
module ecrs.serialization;


static import ecrs.context;
static import ecrs.registry;
static import ecrs.storage;
static import fp.dynarray;
static import fp.pointer;
static import fp.string;

public import ecrs.registry : EntityId, invalidEntity;

@nogc nothrow:


// Layout, all native-endian: magic, version, entity table length, freelist, then per section a NUL-terminated name, element size, encoded flag, count, and (owner, component) records.
private immutable char[4] magic = "ECRS";
private enum uint formatVersion = 2;


// wrapper: views a value as the bytes the encoding writes
private bool put(ref ubyte* out_, const(void)[] bytes) @trusted {
	immutable before = fp.dynarray.length(out_);
	immutable written = fp.dynarray.concatenate(out_, cast(const(ubyte)[]) bytes);
	assert(fp.dynarray.length(out_) == before + (written ? bytes.length : 0), "ecrs.serialization: wrote the wrong number of bytes");
	return written;
}

// wrapper: views a value as the bytes the encoding writes
private bool putValue(T)(ref ubyte* out_, T value) @trusted {
	return put(out_, (&value)[0 .. 1]);
}

private bool serializable(const ref ecrs.context.Context self, size_t componentId) {
	auto storage = ecrs.context.getStorage(self, componentId);
	if (storage is null || ecrs.storage.empty(*storage)) return false;
	immutable hooks = ecrs.registry.hooksOf(componentId);
	return !hooks.opaque || hooks.serializeFunction !is null;
}

private bool writeSection(ref ubyte* out_, const ref ecrs.storage.Storage storage, size_t componentId) @trusted {
	immutable encode = ecrs.registry.hooksOf(componentId).serializeFunction;
	auto name = ecrs.registry.nameOf(componentId);
	assert(name !is null, "ecrs: serializing a component the registry has forgotten");
	auto named = name[0 .. fp.string.sliceTerminated(name).length + 1];
	if (!putValue(out_, cast(ulong) named.length) || !put(out_, named)) return false;
	if (!putValue(out_, cast(ulong) storage.elementSize) || !putValue(out_, cast(ubyte)(encode !is null))) return false;
	if (!putValue(out_, cast(ulong) ecrs.storage.liveCount(storage))) return false;
	size_t written = 0;
	foreach (slot; 0 .. ecrs.storage.slotCount(storage)) {
		immutable owner = ecrs.storage.owner(storage, slot);
		if (owner == invalidEntity) continue;
		auto element = ecrs.storage.get(storage, slot);
		if (!putValue(out_, owner)) return false;
		if (encode !is null ? !encode(element, out_) : !put(out_, element[0 .. storage.elementSize])) return false;
		++written;
	}
	assert(written == ecrs.storage.liveCount(storage), "ecrs.serialization: a section whose count disagrees with its components");
	return true;
}

private bool writeContext(ref ubyte* out_, const ref ecrs.context.Context self) @trusted {
	if (!put(out_, magic[]) || !putValue(out_, formatVersion)) return false;
	if (!putValue(out_, cast(ulong) fp.dynarray.length(self.indexTable))) return false;
	immutable freed = fp.dynarray.length(self.freelist);
	if (!putValue(out_, cast(ulong) freed)) return false;
	foreach (i; 0 .. freed)
		if (!putValue(out_, cast(ulong) self.freelist[i])) return false;

	ulong sections = 0;
	foreach (id; 0 .. ecrs.context.storageCount(self))
		if (serializable(self, id)) ++sections;
	if (!putValue(out_, sections)) return false;
	assert(sections <= ecrs.context.storageCount(self), "ecrs.serialization: more sections than storages");
	foreach (id; 0 .. ecrs.context.storageCount(self))
		if (serializable(self, id) && !writeSection(out_, *ecrs.context.getStorage(self, id), id)) return false;
	assert(fp.dynarray.length(out_) >= magic.length + formatVersion.sizeof + 3 * ulong.sizeof, "ecrs.serialization: an encoding shorter than its header");
	return true;
}

/// Writes `self` into a new byte dynarray, which the caller releases with `fp.dynarray.free`: the entity table's length, the freelist, and every component with its owner, as its bytes or through its type's encoding hooks.
/// Opaque components without those hooks are left out.
///
/// Returns null if allocation fails.
///
/// Examples:
/// ---
/// static struct Health { int points; }
/// ecrs.context.Context context = ecrs.context.create();
/// scope(exit) ecrs.context.free(context);
/// ecrs.context.addComponent!Health(context, ecrs.context.addEntity(context)).points = 3;
/// ubyte* bytes = serialize(context);
/// assert(bytes !is null);
/// fp.dynarray.free(bytes);
/// ---
ubyte* serialize(const ref ecrs.context.Context self) @trusted {
	assert(!ecrs.context.inTransaction(self), "ecrs.serialization: serializing in the middle of a transaction");
	ubyte* out_ = null;
	if (writeContext(out_, self)) return out_;
	fp.dynarray.free(out_);
	return null;
}


private bool take(ref const(ubyte)[] data, void* dest, size_t n) @trusted {
	assert(dest !is null || n == 0, "ecrs.serialization: taking bytes into nowhere");
	if (data.length < n) return false;
	immutable before = data.length;
	fp.pointer.copy((cast(ubyte*) dest)[0 .. n], data[0 .. n]);
	data = data[n .. $];
	assert(data.length == before - n, "ecrs.serialization: took the wrong number of bytes");
	return true;
}

private bool readSection(ref ecrs.context.Context self, ref const(ubyte)[] data) @trusted {
	ulong nameLength, elementSize, count;
	ubyte encoded;
	if (!take(data, &nameLength, nameLength.sizeof) || nameLength == 0 || nameLength > data.length) return false;
	auto name = cast(const(char)[]) data[0 .. cast(size_t) nameLength];
	data = data[name.length .. $];
	if (fp.string.sliceTerminated(name.ptr).length + 1 != name.length) return false;

	immutable id = ecrs.registry.idOf(name.ptr);
	if (id == fp.pointer.notFound) return false;
	immutable hooks = ecrs.registry.hooksOf(id);
	immutable decode = hooks.deserializeFunction;
	if (!take(data, &elementSize, elementSize.sizeof) || elementSize != ecrs.registry.elementSizeOf(id)) return false;
	if (!take(data, &encoded, encoded.sizeof) || encoded != (decode !is null) || (decode is null && hooks.opaque)) return false;
	if (!take(data, &count, count.sizeof)) return false;
	immutable size = cast(size_t) elementSize;
	foreach (_; 0 .. count) {
		immutable remaining = data.length;
		EntityId owner;
		if (!take(data, &owner, owner.sizeof) || owner == invalidEntity || owner >= fp.dynarray.length(self.indexTable)) return false;
		if ((decode is null && data.length < size) || ecrs.context.hasComponent(self, owner, id)) return false;
		void* p = ecrs.context.addComponent(self, owner, id, size);
		if (p is null) return false;
		// A failed decode leaves the component safe to finalize, which freeing `self` then does.
		if (decode !is null) {
			if (!decode(p, data)) return false;
		} else
			cast(void) take(data, p, size); // length checked above
		assert(data.length < remaining, "ecrs.serialization: a component that read no bytes");
		assert(ecrs.context.hasComponent(self, owner, id), "ecrs.serialization: a decoded component its owner does not have");
	}
	return true;
}

// Removing in saved order rebuilds the freelist exactly, so `addEntity` hands ids out again in the same order.
private bool freeEntities(ref ecrs.context.Context self, const(ubyte)[] freedIds) @trusted {
	if (freedIds.length == 0) return true;
	immutable n = fp.dynarray.length(self.indexTable);
	auto freed = cast(bool*) fp.pointer.allocator(null, n * bool.sizeof);
	if (freed is null) return false;
	scope(exit) cast(void) fp.pointer.allocator(freed, 0);
	freed[0 .. n] = false;
	while (freedIds.length > 0) {
		ulong e;
		cast(void) take(freedIds, &e, e.sizeof); // the caller sliced whole ids
		if (e == invalidEntity || e >= n || freed[cast(size_t) e]) return false;
		freed[cast(size_t) e] = true;
		if (!ecrs.context.removeEntity(self, cast(EntityId) e)) return false;
	}
	assert(fp.dynarray.length(self.freelist) <= n, "ecrs.serialization: more freed entities than the table holds");
	return true;
}

private bool readContext(ref ecrs.context.Context self, const(ubyte)[] data) @trusted {
	char[4] fileMagic;
	uint fileVersion;
	if (!take(data, fileMagic.ptr, magic.length) || fileMagic != magic) return false;
	if (!take(data, &fileVersion, fileVersion.sizeof) || fileVersion != formatVersion) return false;

	ulong entityTableLength, freedCount, sections;
	if (!take(data, &entityTableLength, entityTableLength.sizeof) || entityTableLength == 0 || entityTableLength > EntityId.max) return false;
	foreach (_; 1 .. cast(size_t) entityTableLength)
		if (ecrs.context.addEntity(self) == invalidEntity) return false;
	assert(fp.dynarray.length(self.indexTable) == entityTableLength, "ecrs.serialization: a table of the wrong length");

	// Freed ids are applied after the components, which may only be given to entities that exist.
	if (!take(data, &freedCount, freedCount.sizeof) || freedCount > data.length / ulong.sizeof) return false;
	auto freedIds = data[0 .. cast(size_t) freedCount * ulong.sizeof];
	data = data[freedIds.length .. $];

	if (!take(data, &sections, sections.sizeof)) return false;
	foreach (_; 0 .. sections)
		if (!readSection(self, data)) return false;
	return data.length == 0 && freeEntities(self, freedIds);
}

/// Loads what `serialize` wrote into `self`, which must be fresh from `ecrs.context.create`, so every entity keeps its id and freed ids stay freed.
/// Every saved component type must already be registered under the same name and size, encoding itself just as it did when saved; `ecrs.registry.register` does that up front.
///
/// Returns false if `data` is malformed, names a type that is unknown, resized or now encoded differently, or allocation fails, leaving `self` as a fresh context again.
///
/// Examples:
/// ---
/// static struct Health { int points; }
/// ecrs.context.Context saved = ecrs.context.create();
/// scope(exit) ecrs.context.free(saved);
/// EntityId e = ecrs.context.addEntity(saved);
/// ecrs.context.addComponent!Health(saved, e).points = 3;
/// ubyte* bytes = serialize(saved);
/// scope(exit) fp.dynarray.free(bytes);
///
/// ecrs.context.Context loaded = ecrs.context.create();
/// scope(exit) ecrs.context.free(loaded);
/// assert(deserialize(loaded, fp.dynarray.slice(bytes)));
/// assert(ecrs.context.getComponent!Health(loaded, e).points == 3);
/// ---
bool deserialize(ref ecrs.context.Context self, const(ubyte)[] data) {
	assert(fp.dynarray.length(self.indexTable) <= 1 && fp.dynarray.length(self.freelist) == 0, "ecrs: deserialize needs a fresh context");
	if (readContext(self, data)) {
		assert(ecrs.context.validate(self), "ecrs.serialization: decoded a store that breaks its invariants");
		return true;
	}
	ecrs.context.free(self);
	self = ecrs.context.create();
	assert(ecrs.context.entityCount(self) <= 1, "ecrs.serialization: a refused decode left entities");
	return false;
}


unittest {
	// A round trip keeps ids, values, relations of either arity and the freelist, skips opaque components without encoding hooks, and leaves no holes.
	static import ecrs.relation;
	static struct Vec2 { float x = 0, y = 0; }
	alias Next = ecrs.relation.Relation!1;
	alias Many = ecrs.relation.Relation!(ecrs.relation.dynamicArity);
	alias ManyTerms = ecrs.relation.Relation!(ecrs.relation.dynamicArity, true);
	static struct Handle { int* p; }
	assert(ecrs.registry.hooksOf(ecrs.registry.componentId!Many()).opaque);

	auto saved = ecrs.context.create();
	scope(exit) ecrs.context.free(saved);
	EntityId[5] e;
	foreach (i, ref id; e) {
		id = ecrs.context.addEntity(saved);
		*ecrs.context.addComponent!Vec2(saved, id) = Vec2(i, -cast(float) i);
	}
	ecrs.context.addComponent!Next(saved, e[0]).related[0] = e[4];
	assert(fp.dynarray.pushBack(ecrs.context.addComponent!Many(saved, e[1]).related, e[2]));
	auto many = ecrs.context.addComponent!Many(saved, e[4]);
	assert(fp.dynarray.pushBack(many.related, e[0]) && fp.dynarray.pushBack(many.related, e[2]));
	assert(ecrs.context.addComponent!Many(saved, e[2]) !is null); // empty
	auto terms = ecrs.context.addComponent!ManyTerms(saved, e[0]);
	assert(fp.dynarray.pushBack(terms.related, ecrs.relation.Term()) && fp.dynarray.pushBack(terms.related, ecrs.relation.Term(e[4])));
	assert(ecrs.context.addComponent!Handle(saved, e[0]) !is null);
	assert(ecrs.context.removeComponent!Vec2(saved, e[2])); // leaves a hole
	assert(ecrs.context.removeEntity(saved, e[3]));
	assert(ecrs.context.removeEntity(saved, e[1]));

	ubyte* bytes = serialize(saved);
	assert(bytes !is null);
	scope(exit) fp.dynarray.free(bytes);

	auto loaded = ecrs.context.create();
	scope(exit) ecrs.context.free(loaded);
	assert(deserialize(loaded, fp.dynarray.slice(bytes)));
	assert(ecrs.context.entityCount(loaded) == ecrs.context.entityCount(saved));
	assert(ecrs.context.getComponent!Vec2(loaded, e[0]) == Vec2(0, 0));
	assert(ecrs.context.getComponent!Vec2(loaded, e[4]) == Vec2(4, -4));
	assert(!ecrs.context.hasComponent!Vec2(loaded, e[2]));
	assert(ecrs.context.getComponent!Next(loaded, e[0]).related[0] == e[4]);
	auto loadedMany = ecrs.context.getComponent!Many(loaded, e[4]).related;
	assert(fp.dynarray.length(loadedMany) == 2 && loadedMany[0] == e[0] && loadedMany[1] == e[2]);
	assert(loadedMany !is many.related);
	assert(ecrs.context.getComponent!Many(loaded, e[2]).related is null);
	assert(!ecrs.context.hasComponent!Many(loaded, e[1])); // its entity was freed
	auto loadedTerms = ecrs.context.getComponent!ManyTerms(loaded, e[0]).related;
	assert(fp.dynarray.length(loadedTerms) == 2 && loadedTerms[0].isVar && loadedTerms[1].constant == e[4]);
	assert(!ecrs.context.hasComponent!Handle(loaded, e[0]));
	assert(ecrs.storage.slotCount(*ecrs.context.getStorage!Vec2(loaded)) == 2);
	assert(ecrs.context.addEntity(loaded) == ecrs.context.addEntity(saved));
	assert(ecrs.context.addEntity(loaded) == ecrs.context.addEntity(saved));

	// An empty context round-trips too.
	auto empty = ecrs.context.create();
	scope(exit) ecrs.context.free(empty);
	ubyte* emptyBytes = serialize(empty);
	scope(exit) fp.dynarray.free(emptyBytes);
	auto reloaded = ecrs.context.create();
	scope(exit) ecrs.context.free(reloaded);
	assert(deserialize(reloaded, fp.dynarray.slice(emptyBytes)));
	assert(ecrs.context.entityCount(reloaded) == 1);
}

unittest {
	// Malformed data, an unknown name and failed allocations each fail, leaving a fresh context; truncation also cuts a dynamic relation short.
	static import ecrs.relation;
	alias Many = ecrs.relation.Relation!(ecrs.relation.dynamicArity);
	static struct Stamp { long value; }
	auto saved = ecrs.context.create();
	scope(exit) ecrs.context.free(saved);
	foreach (i; 0 .. 3)
		ecrs.context.addComponent!Stamp(saved, ecrs.context.addEntity(saved)).value = i;
	foreach (EntityId related; 1 .. 4)
		assert(fp.dynarray.pushBack(ecrs.context.ensureComponent!Many(saved, 1).related, related));
	assert(ecrs.context.removeEntity(saved, 2));
	ubyte* bytes = serialize(saved);
	assert(bytes !is null);
	scope(exit) fp.dynarray.free(bytes);
	auto data = fp.dynarray.slice(bytes);

	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);
	foreach (n; 0 .. data.length) {
		assert(!deserialize(context, data[0 .. n]));
		assert(ecrs.context.entityCount(context) == 1);
	}

	ubyte* corruptBytes = fp.dynarray.clone(bytes);
	assert(corruptBytes !is null);
	scope(exit) fp.dynarray.free(corruptBytes);
	auto corrupt = fp.dynarray.slice(corruptBytes);
	corrupt[0] = 'X';
	assert(!deserialize(context, corrupt));

	enum name = ecrs.registry.componentName!Stamp;
	bool renamed = false;
	foreach (i; 0 .. data.length - name.length)
		if (cast(const(char)[]) data[i .. i + name.length] == name) {
			fp.pointer.copy(corrupt, data);
			corrupt[i + name.length - 1] = '?';
			assert(!deserialize(context, corrupt));
			renamed = true;
		}
	assert(renamed);

	foreach (n; 0 .. 64) {
		ecrs.registry.failAllocationsAfter(n);
		immutable loaded = deserialize(context, data);
		ecrs.registry.restoreAllocations();
		if (!loaded) {
			assert(ecrs.context.entityCount(context) <= 1);
			continue;
		}
		assert(ecrs.context.getComponent!Stamp(context, 3).value == 2);
		assert(fp.dynarray.length(ecrs.context.getComponent!Many(context, 1).related) == 3);
		break;
	}
	assert(ecrs.context.entityCount(context) == 3);

	ecrs.registry.failAllocationsAfter(0);
	assert(serialize(saved) is null);
	ecrs.registry.restoreAllocations();
}
