/// A minimal tour of the public API: component registration, entities and components, and iterating entities.
module examples.simple;

static import ecrs.context;
static import ecrs.registry;
static import ecrs.storage;
static import fp.io;

struct Vec2 { float x, y; }

extern(C) int main() {
	if (!ecrs.registry.register!(Vec2, int, float)()) return 1;
	scope(exit) ecrs.registry.free();

	cast(void) fp.io.print("int component id: ", ecrs.registry.idOf("int"), '\n');
	cast(void) fp.io.print("int component size: ", ecrs.registry.elementSizeOf(ecrs.registry.componentId!int()), '\n');

	auto context = ecrs.context.create();
	scope(exit) ecrs.context.free(context);

	// Each step can fail only by running out of memory, which a real program would handle.
	immutable Vec2[3] positions = [Vec2(1, 2), Vec2(3, 4), Vec2(5, 6)];
	ecrs.registry.EntityId[3] entities;
	foreach (i, position; positions) {
		entities[i] = ecrs.context.addEntity(context);
		if (entities[i] == ecrs.registry.invalidEntity) return 1;
		auto component = ecrs.context.addComponent!Vec2(context, entities[i]);
		if (component is null) return 1;
		*component = position;
	}
	if (!ecrs.context.removeEntity(context, entities[1])) return 1;

	foreach (e; ecrs.context.entities(context)) {
		if (!ecrs.context.hasComponent!Vec2(context, e)) continue; // the reserved entity 0 has none
		auto component = ecrs.context.getComponent!Vec2(context, e);
		cast(void) fp.io.print(e, ": ", component.x, ", ", component.y, '\n');
	}

	// The same entities, read from the storage's owner list instead.
	foreach (e; ecrs.storage.slotOwnersOf(*ecrs.context.getStorage!Vec2(context)))
		if (e != ecrs.registry.invalidEntity) cast(void) fp.io.print("owns a Vec2: ", e, '\n');
	return 0;
}
