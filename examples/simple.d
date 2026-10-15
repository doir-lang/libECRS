/// A minimal tour of the public API: component registration, entities and components, and iterating entities.
module examples.simple;

import core.stdc.stdio : printf;
static import ecrs.context;
static import ecrs.registry;
static import ecrs.storage;

struct Vec2 { float x, y; }

extern(C) int main() {
	if (!ecrs.registry.register!(Vec2, int, float)()) return 1;
	scope(exit) ecrs.registry.free();

	cast(void) printf("int component id: %zu\n", ecrs.registry.lookupId("int"));
	cast(void) printf("int component size: %zu\n", ecrs.registry.lookupSize(ecrs.registry.componentId!int()));

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	// Each step can fail only by running out of memory, which a real program would handle.
	immutable Vec2[3] positions = [Vec2(1, 2), Vec2(3, 4), Vec2(5, 6)];
	ecrs.registry.EntityId[3] entities;
	foreach (i, position; positions) {
		entities[i] = ecrs.context.addEntity(ctx);
		if (entities[i] == ecrs.registry.invalidEntity) return 1;
		auto component = ecrs.context.addComponent!Vec2(ctx, entities[i]);
		if (component is null) return 1;
		*component = position;
	}
	if (!ecrs.context.removeEntity(ctx, entities[1])) return 1;

	foreach (e; ecrs.context.entities(ctx)) {
		if (!ecrs.context.hasComponent!Vec2(ctx, e)) continue; // the reserved entity 0 has none
		auto component = ecrs.context.getComponent!Vec2(ctx, e);
		cast(void) printf("%u: %f, %f\n", cast(uint) e, cast(double) component.x, cast(double) component.y);
	}

	// The same entities, read from the storage's owner list instead.
	foreach (e; ecrs.storage.owners(*ecrs.context.getStorage!Vec2(ctx)))
		if (e != ecrs.registry.invalidEntity) cast(void) printf("owns a Vec2: %u\n", cast(uint) e);
	return 0;
}
