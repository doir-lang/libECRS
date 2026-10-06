/// D port of hello.cpp - a minimal smoke test exercising the public API:
/// component registration, entity/component CRUD, and the entities() range.
module examples.simple;

import core.stdc.stdio : printf;
import ecrs;

struct Vec2 { float x, y; }

extern (C) void main() {
	registerComponents!(Vec2, int, float)();
	scope(exit) freeRegistry();

	printf("int component id: %zu\n", lookupComponentId("int"));
	printf("int component size: %zu\n", lookupComponentSize(componentId!int()));

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	EntityId e1 = ctx.addEntity();
	ctx.addComponent!Vec2(e1) = Vec2(1, 2);
	EntityId e2 = ctx.addEntity();
	ctx.addComponent!Vec2(e2) = Vec2(3, 4);
	EntityId e3 = ctx.addEntity();
	ctx.addComponent!Vec2(e3) = Vec2(5, 6);

	ctx.removeEntity(e2);

	foreach (e; ctx.entities()) {
		if (!ctx.hasComponent!Vec2(e)) continue; // skips the reserved invalid entity 0
		auto comp = ctx.getComponent!Vec2(e);
		printf("%u: %f, %f\n", cast(uint) e, cast(double) comp.x, cast(double) comp.y);
	}

	// The same entities, read from the storage's owner list instead.
	foreach (e; ctx.getStorage!Vec2().owners())
		if (e != invalidEntity) printf("owns a Vec2: %u\n", cast(uint) e);
}
