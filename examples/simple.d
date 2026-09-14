/// D port of hello.cpp - a minimal smoke test exercising the public API:
/// component registration, entity/component CRUD, and the entities() range.
module examples.simple;

import core.stdc.stdio : printf;
import ecrs;

struct Vec2 { float x, y; }
alias Comp = WithEntity!Vec2;
static assert(hasSwapEntities!Comp);

extern (C) void main() {
	registerComponents!(Comp, int, float)();
	scope(exit) freeRegistry();

	printf("int component id: %zu\n", lookupComponentId("int"));
	printf("int component size: %zu\n", lookupComponentSize(componentId!int()));

	auto ctx = ecrs.context.create();
	scope(exit) ecrs.context.free(ctx);

	EntityId e1, e2, e3;
	{
		e1 = ctx.addEntity();
		auto c1 = &ctx.addComponent!Comp(e1);
		c1.value = Vec2(1, 2);

		e2 = ctx.addEntity();
		auto c2 = &ctx.addComponent!Comp(e2);
		c2.value = Vec2(3, 4);

		e3 = ctx.addEntity();
		auto c3 = &ctx.addComponent!Comp(e3);
		c3.value = Vec2(5, 6);
	}

	ctx.removeEntity(e2);

	foreach (e; ctx.entities()) {
		if (!ctx.hasComponent!Comp(e)) continue; // skips the reserved invalid entity 0
		auto comp = ctx.getComponent!Comp(e);
		printf("%u: %f, %f\n", cast(uint) e, cast(double) comp.x, cast(double) comp.y);
	}
}
