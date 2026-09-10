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

	auto ctx = Context.create();
	scope(exit) ctx.free();
	ctx.makeCurrent();

	Entity e1, e2, e3;
	{
		e1 = ctx.addEntity();
		auto c1 = &e1.addComponent!Comp();
		c1.value = Vec2(1, 2);

		e2 = ctx.addEntity();
		auto c2 = &e2.addComponent!Comp();
		c2.value = Vec2(3, 4);

		e3 = ctx.addEntity();
		auto c3 = &e3.addComponent!Comp();
		c3.value = Vec2(5, 6);
	}

	e2.remove();

	foreach (e; ctx.entities()) {
		if (!e.hasComponent!Comp()) continue; // skips the reserved invalid entity 0
		auto comp = e.getComponent!Comp();
		printf("%u: %f, %f\n", cast(uint) e.entity_, cast(double) comp.x, cast(double) comp.y);
	}
}
