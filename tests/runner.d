/// Manual unittest runner for -betterC: druntime's automatic test runner
/// (`core.runtime.runModuleUnitTests`) isn't available, so this discovers
/// and runs every `unittest {}` block in the ecrs package modules itself.
module runner;

import std.meta : AliasSeq;
import ecrs.registry;
import ecrs.storage;
import ecrs.context;
import ecrs.relation;
import ecrs.system;

private alias ModuleList = AliasSeq!(
	ecrs.registry,
	ecrs.storage,
	ecrs.context,
	ecrs.relation,
	ecrs.system,
);

extern (C) void main() {
	import core.stdc.stdio : printf;

	size_t count = 0;
	static foreach (m; ModuleList) {
		static foreach (u; __traits(getUnitTests, m)) {
			u();
			count++;
		}
	}
	printf("libecrs: %zu unittests passed\n", count);
}
