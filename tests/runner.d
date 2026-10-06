/// Runs every module's unittests, which `-betterC` has no built-in runner for, by walking them with `__traits(getUnitTests)`. Progress goes to the unbuffered `stderr`, so a test that hangs or aborts still shows how far the run got.
module runner;

import core.stdc.stdio : fprintf, printf, stderr;

// `ecrs.package` only re-exports, so it has no tests of its own.
private enum modules = [
	"ecrs.registry",
	"ecrs.storage",
	"ecrs.relation",
	"ecrs.context",
	"ecrs.system",
	"ecrs.datalog",
	"datalog_hammer",
];

private int runEveryTest() {
	size_t total = 0;

	static foreach (name; modules) {{
		alias mod = mixin("imported!\"" ~ name ~ "\"");
		alias tests = __traits(getUnitTests, mod);
		cast(void) fprintf(stderr, "%s (%d tests)\n", name.ptr, cast(int) tests.length);
		static foreach (i, test; tests) {
			cast(void) fprintf(stderr, "  [%d] ", cast(int) i);
			test();
			cast(void) fprintf(stderr, "ok\n");
			++total;
		}
	}}

	// Releases the registry's process-lifetime tables, so a leak checker sees nothing outstanding.
	imported!"ecrs.registry".free();

	cast(void) printf("libecrs: all %d tests passed.\n", cast(int) total);
	return 0;
}

// `tools/coverage.py` builds this as ordinary D, since `-cov` registers its counters through druntime, which needs druntime's own `main`.
version(EcrsCoverage) {
	// Stops druntime running every unittest itself before `main` runs them again.
	shared static this() {
		import core.runtime : Runtime, UnitTestResult;
		Runtime.extendedModuleUnitTester = () => UnitTestResult(0, 0, true, false);
	}

	int main() { return runEveryTest(); }
} else
	extern(C) int main() { return runEveryTest(); }
