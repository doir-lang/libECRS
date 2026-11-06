/// Runs every module's unittests, which `-betterC` has no built-in runner for, by walking them with `__traits(getUnitTests)`. Progress goes to the unbuffered `stderr`, so a test that hangs or aborts still shows how far the run got.
module runner;

// `ecrs.package` only re-exports, so it has no tests of its own.
private alias modules = imported!"std.meta".AliasSeq!(
	"ecrs.registry",
	"ecrs.storage",
	"ecrs.relation",
	"ecrs.context",
	"ecrs.schedules",
	"ecrs.datalog",
	"ecrs.serialization",
	"datalog_hammer",
);

private int runEveryTest() {
	cast(void) imported!"fp.testing".runTests!modules("libecrs");
	// Releases the registry's process-lifetime tables, so a leak checker sees nothing outstanding.
	imported!"ecrs.registry".free();
	return 0;
}

// `tools/coverage.py` builds this as ordinary D, since `-cov` registers its counters through druntime, which needs druntime's own `main`.
version(EcrsCoverage) {
	// Stops druntime running every unittest itself before `main` runs them again.
	shared static this() {
		static import core.runtime;
		core.runtime.Runtime.extendedModuleUnitTester = () => core.runtime.UnitTestResult(0, 0, true, false);
	}

	int main() { return runEveryTest(); }
} else
	extern(C) int main() { return runEveryTest(); }
