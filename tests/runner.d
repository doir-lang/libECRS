/**
* `-betterC` has no built-in unittest runner, so this walks every module's
* tests with `__traits(getUnitTests)` and calls them.
*
* Progress goes to `stderr`, which is unbuffered, so a test that hangs or
* aborts still leaves a record of how far the run got.
*/
module runner;

import core.stdc.stdio : fprintf, printf, stderr;

/*
* `ecrs.package` is only public imports, so it has no tests of its own and
* is left out; naming it here would run nothing and report a module with
* zero tests.
*/
private enum modules = [
    "ecrs.registry",
    "ecrs.storage",
    "ecrs.context",
    "ecrs.relation",
    "ecrs.system",
];

private int runEveryTest() {
    size_t total = 0;

    static foreach (name; modules) {{
        alias mod = mixin("imported!\"" ~ name ~ "\"");
        alias tests = __traits(getUnitTests, mod);
        fprintf(stderr, "%s (%d tests)\n", name.ptr, cast(int) tests.length);
        static foreach (i, test; tests) {
            fprintf(stderr, "  [%d] ", cast(int) i);
            test();
            fprintf(stderr, "ok\n");
            ++total;
        }
    }}

    printf("libecrs: all %d tests passed.\n", cast(int) total);
    return 0;
}

/**
* `tools/coverage.sh` builds this as ordinary D rather than `-betterC`,
* because `-cov` registers its counters through druntime. That build needs
* druntime's own `main` so the registration actually runs.
*/
version(EcrsCoverage) {
    /*
    * druntime would otherwise run every `unittest` itself on the way to
    * `main`, and `runEveryTest` then runs the same tests a second time.
    * Replacing the tester with one that runs nothing (but still asks for
    * `main`) leaves this build doing exactly what the `-betterC` one does.
    */
    shared static this() {
        import core.runtime : Runtime, UnitTestResult;
        Runtime.extendedModuleUnitTester = () => UnitTestResult(0, 0, true, false);
    }

    int main() { return runEveryTest(); }
} else
    extern(C) int main() { return runEveryTest(); }
