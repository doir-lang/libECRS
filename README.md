# libECRS

An entity-component-relation-system library for `-betterC` D. Entities are ids, components are plain-data structs stored per type, and relations are components whose slots point at other entities, so a graph lives in the same store as everything else. A Datalog layer queries that store and writes what its rules derive back into it.

## Modules

`import ecrs;` pulls in every module; `static import ecrs.context;` and the like keep each one's names qualified.

- `ecrs.registry`: gives every component type a stable numeric id, with name, size and hook tables for callers that only have an id or a name.
- `ecrs.storage`: per-type component storage, whose components never move while they exist.
- `ecrs.context`: the entity and component database, `Context`.
- `ecrs.relation`: fixed- or dynamic-arity relation components, `Relation!n`.
- `ecrs.system`: systems, and combinators that run them over a `Context` in sequence or concurrently on a `bc.threadpool`.
- `ecrs.datalog`: stratified, semi-naive Datalog whose relations are components.
- `ecrs.serialization`: saves a `Context` by copying out its components, or through encoding hooks for those holding pointers such as dynamic relations, and loads it back with every entity id intact.

Types are plain data operated on by free functions taking them by `ref`, and every function that can fail says in its documentation how it reports it. `AGENTS.md` sets out the conventions in full.

## Building

The library is a [dub](https://dub.pm) source library depending on [libfp](https://github.com/doir-lang/libfp) and [bc-threads](https://github.com/doir-lang/bc-threads).

```sh
dub test --compiler=ldc2                                   # every module's unittests
dub run --config=simple --compiler=ldc2                    # a tour of the core API
dub run --config=simpsons --compiler=ldc2                  # Datalog over a family tree
dub run --config=typeinference --compiler=ldc2             # type inference written as Datalog rules
dub build --config=datalog-bench --compiler=ldc2 --build=release
./bin/datalog-bench 1                                      # Datalog throughput; arguments are a size scale and an optional filter
```

`-betterC` has no unittest runner, so `tests/runner.d` walks each module's tests itself; a new module has to be added to its list.

## WebAssembly

```sh
python3 tools/wasi.py --serve                    # build the unittests for wasm32-wasi with threads and serve a page that runs them in a browser
python3 tools/wasi.py --node                     # build and run the same tests headlessly under Node
python3 tools/wasi.py --node --single-threaded   # the same without threads, where bc-threads pools run jobs inline
```

The script, and the page and worker scripts in `tests/wasi`, follow bc-threads' own; its README explains the setup. It downloads [wasi-sdk](https://github.com/WebAssembly/wasi-sdk) into `bin/wasi-sdk` on first use (or set `WASI_SYSROOT` and `WASI_BUILTINS`), compiles bc-threads and libfp in from the paths `dub describe` reports, and installs [@tybys/wasm-util](https://github.com/toyobayashi/wasm-util) and [@emnapi/wasi-threads](https://github.com/toyobayashi/emnapi/tree/main/packages/wasi-threads) into `bin/wasi`. Threads need an LDC newer than 1.43, which until [ldc-developers/ldc#5268](https://github.com/ldc-developers/ldc/pull/5268) compiled D's thread-locals on wasm as ordinary globals; set `DC` to an LDC master build (CI uses `ldc-master`), or pass `--single-threaded`.

## Documentation and coverage

```sh
python3 tools/doctest.py   # compile and run every DDoc example, and report undocumented public definitions
python3 tools/coverage.py  # per-module unittest coverage; -v lists uncovered lines
```

Both default to LDC; set `DC` to use another compiler.

## Profiling

```sh
DFLAGS="--frame-pointer=all" dub build --config=datalog-bench --compiler=ldc2 --build=release-debug --force
perf record --call-graph fp -e cpu_core/cycles/ -- ./bin/datalog-bench 1 "left-linear serial" # the call to profile
perf script > perf.script
~/Dev/Packages/FlameGraph/stackcollapse-perf.pl perf.script > perf.folded
~/Dev/Packages/FlameGraph/flamegraph.pl perf.folded > perf.svg
```

`--frame-pointer=all` is what makes the profile readable, and it is not optional: `--call-graph dwarf` against a build without it unwound 0.1% of cycles to a real stack, left 65% of samples with no frames at all, throttled the sample period 5x under the cost of copying stacks, and wrote 4.6GB of `perf.data`. With frame pointers in the binary, `--call-graph fp` needs none of that copying; `dwarf` also works, but there is nothing left for it to buy.

`-e cpu_core/cycles/` because a hybrid CPU otherwise reports `cpu_atom` and `cpu_core` as two events with their own sample periods, and anything that sums raw sample counts across them is measuring nothing.

Check `kernel.perf_event_paranoid` before reading any of the numbers. At the default of 2 a run can land ~40% of its cycles on a single unresolvable `0xffffffff...` address, and that time is simply invisible; `sudo sysctl kernel.perf_event_paranoid=1` attributes it.

Mind what `bin/datalog-bench` spends its time on: unfiltered, it runs every workload under every pool size, and each workload's graph is built outside the timed region but inside the profile. Pass the second argument, a substring of the printed "workload pool" line, to profile one workload under one pool, and expect pooled runs to split their stacks between the calling thread and `bc.threadpool` workers.

`perf.script` for a run of any size is gigabytes, so stream it with `awk` rather than loading it, and weight each sample by the period in its header line: once perf has throttled, that period is not constant, and treating every sample as one unit silently reweights the profile.
