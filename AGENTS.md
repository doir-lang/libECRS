# Agent guidelines for libecrs

## Comments

- Keep comments minimal.
  Write one only where the code does something difficult to follow on its own: a non-obvious invariant, a subtle memory or lifetime rule, a workaround for a compiler bug, or why an apparently simpler approach would be wrong.
  Do not restate what the code already says.
- Cap every free-standing comment (a `//` or `/* */` block that is not a documentation comment) at 25 words.
  If it needs more, the code or its documentation should carry the explanation instead.
- Editors here soft-wrap, so write each comment, and each paragraph of a DDoc comment, on a single line rather than hard-wrapping it at a column.
- Do not leave commented-out code, change logs, or notes about what was changed in a comment; those belong in commit messages.

## Documentation

- Put a DDoc comment (`///` or `/** */`) directly above every publicly accessible definition: each public or package-visible function, struct, enum, alias, template, mixin template, and module-level variable.
  Private helpers do not need one.
- Every DDoc comment on a function or template includes an example of its use in an `Examples:` section, as a `---` code block:

  ```d
  /// Increments `s`, waking one thread blocked in `wait` on it, if any.
  ///
  /// Examples:
  /// ---
  /// Semaphore s = create();
  /// post(s);
  /// wait(s);
  /// free(s);
  /// ---
  void post(ref Semaphore s) { ... }
  ```

- Keep examples short, and make them correct against the current API: they should compile and pass as written under `-betterC`.
  Check them with `python3 tools/doctest.py`, which compiles and runs every example and reports public definitions missing documentation or an example.
- When a platform `static if` or `version` gives an API several implementations, document the first branch's definitions; an `else` branch reimplementing the same API needs no second copy.
- A DDoc comment is documentation, not a free-standing comment, so the 25-word cap does not apply to it, but keep it as brief as the definition allows.

## Style

- Prefer plain-data structs operated on by free functions that take them by `ref` (for example `post(s)`, `free(s)`), rather than methods.
  Use member functions only for operator overloads, for `@property` accessors that name part of a field (such as `ecrs.relation.Relates` naming a slot of `related`), and for what a language protocol requires to be a member, such as range primitives (`empty`, `front`, `popFront`) or an `alias this` target.
- Prefer fully qualified names to aliasing imports: call `bc.semaphore.free(s)` rather than `import bc.semaphore : semaphoreFree = free;` or `alias semaphoreFree = bc.semaphore.free;`.
  A `static import` keeps a module's names out of scope so every use has to be qualified.
- One ecrs module uses another, or a libfp or bc-threads module, through a `static import`, so every call names its layer (`ecrs.storage.add`, `fp.dynarray.pushBack`, `bc.spinlock.readLock`).
  The exception is a `public import` that re-exports names as part of the module's own API.
- Name everything in camelCase.
  Add a trailing underscore only when the plain name is a D keyword (`out_`, `in_`, `with_`).
- Indent with tabs.
- Under a `@nogc nothrow:` label, do not repeat those attributes on the declarations it already covers, including struct members and `version` blocks.

## Failure and invariants

- Every function that can fail says in its DDoc how it reports failure (null, `false`, an empty `Nullable`, `fp.pointer.notFound`), and what state it leaves its arguments in; prefer leaving them as they were.
- Never drop the result of a call that can fail: check it, or discard it explicitly with `cast(void)` when failure is impossible or harmless there.
  Tests assert on it.
- When a limit on one value follows from another (such as a bit position), name the constant once, derive the others from it, and `assert` the limit where the value is accepted.
- Put test-only code, such as helper functions and globals the tests use, inside `version(unittest)`.

## Organization

- Where possible, group related definitions into sections (for example: types and layout, queries, creation and freeing, growth, removal), separated by blank lines, and order them so a reader meets a type before the functions built on it.
- Whenever possible, define a function before anything that uses it, so a module reads bottom-up from its building blocks.
  When functions use each other in a cycle, define first the one that more of the module uses.
- Keep a module's unittests in the same order as the code they test.
- Prefer merging a new test case into an existing `unittest` block covering the same section over adding a new block; add one only when no existing block fits.

## Bugs

- If you find a bug while working, fix it, with a test that would have caught it, rather than only reporting it.
  Only when the fix would likely take a long time, report it instead, saying what you found and where.
