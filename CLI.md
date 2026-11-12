# Truss Command Line

This document describes `truss`, the one program that people and agents run
to work on Truss code. It lives in [`stage0/cli/`](stage0/cli) and covers
checking, testing, running, building, and the tools that tell an agent a
change's effects. It follows [GOALS.md](GOALS.md) and the decisions in
[DESIGN.md](DESIGN.md). It drives the type checker
([TYPECHECKER.md](TYPECHECKER.md)), the prover ([PROVER.md](PROVER.md)), and
code generation ([CODEGEN.md](CODEGEN.md)) through the code database
([DATABASE.md](DATABASE.md)).

## Principles

- **One program.** Every tool a Truss user runs is a subcommand of `truss`:
  one thing to install, one version to report, and one place that loads a
  package. The rest of the compiler is libraries that return data, and this
  program owns every command, report, and exit status. Tools for developing
  the compiler are separate programs in `stage0/tools/`, not shipped.
- **Every command is O(change),** so commands act on the whole package by
  default, and need few flags to select packages and tests.
- **No warnings, no levels, no configuration of checks.** A command either
  succeeds or reports errors.
- **Built for agents as much as for people.** Every command that reports
  results can report them as JSON, with stable diagnostic codes and fixes as
  byte ranges, and `holes`, `show`, `impact`, and `rename` report a change's
  effect, print the relevant signatures, and edit code structurally, as
  GOALS.md asks.
- **Deterministic output.** A command's output depends only on the code, the
  toolchain, and, for `run` and external tests, the environment. It does not
  depend on whether a background process was running, on the cache, or on
  the number of cores. The exceptions describe the run itself: which test
  results were cached, and how long each step took.

## Commands

| Command | Action |
|---|---|
| `truss check` | Reports every diagnostic of the packages and of the project's packages they depend on, and the overlaps with other worktrees; `--fix` applies each diagnostic's only fix, and `--no-proofs` skips the prover |
| `truss test` | Checks the packages, then runs the tests that have no cached result |
| `truss run` | Checks the package, builds its program for development, and runs it |
| `truss build` | Checks the package and builds its program for release; rejects a program whose `main` reaches a `todo` or an `echo` |
| `truss holes` | Lists every `todo` with its type, the bindings in scope, and the tests and `main` that reach it |
| `truss show` | Prints the signatures of a package, module, type, or definition |
| `truss impact` | Lists the definitions that the worktree changes since a base commit, and their dependents |
| `truss references`, `truss dependencies` | Lists the dependents or the dependencies of a definition, by part |
| `truss explain` | Describes the name or expression at a position: its meaning, its type, and the signature of its definition |
| `truss overlap` | Lists where the worktree's changes overlap those of other worktrees or of a branch |
| `truss rename` | Renames a definition, method, or module, and every reference to it in the project |
| `truss add` | Adds registry packages as dependencies, and records their versions in the lock file |
| `truss upgrade` | Changes the versions of the project's registry packages, and reports the effect |
| `truss publish` | Publishes the package to the registry as its next version, if it is complete and compatible |
| `truss new` | Creates a package |
| `truss sync`, `truss status`, `truss stop` | Updates a worktree's session, lists the background process's sessions, and stops the process |
| `truss clean` | Stops the background process and deletes the store |
| `truss lsp` | Runs the language server for an editor, on standard input and output |

`truss --version` prints the toolchain's Truss version, which is compared
with the `truss` field of a package's manifest. It also prints the version
of each stage that has one: code generation and the Unicode tables. These
versions are part of exact keys, so a report of a stale result can name the
stage that produced it. Every other result is keyed by the compiler's
identity, the hash of its executable.

### Finding the packages

A command acts on the packages of its project (see
[PACKAGES.md](PACKAGES.md#projects)), through the project's session in the
code database. A directory with no manifest at or above it belongs to no
project, and a command there cannot run.

A command acts on the packages at or below the current directory, or else on
the package that contains it. Run in a package's directory, or below it, a
command acts on that package. Run at the root of a project of several
packages, it acts on all of them. `run` and `build` need exactly one package
and report an error when there are several. `-C DIRECTORY`, as in `git` and
`make`, runs the command as if from that directory, and can be written
before or after the command. The positional arguments are left to each
command.

A directory with its own `truss.toml` is another package. Directories named
`_build` or `node_modules`, or whose names start with `.`, are skipped.

A manifest problem is an error in the code. It is reported with the
diagnostics, and the exit status is 1. These are manifest problems:

- a manifest that does not parse, with the line
- a package name used twice in the project, or the name `standard`
- a package without a `truss` field, or with a `truss` version newer than
  the toolchain's, which `truss --version` prints
- a dependency that is not a package of the project and has no version in
  the lock file, a package that depends on itself, or a dependency cycle
- a lock file that does not parse, that names a package whose files cannot
  be fetched, or that differs from the lock file the manifests determine
- a package that runs on every target and has a dependency with
  `usize_bits = 64`
- a one-part package name that is the owner in another package's name,
  since a path that starts with it would be ambiguous
- a `[test]` table in a manifest other than the project's
- a grant that names no capability
- a dependency that no code in its package uses

The last two require the package's code, as described in TYPECHECKER.md's
"The manifest", and are reported only for the packages the command acts on.

### Common options

- **`--json`** writes one JSON document to standard output instead of the
  report for people. Every command accepts it except `run`, `new`, and
  `clean`, whose output is a program's output or nothing. Each command
  lists its fields below. Every document has `"format": 1`, which changes
  only when a field is removed or changes meaning. Every document also has
  `"diagnostics"`, an array of diagnostics as `Diagnostic.to_json_object`
  writes them, each with its file. A command that reads code adds
  `"problems"`, the manifest problems. A command that stops at diagnostics
  still writes its document.
- **`-C DIRECTORY`**, described above.
- **`--no-server`,** before or after the command, or `TRUSS_NO_SERVER=1`,
  runs the command in its own process instead of the background process (see
  [The background process](#the-background-process)).

There is no `--quiet` or `--verbose` beyond the options each command lists.
Reports for people are plain text. Color, once added, will appear only on a
terminal and never when `NO_COLOR` is set, so it needs no option either.

Every position a command prints names its file by a path relative to the
current directory, such as `forecast.truss` or `../weather/forecast.truss`,
so a terminal or an editor can open it. A program from a development build
prints its own positions the same way, so a failed test's message matches
the diagnostics. A release build names files relative to the package root,
such as `weather/forecast.truss`, so the program is identical wherever it was
built.

### Output streams and exit status

- **A command's result goes to standard output:** a test report, a list of
  holes, signatures, or a JSON document. **Diagnostics for people go to
  standard error,** so standard output of
  `truss run` holds only the program's output. With `--json`, diagnostics
  are in the document on standard output, and standard error is empty unless
  the command could not run.
- **Exit status:**

  | Status | Meaning |
  |---|---|
  | 0 | The command succeeded, and the code has no error |
  | 1 | The code has an error: a diagnostic, a failed test, or a build rejected for a `todo` |
  | 2 | The command could not run: a bad argument, a path that names nothing, no `truss.toml`, no C compiler, or a compiler bug |

  Once the program starts, `truss run` exits with the program's status.

## Checking

```text
truss check [--fix] [--no-proofs] [--json]
```

`truss check` runs every stage that reports diagnostics: lexing, parsing,
name resolution, type checking, the ownership check, the capability and
dependency-grant checks, the package-wide checks, and the prover.

Every command that reads code also checks the project's packages that its
packages depend on, transitively, because the program is built from them.
Code generation cannot lower a body that does not type-check, and a release
build omits the run-time checks that the dependencies' proofs replace. A
registry package and the standard library are checked and proven when they
are published, so commands do not check them again (see [Registry
packages](#registry-packages)).

The prover runs by default, since a package whose obligations are unchecked
has not been checked. The prover reads the type checker's output, so it proves a
file only once no other stage reports a diagnostic in it. It needs the
pinned solver, as `run` needs a C compiler. Code generation reports no
diagnostics, so `check` builds only the checks of tagged templates, which
the prover runs as described in PROVER.md's "Running code while proving".
Their results are cached by the key of their code, as test results are.
`test` and `run` do not run the prover, since tests do not wait for proofs.

**`--no-proofs`** skips the prover. It reports every other stage's
diagnostics and needs no solver. Proofs are modular and cached, but a fresh
session, a strengthened contract with many callers, or a new dependency can
still leave many obligations to solve, and type errors are fixed first. A
package is checked only when `check` without the
flag reports nothing, and `build` and `publish` require that.

`check` prints the manifest problems, then every diagnostic except the
prover's, then the prover's diagnostics, and then a count. Each diagnostic
is printed as `Diagnostic.render` prints it, at most `Diagnostic.limit` per
file. The prover starts only after the other diagnostics are printed, so
type errors appear while the solver runs. The JSON document is
`{"format", "diagnostics"}`.

**`--fix`** applies every fix that is the only fix of its diagnostic, writes
the files, checks again, and repeats until no such fix remains. It then
reports the remaining diagnostics. Two fixes whose edits overlap are not
applied in the same round, because applying both could produce neither
intended result; the second waits for the next round, after the file is
checked again. `--fix` stops after 32 rounds, so two fixes that undo each
other cannot loop forever. A diagnostic with several fixes is a choice for
the person or agent, so `--fix` reports it and leaves it. A possible
overflow, for example, has four fixes. An unused dependency has one fix,
which deletes its manifest entry, and `--fix` applies it. A capability that
is not granted has no fix: `--fix` never widens a grant, as PACKAGES.md's
"Grants" says. An agent that has chosen a fix applies its edits
from the JSON. Fixing is on the checking command, since a separate command
would load and check the package exactly as `check` does. The JSON document adds `"fixed"`, the
diagnostics whose fixes were applied.

`check` also prints, on standard output, where the worktree's changes
overlap those of the repository's other worktrees that the background
process has open, as [`truss overlap`](#truss-overlap) does. An overlap is
not a diagnostic, since neither worktree's code has an error, so it does not
change the exit status. The JSON document lists them in `"overlaps"`.

## Testing

```text
truss test [--match TEXT] [--timings] [--rerun] [--json] [FILE_OR_DIRECTORY...]
```

`truss test` checks the packages, stops if there is any diagnostic, and runs
the tests as described in CODEGEN.md's "Tests": one test program, a worker
per core, and each result cached by the key of the code the test can reach.
A test with a cached result is not built or run again. External tests, the
tests with `uses`, run every time, as SPECIFICATION.md requires.

- **Selection.** All tests run by default, which is cheap because results
  are cached. File and directory arguments select the tests defined in them,
  and `--match TEXT` selects the tests whose names contain the text. There is
  no way to skip external tests: SPECIFICATION.md requires them to run every time
  the suite runs.
- **Progress.** While the tests build and run, a status line on standard
  error shows the number of tests finished, the number that did not pass,
  the elapsed time, and the longest-running test. It is redrawn as each test starts and ends:

  ```text
  [ 97/143] 1 not passed · 0.6s · running weather::parse "reads hourly rows" (0.4s)
  ```

  Before the tests run, the line shows the build instead: lowering, then the
  number of uncached C files compiled. The line is drawn only when standard
  error is a terminal, and it is erased when the run ends, so logs and CI
  output contain only the report. It never appears on standard output or
  with `--json`.
- **The report** lists every test that did not pass, in test order, with its
  outcome, its message, and its `echo` output indented under it. It ends
  with a count of each outcome, the number of passes from the cache, and the
  run's duration:

  ```text
  weather::forecast "rain chance is a percentage": failed
      assert failed at forecast.truss:41:3
  weather::parse "reads hourly rows": incomplete
      todo at parse.truss:18:15

  141 passed (139 cached), 1 failed, 1 incomplete in 1.4s (check 0.1s, build 0.9s, tests 0.4s)
  ```

  Passing tests are omitted. After a small edit nearly
  every test passes from the cache, and listing them would bury the few
  relevant lines. The report follows test order, not completion order, so
  two runs of the same code produce the same report except for durations.
- **`--timings`** lists every selected test, passing or not, slowest first,
  with its duration, after the report. A cached test shows the duration
  from the run that produced its result and is marked `cached`, so the list
  gives the cost of the whole suite and not only of this run:

  ```text
  2.31s  weather::forecast "a year of hourly data"
  420ms  weather::parse "reads hourly rows"
   87µs  weather::render "renders an empty report"  cached
  ```

  A duration is the test's time in its worker, from dispatch to completion.
  It excludes the build and the wait for a free worker.
- **Outcomes** are the test program's: `passed`, `failed`, `panicked`,
  `incomplete`, `timed_out`, and `crashed`. **Every outcome except `passed`
  fails the run,** with exit status 1. A test written before the code it
  tests, which DESIGN.md allows, fails the suite until that code exists, as
  in test-first development. `incomplete` is a separate outcome, so the
  report distinguishes tests that reach a `todo` from tests that fail, and
  `truss holes` lists the tests that each `todo` blocks.
- **`--rerun`** runs every selected test without reading cached results,
  and caches the new ones. Results are
  deterministic, so this is only for a suspected cache or compiler bug, or
  for timing every test on the current machine.
- **The time limit** of each test is set in the project's manifest as
  `[test] time_limit = 10`, in seconds, and defaults to 10. It is not a flag,
  so every machine and every CI run uses the same limit. A run over several
  packages builds one test program per package.
- **The JSON document** is `{"format", "diagnostics", "tests", "timings"}`.
  Each test is `{"module", "name", "file", "line", "outcome", "cached",
  "microseconds", "message", "echo"}`, for every selected test, passing or
  not. `"timings"` gives the microseconds of the check, the build, the
  tests, and the whole run. When the packages have diagnostics, each test
  has only its name and position.

## Running and building

```text
truss run [--release] [--] [ARGUMENT...]
truss build [--output PATH] [--json]
```

A package's program starts at the `main` function of its `main` module, as
described in PACKAGES.md's "Packages", and a package compiles to one program or
one library, as IMPLEMENTATION.md says. A package without that `main` is a
library and has no program, so `run` and `build` exit with 2. A function
named `main` in another module is an ordinary function.

**`truss run`** builds a development program, as described in CODEGEN.md's
"C files and optimization", and runs it on the terminal with the arguments,
so the program can prompt and read input. It then exits with the program's
status. When the background process builds the program, the program is
written to the store, and the command runs it on the client's terminal,
since the background process has none. `echo` writes to standard error, as
SPECIFICATION.md says. `run` rejects a program whose `main` reaches a `todo`, as
`build` does. DESIGN.md rules out a `todo` that panics when reached, since
that failure would not appear in the signature, and the rule holds for
development runs too. The first argument that is not an option starts the
program's arguments, and `--` marks the start when the first one begins with
`-`. **`--release`** builds as `truss build` does, and rejects an `echo` as
it does, for timing the program.

**`truss build`** builds a release program, as described in CODEGEN.md's "C
files and optimization": at `-O2`, with link-time optimization across every
file, ThinLTO when the C compiler is clang. It rejects a program with an
unproven obligation, as `check` reports it, and a program whose `main`
reaches a `todo` or an `echo`, in code or in a proof. It lists each one, and
for a `todo` in code, the call path from `main`:

```text
render.truss:12:14: `todo` can be reached from `main`, so the program cannot be built.
    weather::main::main -> weather::render::render
```

Every obligation the program reaches is proven, so the program omits the
run-time checks of a test build, as described in CODEGEN.md's "Test builds
check instead of waiting for proofs". `run --release` keeps those checks,
since it does not run the prover. The program is written to `--output`, or
else to a file named after the package in the current directory. Truss keeps every intermediate file in its cache, so the package
has no build directory, and `.gitignore` needs only the program. The JSON
document is `{"format", "diagnostics", "output"}`. When the build is
rejected, it is `{"format", "diagnostics", "unshippable"}`, and each entry
has its kind, `todo` or `echo`, its file, line, and column, and its call
path from `main`.

Building for another target, which CODEGEN.md allows through the target's
`USize`, would add `--target` to `build`. Stage0 builds for the host only.

## Tools for agents

These commands answer the questions that GOALS.md says dominate fast
development: unfinished code, a definition's contract, a change's
effects, and how to rename a definition everywhere at once.

### `truss holes`

```text
truss holes [--json] [FILE_OR_DIRECTORY...]
```

Lists every `todo` in the packages, or in the named files, as DESIGN.md's
"Unfinished code" requires. Each hole has its position, its expected type,
the bindings in scope with their types, and the work it blocks: `main`, if
`main` reaches it, and each test that reaches it. A `todo` in a theorem or a
`proof` block is a hole in a proof and is listed the same way. Each hole is
a task that a person or agent can do independently. A type defined as
`todo` is listed too.

```text
render.truss:12:14: hole of type String
    in scope: header: String, report: Report
    blocks: main; test weather::render "renders an empty report"
```

A `todo` whose type is not constrained, such as one inside an interpolation,
is listed with the type "not decided yet". Name resolution records the
bindings in scope at each `todo`, and the type checker's tables give their
types, through the `Inspect` library. A hole blocks every test, and `main`,
that reaches the hole's definition in the dependency graph that the code
database keeps. The JSON document is `{"format", "diagnostics", "holes"}`.
Each hole has its definition, file, line, and column, its kind, `value` or
`type`, its type, the bindings in scope with their types, and the tests and
`main` it blocks. A hole is not an error, so the exit status is 0 unless the
packages have diagnostics.

### `truss show`

```text
truss show [--body] [--json] PATH...
```

Prints the signatures at each path, each after its file and line. A
signature is the definition's text without any body.

- for a definition, such as `weather::forecast::parse`, its signature with
  every clause: generic parameters, parameters with their defaults, the
  return type, `uses`, `cost`, `requires`, `ensures`, and `decreases`
- for a type, such as `weather::forecast::Forecast`, its definition, its
  `derives`, and the signatures of its methods and of the `impl`s in its
  package
- for a method, such as `weather::forecast::Forecast.summary`, its signature
- for a module, such as `weather::forecast`, every definition's signature,
  and for a package, such as `weather`, every public definition's signature

A module of another package, such as `standard::list`, shows only its
definitions visible from this package, so an opaque type's fields stay
hidden. A path that names no visible definition is a bad argument, and the
exit status is 2. `--body` prints whole definitions. Truss has no comments,
so a definition's signature is its whole documentation. GOALS.md asks for a tool that gives an agent the
signatures it needs without whole files. The JSON document is
`{"format", "diagnostics", "definitions"}`, and each definition has its
path, its kind, its file and line, and its text.

### `truss impact`

```text
truss impact [--base REVISION] [--json]
```

Compares the worktree with a base commit: the commit that `--base` names, or
else the merge base of the worktree's branch and the default branch. The
comparison therefore includes every change on the branch, uncommitted ones
too. The code database compares the two sessions, as DATABASE.md's
"Questions" describes. Every result that depends on a changed
file is updated in both sessions and compared, so a result that was
recomputed with the same value counts as unchanged. Reformatting a file, or
moving a definition within its file, changes nothing. For each definition
that was added, removed, or changed, `impact` shows:

- **The parts that changed,** such as its syntax tree, its signature, or its
  body.
- **For a changed signature,** the old and new signature, which a reviewer
  must read closely, and every dependent, which are the callers to review.

It then lists the tests whose code changed, which are the only tests the
change can affect, each with whether its result is cached, so an agent knows
the cost of its change before running anything.

```text
Changed since 3f2a9c1e04b7:
  weather::forecast::parse: tree, signature, body
    was: public fn parse(text: String) -> Forecast
    now: public fn parse(text: String) -> Result[Forecast, ParseError]
    read by: weather::main::main, weather::forecast::test "parses a day"

Tests whose code changed: 1
  weather::forecast::test "parses a day"
```

A definition is matched with its earlier version by path, so a renamed
definition is listed as removed and added. Two agents on the same repository
can each run `impact` and compare the dependents, and `truss overlap` does
that for them. The JSON document is `{"format", "diagnostics", "problems",
"base", "changes", "tests"}`. Each change has its path, its kind (`added`,
`removed`, or `changed`), the parts that changed, its signature before and
after, and its dependents, with the parts on each side.

### `truss references` and `truss dependencies`

```text
truss references [--json] NAME
truss dependencies [--json] NAME
```

`references` lists the dependents of a definition, and `dependencies` lists
its dependencies, by part, such as `weather::main::main: its body reads the
signature of weather::forecast::parse`. `NAME` is a full path or a suffix of
one, such as `parse` or `Forecast.summary`, and selects every definition it
matches. The answers come from the code database's dependency graph, so no
dependency is missing: a use through a method that type checking resolved,
or through an `impl`, is found as well as a use by name. The answers
over-approximate: a use of a result about a whole package, such as the
package's impls, counts as a use of every definition that result read.

### `truss explain`

```text
truss explain [--json] FILE:LINE:COLUMN
```

Describes the name or expression at a position, written as diagnostics write
positions: a name's referent, its type, and the signature of its
definition. An agent can ask about one name without reading the file around
it.

### `truss overlap`

```text
truss overlap [--with BRANCH] [--merge] [--json]
```

Lists where the worktree's changes since its merge base with another
worktree overlap the other's changes, as described in DATABASE.md's
"Parallel work". Two changes overlap when both change the same part, or when
one change depends on a part that the other changes, such as a new call to a
function whose signature the other changes. git merges such changes cleanly,
and the merge result does not compile. `overlap` compares with every other
worktree of the repository that the background process has open, or with the
branch that `--with` names. **`--merge`** also checks the merge result,
without committing it, and lists the diagnostics that only the merge result
has.

### `truss rename`

```text
truss rename [--json] FROM TO
```

Renames a definition, a method with every version of it, or a module, and
rewrites every reference to it in every package of the project, regardless
of the current directory. `TO` is either a new name, as in `truss rename
weather::forecast::parse read`, or a full path in the same module, or for a
method, on the same type. Renaming a module, as in `truss rename
weather::forecast weather::outlook`, moves its file and rewrites every `use`
of it and every full path to it.

The rename is made in a trial, a session that starts from the worktree's
session and holds only the rename's edits, and is checked there first. It is
rejected, with no file changed, if the result has any diagnostic, such as a
name that is taken, a name that breaks a naming rule, or a name that shadows
another. A hand-made rename would cause the same diagnostics. A worktree
that already has diagnostics is rejected too, because references are found
through checked code. References in packages outside the project cannot be
rewritten, so renaming a public definition changes the package's public
interface, which `truss impact` reports like any other changed signature.
Each edit replaces only the name's tokens, so the files need no formatting
afterward. The dependents of the renamed definition are type-checked again,
but nothing is proven or tested again: solver answers and test results are
keyed without names. Renaming a local variable is left to the language
server, which has the cursor position. The JSON document is `{"format",
"diagnostics", "edits", "moved"}`, and each edit has its file, byte range,
and replacement.

## Registry packages

A package whose name has an owner and that is not a package of the project
comes from the registry, as described in PACKAGES.md's "Packages".

- **The registry is a directory,** named by `TRUSS_REGISTRY`. For each
  package it holds `owner/name/versions`, one line per version with the hash
  of its files, oldest first, and `owner/name/VERSION/`, the files published
  as that version. A registry is append-only. A command sends its own
  `TRUSS_REGISTRY` to the background process, so the result does not depend
  on the environment the process was started in.
- **A build's versions come from `truss.lock`** at the project root, and from
  the records of the packages it names, as described in PACKAGES.md's "The lock
  file" and "Choosing versions". Each package gets the highest
  version that the lock file or any package of the build names. Only `add`
  and `upgrade` choose versions.
- **Every command fetches a package's files if the store lacks them,** from
  the registry into the store, in a directory named by their hash. Fetched
  files are kept only if their hash matches the lock file. Fetching never
  changes a result. A package already in the store needs no registry.
- **A registry package is checked and proven when it is published,** and
  commands only type-check the signatures that the project uses and the
  bodies that its programs and tests reach. Its modules are not checked
  whole: its tests can use dependencies that are left out of its published
  lock file, so they are not in the project's build. Its tests are not the
  project's, and `truss test` does not run them.
- **The lock file has one canonical form.** It has one line for each registry
  package the build uses, and no other lines, at the build's versions, with
  the capabilities each package is granted. A lock file that differs is a
  problem whose message describes the difference, and `truss check --fix`
  writes the canonical one. `--fix` never chooses a version: a dependency
  that has no version in the lock file or any record is a problem whose
  message says to run `truss add`.

### `truss add`

```text
truss add [--json] PACKAGE...
```

Adds each package as a dependency of the package the command runs in. It
writes a manifest entry that grants the dependency nothing, since a grant is
a choice someone makes, and a lock file line at the registry's newest
version, or at the version written after `@`, as in
`truss add acme::geometry@1.4.2`. The new package's own dependencies come
with it, at the versions it was published with, unless the build already
has newer ones. `add` prints the packages that entered the build. A package
that the registry does not hold is a bad argument, and nothing is written.
The JSON document is `{"format", "diagnostics", "changes", "signatures",
"breaks"}`, as `upgrade` writes it.

### `truss upgrade`

```text
truss upgrade [--json] [PACKAGE...]
```

Changes every registry package of the build to its newest version, or only
the named packages, each to its newest version or to the version written
after `@`. The other versions are then chosen as for any build, so a named
package can bring newer versions of its dependencies. A requested version
lower than the build's takes effect only if no package of the build was
published with a higher one.

The new versions are checked before the lock file is written, in a trial
session that starts from the project's session, as a rename is checked. The
command prints:

- **The lock file changes:** each package that changes version, enters, or
  leaves, and each package that would be granted a capability it lacks now.
- **The changed signatures that the project depends on,** each before and
  after, with the project's definitions that depend on it. These are the
  only places to review: if every signature of a package that the project
  depends on is unchanged, only the package's bodies changed.
- **The errors that the project would have and does not have now.**

```text
`acme::units` goes from 1.1.0 to 1.2.0.

Signatures the project reads that change:
  acme::units::lengths::meter
    was: public fn meter() -> Int64
    now: public fn meter(scale: Int64) -> Int64
    read by: weather::main::height

With these versions the project has errors it does not have now:
  main.truss: `scale` is not given, and has no default.
```

It then writes the lock file. The exit status is 1 when the project would
have new errors, since the code then has an error, and 0 otherwise. The JSON
document is `{"format", "diagnostics", "changes", "signatures", "breaks"}`.
Each change has its kind (`moved`, `entered`, `left`, or `holds`), its
package, and its versions or the newly granted capabilities. Each signature
has its path, its text before and after, and its dependents. Each error is a
sentence.

### `truss publish`

```text
truss publish [--json]
```

Publishes the package the command runs in to the registry, as described in
PACKAGES.md's "Versions" and "The registry". The package's name must have an
owner. `publish` requires:

- **No errors,** including unproven obligations, and no manifest or lock
  file problem.
- **No `todo` and no `echo`** anywhere, since a library has no `main` to
  restrict the check to. Each one is listed with its position.
- **Passing tests,** except external tests. They run as `truss test` runs
  them, so a cached result is not run again.
- **Registry dependencies only.** A dependency that is a package of the
  project counts as a registry package when its files match a version the
  registry holds, so a project's packages are published one after another.
  Any other such dependency must be published first.
- **Compatibility with its newest version** (below).

The published files are the package's files as PACKAGES.md's "The lock file"
lists them: its manifest as written, its modules, and the Markdown files
beside them. The project's lock file is replaced by one with a line for each
registry package that the package's non-test code uses, transitively, at
the build's versions. A dependency used only by tests is left out, so a
project that uses the package does not inherit it. Files identical to the
newest version are not published again.

**The registry assigns the version number,** as PACKAGES.md's "Versions"
says. The first
version is 1.0.0, or 2.0.0 for a name that ends in `_v2`. After that, the
package is compared with its newest version, which is loaded into a session
of its own with the packages it was published with:

- An incompatible release is rejected. `publish` lists each incompatible
  definition, the incompatibility, its signature before and after, and the
  name to publish under instead.
- A release that only adds gets the next minor version, and the additions
  are listed.
- Any other release gets the next patch version.

```text
This release is incompatible with `acme::geometry` 1.4.2, so it cannot be published under that name:
  acme::geometry::vector::length changed its parameters or its result.
    was: public fn length(self) -> Float64
    now: public fn length(self, scale: Float64) -> Float64
Publish it under a new name, such as `acme::geometry_v2`.
```

The comparison applies PACKAGES.md's rules of compatibility (see
[Versions](PACKAGES.md#versions)) to every public definition and every `impl`.
Types are compared after type checking, so a type written through another
`use` is the same type. The exit status is 1 when the package is not
published. The JSON document is `{"format", "diagnostics", "problems",
"package", "version", "hash", "grows"}`, each entry of `grows` being
`{"path", "addition"}`, or with `"refused"`, the sentences that give the
reasons.

## The language server

```text
truss lsp
```

Speaks the Language Server Protocol on standard input and output. It holds
the text of each file the editor has open and, after each change, reports
the diagnostics `truss check` would report for the open files with that text instead
of the files on disk. It writes no file.

- **The check runs where commands run:** in the project's background
  process, or with `--no-server`, in the language server's own process. It
  reads a trial session that starts from the worktree's session and replaces
  the open files, so an edit costs O(change).
- **Each open file's diagnostics** are published as
  `textDocument/publishDiagnostics`, with a diagnostic's notes as related
  information. The prover's diagnostics are included, as `truss check`
  includes them.
- **Each obligation's state** is sent in a `truss/proofStates` notification.
  For each open file it gives every obligation's range, its code, the
  proposition to prove, whether it is proven, and whether its proof trusts
  compiled code. An editor can then mark proven and unproven code, and show
  which proofs rely on running code.
- **Positions count UTF-16 code units,** the protocol's default, or bytes
  when the client offers `utf-8` among its position encodings.
- **A burst of changes is checked once:** a check starts only when no message
  is waiting.

The server asks for each change as the whole text, and also accepts range
edits. It answers `initialize`, `shutdown`, and `exit`, and answers every
other request with a "not supported" error.

## Creating a package

```text
truss new NAME
```

Creates a directory with a `truss.toml` that names the package and the
toolchain's Truss version, and a `main.truss` with an empty `main`:

```truss
fn main(arguments: List[String]) -> ExitCode {
  ExitCode.success
}
```

A library is a package without `main`, so it needs no flag: delete the file.
The name must be a valid package name, either a `lower_snake_case` name or
an owner and a name, such as `acme::weather`, since it starts every module
path. The directory is named after the package without its owner. A package
created under a project's root is a package of that project.

## The background process

A command that reads code asks its project's background process, which
DATABASE.md's "The background process" describes, and starts it if it is not
running. The process runs the same command-line code from the command's
directory, so the result is the same as in the client's own process. A
command's writes to standard error, such as the status line, reach the client
as they happen.

- **`truss status`** lists each process's sessions, **`truss stop`** stops every
  project's process, and **`truss sync`** updates a worktree's session and does
  nothing else.
- **`--no-server` and `TRUSS_NO_SERVER=1`** run a command in its own process,
  for CI, where a process that outlives the job is a nuisance.
- **`truss new` and `truss clean`** always run in the client's process, since
  they read no code. `truss clean` stops the background process and deletes
  the store, which costs only time.

## For working on the compiler

**`--sanitize`,** on `test` and `run`, builds with AddressSanitizer and
UndefinedBehaviorSanitizer and caches no test results. A memory error in
Truss code can come only from a compiler bug, so every report is one. It is
omitted from each command's help.

## Left out

- **`truss explain CODE`,** which rustc has. A diagnostic's message, notes,
  and fixes are meant to say everything needed to act on it, and a second
  text for each code would be a second place to keep up to date.
- **A watch mode,** such as `cargo watch` or `vitest --watch`. The
  background process already updates every open worktree's session as its
  files change, so running a command again is as fast as a watch would be.
- **Selecting tests by changed files,** as Nx's `affected` does. The cache
  already runs exactly the tests whose code changed, so a selection by
  changed files could only be less precise.

## Not built

- **Comparing contracts semantically.** PACKAGES.md has a release keep a
  `requires` that the old one implies and an `ensures` that implies the old
  one, which the prover would show. `truss publish` compares a contract's
  clauses syntactically: a reworded clause is incompatible, and a clause
  whose text is unchanged but whose meaning changed, because a private
  definition it names changed, is not detected.
- **The registry checking a release itself.** `truss publish` checks the
  package on the publisher's machine and writes to the registry's directory.
- **A registry that is not a directory.** PACKAGES.md's registry is served
  over a network, keeps a public log of every version's hash, signs the
  proofs it checked, has owners who alone publish under their names, and can
  mark a release as one not to use. Stage0's registry is a directory that
  anyone with write access can add to. A lock file's hash is checked against
  the files and against the records of the packages that name it, and
  against nothing else.
- **The tests whose code an upgrade changes,** listed by `truss upgrade` as
  `truss impact` lists them.
- **Checking a package against the Truss version it names.** There is one
  version of Truss, so `truss` only checks that the toolchain is new enough.
- **`truss fmt [--check] [FILE...]`,** which waits for the formatter. It will
  rewrite the package's files, or the named ones, into the one layout
  SPECIFICATION.md describes, and print the names of the files it changed, with no
  style options. `--check` changes nothing, lists the unformatted files, and
  exits with 1, for CI. A file with
  a syntax error is reported and left unchanged. Formatting changes no
  definition, so it rebuilds nothing. `truss show` will then print a
  signature as `truss fmt` writes it.
- **Code actions, hover, and go-to-definition in `truss lsp`.** A
  diagnostic's fixes will be code actions, and `truss explain` and `truss
  references` will answer hover and navigation.
- **Renaming a field or a variant** with `truss rename`.
- **Listing the obligations to prove again** in `truss impact`, as it lists
  the tests whose code changed.
