# Truss Command Line

`truss` is the one program that people and agents run to work on Truss code.
It covers checking, testing, running, building, and the tools that tell an
agent a change's effects. It drives the type checker
([TYPECHECKER.md](TYPECHECKER.md)), the prover ([PROVER.md](PROVER.md)), and
code generation ([CODEGEN.md](CODEGEN.md)) through the code database
([DATABASE.md](DATABASE.md)).

## Principles

- **One program.** Every tool a Truss user runs is a subcommand of `truss`:
  one thing to install, one version to report, and one place that loads a
  package. The rest of the compiler is libraries that return data.
- **Every command is O(change),** so commands act on the whole package by
  default, and need few flags to select packages and tests.
- **No warnings, no levels, no configuration of checks.** A command either
  succeeds or reports errors.
- **Built for agents as much as for people.** Every command that reports
  results can report them as JSON, with stable diagnostic codes and fixes as
  byte ranges.
- **Deterministic output.** A command's output depends only on the code, the
  toolchain, and, for `run` and external tests, the environment, never on
  the cache, the background process, or the number of cores. The exceptions
  describe the run itself: which test results were cached, and how long each
  step took.

## Commands

| Command | Action |
|---|---|
| `truss check` | Reports every diagnostic of the packages and of the project's packages they depend on, and the overlaps with other worktrees; `--fix` applies each diagnostic's only fix, and `--no-proofs` skips the prover |
| `truss test` | Checks the packages, then runs the tests that have no cached result |
| `truss run` | Checks the package, builds its program for development, and runs it |
| `truss build` | Checks the package and builds its program for release |
| `truss holes` | Lists every `todo` with its type, the bindings in scope, and the tests and `main` that reach it |
| `truss show` | Prints the signatures of a package, module, type, or definition |
| `truss impact` | Lists the definitions that the worktree changes since a base commit, and their dependents |
| `truss references`, `truss dependencies` | Lists the dependents or the dependencies of a definition, by part |
| `truss explain` | Describes the name or expression at a position: its meaning, its type, and the signature of its definition |
| `truss overlap` | Lists where the worktree's changes overlap those of other worktrees or of a branch |
| `truss rename` | Renames a definition, method, or module, and every reference to it in the project |
| `truss add` | Adds registry packages as dependencies, and records their versions in the lock file |
| `truss upgrade` | Changes the versions of the project's registry packages, and reports the effect |
| `truss publish` | Publishes the package to the registry as its next version |
| `truss new` | Creates a package |
| `truss sync`, `truss status`, `truss stop` | Updates a worktree's session, lists the background process's sessions, and stops the process |
| `truss clean` | Stops the background process and deletes the store |
| `truss lsp` | Runs the language server for an editor, on standard input and output |

`truss --version` prints the toolchain's Truss version, which is compared
with the `truss` field of a package's manifest.

### Finding the packages

A command acts on the packages of its project (see
[PACKAGES.md](PACKAGES.md#projects)). Run in a package's directory, or below
it, a command acts on that package; run at the root of a project of several
packages, it acts on all of them. `run` and `build` need exactly one package.
`-C DIRECTORY`, as in `git` and `make`, runs the command as if from that
directory.

A manifest or lock file that breaks a rule of [PACKAGES.md](PACKAGES.md) is
an error in the code, reported with the diagnostics.

### Common options

- **`--json`** writes one JSON document to standard output instead of the
  report for people. Every document has `"format": 1`, which changes only
  when a field is removed or changes meaning, and `"diagnostics"`. A command
  that stops at diagnostics still writes its document.
- **`--no-server`,** or `TRUSS_NO_SERVER=1`, runs the command in its own
  process instead of the background process, for CI, where a process that
  outlives the job is a nuisance.

Every position a command prints names its file by a path relative to the
current directory, so a terminal or an editor can open it.

### Output streams and exit status

A command's result goes to standard output, and diagnostics for people go to
standard error, so standard output of `truss run` holds only the program's
output.

| Status | Meaning |
|---|---|
| 0 | The command succeeded, and the code has no error |
| 1 | The code has an error: a diagnostic, a failed test, or a release build rejected for a `todo`, an `echo`, or a hole in a proof |
| 2 | The command could not run: a bad argument, a path that names nothing, no `truss.toml`, no C compiler, or a compiler bug |

Once the program starts, `truss run` exits with the program's status.

## Checking

```text
truss check [--fix] [--no-proofs] [--json]
```

`truss check` runs every stage that reports diagnostics, the prover
included, since a package whose obligations are unchecked has not been
checked. It also checks the project's packages that its packages depend on,
because a release build omits the run-time checks that their proofs
replace. Registry packages and the standard library were checked when they
were published, so commands do not check them again.

The prover starts only after the other diagnostics are printed, so type
errors appear while the solver runs. **`--no-proofs`** skips it, for fixing
type errors first after a change that leaves many obligations to solve.

**`--fix`** applies every fix that is the only fix of its diagnostic, checks
again, and repeats until no such fix remains. A diagnostic with several
fixes is a choice for the person or agent, so `--fix` reports it and leaves
it. A missing grant has no fix: `--fix` never widens a grant.

`check` also prints where the worktree's changes overlap those of the
repository's other worktrees, as [`truss overlap`](#truss-overlap) does. An
overlap is not a diagnostic, since neither worktree's code has an error, so
it does not change the exit status.

## Testing

```text
truss test [--match TEXT] [--timings] [--rerun] [--json] [FILE_OR_DIRECTORY...]
```

`truss test` checks the packages, stops if there is any diagnostic, and runs
every test that has no cached result. It does not wait for the prover, since
a test build checks every operation that could fail. External tests, the
tests with `uses`, run every time.

- **All tests run by default,** which is cheap because results are cached.
  File and directory arguments, and `--match TEXT`, select fewer.
- **The report lists only the tests that did not pass,** in test order, with
  each one's message and `echo` output, and ends with a count. After a small
  edit nearly every test passes from the cache, and listing them would bury
  the few relevant lines.

  ```text
  weather::forecast "rain chance is a percentage": failed
      assert failed at forecast.truss:41:3
  weather::parse "reads hourly rows": incomplete
      todo at parse.truss:18:15

  141 passed (139 cached), 1 failed, 1 incomplete in 1.4s (check 0.1s, build 0.9s, tests 0.4s)
  ```

- **Outcomes** are `passed`, `failed`, `panicked`, `incomplete`, `timed_out`,
  and `crashed`, and every outcome except `passed` fails the run. A test that
  reaches a `todo` is `incomplete`, so a test written before its code fails
  the suite until that code exists.
- **`--timings`** lists every selected test with its duration, slowest
  first, including cached ones from the run that produced their results.
- **`--rerun`** runs every selected test without reading cached results. It
  is only for a suspected cache or compiler bug, or for timing tests on this
  machine.
- **The time limit** of each test is the project manifest's `time_limit`, not
  a flag, so every machine and every CI run uses the same limit.

## Running and building

```text
truss run [--release] [--] [ARGUMENT...]
truss build [--output PATH] [--json]
```

**`truss build`** builds a release program. It rejects a program with an
unproven obligation, and a program whose `main` can reach a `todo` or an
`echo` in code, with the call path from `main`, or a hole in a proof:

```text
render.truss:12:14: `todo` can be reached from `main`, so the program cannot be built.
    weather::main::main -> weather::render::render
```

Every obligation of a release program is proven, so it omits the run-time
checks that the proofs replace.

**`truss run`** is `truss build` followed by running the program on the
terminal with the arguments, except that it builds for development unless
given **`--release`**. A development build does not run the prover, so it
keeps the run-time checks. It refuses nothing that its `main` reaches: a
`todo` that runs stops the program with its position, and an `echo` writes
to standard error.

| | Development: `truss run` | Release: `truss build`, `truss run --release` |
|---|---|---|
| Proofs | Not run | Every obligation proven |
| Run-time checks | Kept | Omitted |
| A `todo` that `main` can reach | Stops the program if it runs | Rejected |
| An `echo` that `main` can reach | Writes to standard error | Rejected |
| A hole in a proof that `main` relies on | Allowed | Rejected |

The program is written to `--output`, or to a file named after the package.
Every intermediate file is in the cache, so a package has no build
directory. Stage0 builds for the host only.

## Tools for agents

These commands answer the questions that GOALS.md says dominate fast
development: unfinished code, a definition's contract, a change's effects,
and how to change a name everywhere at once.

### `truss holes`

```text
truss holes [--json] [FILE_OR_DIRECTORY...]
```

Lists every `todo` with its position, its expected type, the bindings in
scope, and the work it blocks: `main`, if `main` reaches it, and each test
that reaches it. Each hole is a task that a person or agent can do
independently. A hole is not an error, so the exit status is 0 unless the
packages have diagnostics.

```text
render.truss:12:14: hole of type String
    in scope: header: String, report: Report
    blocks: main; test weather::render "renders an empty report"
```

### `truss show`

```text
truss show [--body] [--json] PATH...
```

Prints the signatures at each path: a definition's signature with every
clause; a type's definition with its methods and `impl`s; a module's
definitions; or a package's public definitions. Truss has no comments, so a
definition's signature is its documentation, and `show` gives an agent the
signatures it needs without whole files. A module of another package shows
only what is visible from this one. `--body` prints whole definitions.

### `truss impact`

```text
truss impact [--base REVISION] [--json]
```

Compares the worktree, uncommitted changes included, with a base commit: the
one `--base` names, or the merge base with the default branch. For each
definition that was added, removed, or changed, it shows the parts that
changed and, for a changed signature, the old and new signature and every
dependent. It then lists the tests whose code changed, which are the only
tests the change can affect. Reformatting a file, or moving a definition
within its file, changes nothing.

```text
Changed since 3f2a9c1e04b7:
  weather::forecast::parse: tree, signature, body
    was: public fn parse(text: String) -> Forecast
    now: public fn parse(text: String) -> Result[Forecast, ParseError]
    read by: weather::main::main, weather::forecast::test "parses a day"

Tests whose code changed: 1
  weather::forecast::test "parses a day"
```

### `truss references` and `truss dependencies`

```text
truss references [--json] NAME
truss dependencies [--json] NAME
```

List the dependents or the dependencies of a definition, by part, such as
`weather::main::main: its body reads the signature of
weather::forecast::parse`. `NAME` is a full path or a suffix of one. The
answers come from the code database's dependency graph, so a use through a
method that type checking resolved, or through an `impl`, is found as well
as a use by name.

### `truss explain`

```text
truss explain [--json] FILE:LINE:COLUMN
```

Describes the name or expression at a position: its referent, its type, and
the signature of its definition, so an agent can ask about one name without
reading the file around it.

### `truss overlap`

```text
truss overlap [--with BRANCH] [--merge] [--json]
```

Lists where the worktree's changes overlap another worktree's, or a
branch's: both change the same part, or one depends on a part the other
changes (see [DATABASE.md](DATABASE.md#parallel-work)). git merges such
changes cleanly, and the result does not compile. **`--merge`** also checks
the merge result, without committing it, and lists the diagnostics that only
the merge result has.

### `truss rename`

```text
truss rename [--json] FROM TO
```

Renames a definition, a method with every version of it, or a module, and
rewrites every reference to it in the project. Renaming a module moves the
files of its directory; a subdirectory is a module of its own and stays.
The rename is checked in a
trial first, and is rejected with no file changed if the result has any
diagnostic, such as a name that is taken. Solver answers and test results
are keyed without names, so a rename proves and tests nothing again.

## Registry packages

The rules of the registry, the lock file, and versions are in
[PACKAGES.md](PACKAGES.md). Only `add` and `upgrade` choose versions; every
other command builds with the versions in the lock file, and fetches a
package's files into the store if it lacks them.

### `truss add`

```text
truss add [--json] PACKAGE...
```

Adds each package as a dependency of the current package, with a manifest
entry that grants it nothing, since a grant is a choice someone makes, and a
lock file line at the registry's newest version, or at the version written
after `@`, as in `truss add acme::geometry@1.4.2`. It prints the packages
that entered the build.

### `truss upgrade`

```text
truss upgrade [--json] [PACKAGE...]
```

Changes every registry package of the build to its newest version, or only
the named packages. The new versions are checked in a trial before the lock
file is written, and the command prints:

- **The lock file changes:** each package that changes version, enters, or
  leaves, and each package that would hold a capability it lacks now.
- **The changed signatures that the project depends on,** with the project's
  definitions that read them. These are the only places to review: if every
  signature the project reads is unchanged, only bodies changed.
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

### `truss publish`

```text
truss publish [--json]
```

Publishes the current package to the registry if it meets PACKAGES.md's
rules for [the registry](PACKAGES.md#the-registry) and
[versions](PACKAGES.md#versions). A dependency that is a package of the
project counts as published when its files match a version the registry
holds, so a project's packages are published one after another. An
incompatible release is rejected with each incompatible definition and the
name to publish under instead:

```text
This release is incompatible with `acme::geometry` 1.4.2, so it cannot be published under that name:
  acme::geometry::vector::length changed its parameters or its result.
    was: public fn length(self) -> Float64
    now: public fn length(self, scale: Float64) -> Float64
Publish it under a new name, such as `acme::geometry_v2`.
```

## The language server

```text
truss lsp
```

Speaks the Language Server Protocol on standard input and output. After each
change it reports the diagnostics `truss check` would report for the open
files with their unsaved text, prover diagnostics included. It checks in a
trial that starts from the worktree's session, so an edit costs O(change).
It also sends each obligation's state, so an editor can mark proven and
unproven code, and show which proofs rely on running code.

## Creating a package

```text
truss new NAME
```

Creates a directory with a `truss.toml` and a `main.truss` with an empty
`main`:

```truss
fn main(arguments: List[String]) -> ExitCode {
  ExitCode.success
}
```

A library is a package without `main`, so it needs no flag: delete the file.

## The background process

A command that reads code asks its project's background process
([DATABASE.md](DATABASE.md#the-background-process)), and starts it if it is
not running. The process runs the same command-line code, so the result is
the same as in the client's own process. `truss new` and `truss clean` read
no code, so they always run in the client's process.

**`TRUSS_CFLAGS`** adds flags, separated by spaces, to every command
that compiles or links C, for working on the compiler. Set to a sanitizer's,
such as `-fsanitize=address,undefined`, it finds compiler bugs, since a
memory error or undefined behavior in Truss code can come only from one.
The flags are part of each object's key and each test result's key. The
client sends its value to the background process with each command.

## Left out

- **`truss explain CODE`,** which rustc has. A diagnostic's message, notes,
  and fixes are meant to say everything needed to act on it, and a second
  text for each code would be a second place to keep up to date.
- **A watch mode.** The background process already updates every open
  worktree's session as its files change, so running a command again is as
  fast as a watch would be.
- **Selecting tests by changed files,** as Nx's `affected` does. The cache
  already runs exactly the tests whose code changed, so a selection by
  changed files could only be less precise.

## Not built

- Comparing contracts semantically in `truss publish`, which compares
  clauses by their text.
- The registry checking a release itself.
- A registry served over a network. Stage0's registry is a directory named
  by `TRUSS_REGISTRY`, with no owners, log, or signatures.
- Listing in `truss upgrade` the tests whose code an upgrade changes.
- Checking a package against the Truss version it names.
- `truss fmt [--check] [FILE...]`, which waits for the formatter.
- Code actions, hover, and go-to-definition in `truss lsp`.
- Renaming a field or a variant with `truss rename`.
- Listing the obligations to prove again in `truss impact`.
