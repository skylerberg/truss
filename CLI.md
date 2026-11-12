# Truss Command Line

This document describes `truss`, the one program people and agents run to
work on Truss code, in [`stage0/cli/`](stage0/cli): checking, testing,
running, building, and the tools that let an agent see a change's
effects. It follows [GOALS.md](GOALS.md) and the decisions in
[DESIGN.md](DESIGN.md), and drives the stages that
[TYPECHECKER.md](TYPECHECKER.md), [PROVER.md](PROVER.md), and
[CODEGEN.md](CODEGEN.md) describe, through the code database that
[DATABASE.md](DATABASE.md) describes.

## Principles

- **One program.** Every tool a user of Truss runs is a subcommand of
  `truss`, as with `go` and `cargo`, so there is one thing to install, one
  version to report, and one place to load a package. The other parts of the
  compiler, the code database among them, are libraries with no command line
  of their own: they answer with data, and every command, report, and exit
  status is this program's. Tools for working on the compiler itself, which
  are not shipped, are separate programs in `stage0/tools/`.
- **Every command is O(change).** Each command asks the same query database
  for its results, so running the whole package's checks and tests after a
  small edit does a small amount of work. Commands therefore act on the whole
  package by default and seldom need a target. Go and
  Cargo grow flags for picking packages and tests because running everything
  is slow; Truss leaves most of those out.
- **No warnings, no levels, no configuration of checks.** Every diagnostic is
  an error, as DESIGN.md decides, so there is no `-W`, no `--deny`, and no
  lint configuration. A command either succeeds or reports the problem.
- **Built for agents as much as for people.** Every command that reports
  something can report it as JSON, with stable diagnostic codes and exact
  fixes as byte ranges. The agent-facing commands, `holes`, `show`, `impact`,
  and `rename`, come from GOALS.md's "LLM-friendly" principle: tools that report
  a change's effects, show the signatures that matter, and change code in
  structured ways.
- **The same answer every time.** A command's output depends only on the
  code, the toolchain, and, for `run` and external tests, the world. It does
  not depend on whether a background process was running, the cache's contents,
  or how many cores the machine has. The exceptions are the facts that
  describe the run itself: which test results came from the cache, and how
  long things took.

## Commands

| Command | Does |
|---|---|
| `truss check` | Reports every diagnostic in the packages, and where the worktree's changes meet other worktrees'; `--fix` applies the fixes that have no alternative, and `--no-proofs` leaves out the prover |
| `truss test` | Checks the packages, then runs the tests whose results are not kept |
| `truss run` | Checks the package, builds its program for development, and runs it |
| `truss build` | Checks the package and builds its program for release, refusing any `todo` or `echo` `main` can reach |
| `truss holes` | Lists every `todo`, with its type, the names in scope, and the work it blocks |
| `truss show` | Prints the signatures of a package, module, type, or definition |
| `truss impact` | Lists the definitions the worktree's changes from a base commit modify, and their dependents |
| `truss references`, `truss dependencies` | Lists a definition's readers, or its dependencies, part by part |
| `truss explain` | Describes the entity at a position: a name's meaning, its type, and the signature it refers to |
| `truss overlap` | Lists where the worktree's changes meet other worktrees', or a branch's |
| `truss rename` | Renames a definition, method, or module, and every reference to it in the worktree |
| `truss add` | Makes registry packages dependencies of the package, and writes their versions in the lock file |
| `truss upgrade` | Moves the project's registry packages to other versions, and reports the effects |
| `truss publish` | Adds the package to the registry as its next version, once it is finished and breaks nothing |
| `truss new` | Makes a new package |
| `truss sync`, `truss status`, `truss stop` | Brings a worktree's session up to date, lists the background process's sessions, and stops it |
| `truss clean` | Stops the background process and deletes the store |
| `truss lsp` | Runs the language server for an editor, on standard input and output |

`truss --version` prints the version of Truss the toolchain is, which a
package's `truss` is compared with, and the version of each stage that has
one: code generation and the Unicode tables. Those are the versions in exact keys, so a
report of a stale result can say which stage it came from. Every other
result is kept under the compiler's identity, the hash of its executable.

### Finding the packages

A command acts on the packages of the project it is run in, through that
project's session in the code database, as DATABASE.md's "Sessions"
describes. The project's root is the nearest directory at or above the
current one whose `truss.toml` has a `[project]` table, or with none, the
nearest that holds a `truss.toml`, which is a package that is a project by
itself, as SYNTAX.md's "Projects" says. Cargo finds a workspace the same
way. A directory with no manifest at or above it is in no project, and a
command there cannot do its job. The command is about the packages at or
under the current directory, or else the one it is in, so running in a
package's directory, or any directory below it, is about that package, and
running at the root of a project of several packages is about all of them.
`run` and `build` need exactly one, and say so when there are more.
`-C DIRECTORY`, as in `git` and `make`, runs as if from that directory,
written before the command or after it. The positional arguments are free
for each command's targets.

A package's modules are the `.truss` files under its directory, as
SYNTAX.md says, with two exceptions:

- **A directory with its own `truss.toml` is another package,** and none of
  its files are modules of this one, as with Cargo's and Go's nested
  modules. It is a package of the same project, unless its manifest has a
  `[project]` table, which makes it and everything under it another
  project, or the root has none, which makes the root a project of one
  package.
- **Directories whose names start with `.`, and `_build` and
  `node_modules`, are skipped,** so `.git` and an editor's hidden
  directories are never read.

A package's dependencies are found among the project's packages, by name,
and then among the registry's, at the versions the project's lock file
gives (see [Registry packages](#registry-packages)).

An error in a manifest is a problem in the code, reported with the
diagnostics, and the exit status is 1:

- a manifest that cannot be read, with the line
- a package name used twice in the project, or the name `standard`
- a package without `truss`, or written for a newer Truss than the
  toolchain's, which `truss --version` gives
- a dependency that is no package of the project and that the lock file
  gives no version, a package that depends on itself, and packages that
  depend on each other in a cycle
- a lock file that cannot be read, that names a package whose files cannot
  be had, or that is not the one the manifests give
- a package that runs on every target with a dependency that says
  `usize_bits = 64`
- a package name of one part that is the owner in another package's name,
  since a path that starts with it could then be read two ways
- a `[test]` table in a manifest that is not the project's
- a grant that names no capability
- a dependency that nothing in its package uses

The last two need the package's code, as TYPECHECKER.md's "The manifest"
describes, and are reported for the packages the command is about.

### Common options

- **`--json`** writes one JSON document to standard output in place of the
  report for people, for every command except `run`, `new`, and `clean`,
  whose output is a program's or nothing.
  Its fields are listed with each command. Every document has
  `"format": 1`, which changes only when a field is removed or changes
  meaning, and `"diagnostics"`, an array of diagnostics as
  `Diagnostic.to_json_object` writes them, with each one's file; a command
  that reads code adds `"problems"`, the manifests that could not be read. A
  command that stops at diagnostics still writes its document.
- **`-C DIRECTORY`**, above.
- **`--no-server`,** before or after the command, or `TRUSS_NO_SERVER=1`,
  runs the command in its own process, not in the background process (see
  [The background process](#the-background-process)).

There is no `--quiet` or `--verbose` beyond the options a command lists. Reports
for people are plain text. Color, when it comes, belongs only on a
terminal, and never when `NO_COLOR` is set, so it needs no option either.

Every position a command shows names its file as the current directory
reaches it, such as `forecast.truss` or `../weather/forecast.truss`, so a
terminal or an editor can open it. A development build's program reports
its own positions the same way, so a failed test's message matches the
diagnostics. A release build names files from the package's root, as
`weather/forecast.truss`, so the program is the same wherever it was
built.

### Output streams and exit status

- **A command's output goes to standard output:** a test report, a
  list of holes, signatures, a JSON document. **Diagnostics for people go
  to standard error,** as rustc, Go, and Cargo send them, so that `truss run`
  can give its program's output alone on standard output. With `--json`,
  diagnostics are inside the document on standard output, and standard error
  is empty unless the command could not run.
- **Exit status:**

  | Status | Means |
  |---|---|
  | 0 | The command succeeded, and the code had no problem |
  | 1 | The code has a problem: a diagnostic, a failed test, a build refused for a `todo` |
  | 2 | The command could not do its job: a bad argument, a path that names nothing, no `truss.toml`, no C compiler, a compiler bug |

  `truss run` exits with its program's
  status once the program starts, as `go run` and `cargo run` do; before
  that, it exits as above.

## Checking

```text
truss check [--fix] [--no-proofs] [--json]
```

`truss check` runs every stage that can report a diagnostic: lexing,
parsing, name resolution, type checking, ownership, capabilities and
dependency grants, package-wide checks, and proofs.
Proofs are checked by default because DESIGN.md makes every promise in a
signature something the compiler proves, so a package whose proofs have not
been checked has not been checked. A dependency's proofs are the program's
too, so `check` also checks and proves every package that the command's
packages depend on, except the standard library. A file is proven once it
type-checks, since the prover reads the type checker's output. Proving needs
the pinned solver, as `run` needs a C compiler. Code generation reports
nothing, so `check` builds only the checks of tagged templates, which
PROVER.md's "Running code while proving" runs, kept under the key of their
code as test results are. `test` and `run` do not wait for proofs, as
DESIGN.md's "Tests do not wait for proofs" says.

**`--no-proofs`** stops before the prover. It reports every other stage's
diagnostics, in the command's packages only, and needs no solver. Proofs are
cached and modular, but a fresh session, a changed contract that many callers
rely on, or a new dependency can still leave much to prove, and type errors
are the first thing to fix. Dafny's `resolve` against `verify`, Verus's
`--no-verify`, and F\*'s `--lax` give the same choice. A package is checked
only once `check` without the flag is clean, which `build` and `publish`
require.

It prints each problem with the manifests, then each diagnostic as
`Diagnostic.render` does, at most `Diagnostic.limit` of them in each file,
then the prover's diagnostics, and then a count. The prover runs only after
every other diagnostic is printed, so type errors show while the solver
works. The JSON document is `{"format", "diagnostics"}`.

**`--fix`** applies every fix that is the only fix its diagnostic offers,
writes the files, checks again, and repeats until no such fix is left, then
reports the remaining diagnostics. Two fixes whose edits overlap are not
applied in the same round, since applying both could give a result neither
intended; the second
waits for the next round, after the file is checked again. Rounds stop
after 32, so fixes that undo each other cannot run forever. A diagnostic with several fixes, such as an addition
that may overflow, which offers four, is a choice for the person or agent,
so it is reported and left alone. A dependency that nothing uses has one
fix, which deletes its entry from the manifest, and `--fix` applies it. A
capability that is not granted has none: `--fix` never widens a grant, as
DESIGN.md's "Dependencies" decides. An agent that has chosen applies the
fix's edits from the JSON itself. This follows `ruff check --fix` and
`eslint --fix`, which put fixing on the checking command, rather than
Cargo's separate `cargo fix`; a separate command would load and check the
package exactly as `check` does. The JSON document adds `"fixed"`, the
diagnostics whose fixes were applied.

A check also lists, on standard output, where the worktree's changes meet
those of other worktrees of the repository that the background process has
open, as [`truss overlap`](#truss-overlap) does. Overlaps are not
diagnostics: nothing is wrong with either worktree's code, so they do not
change the exit status. The JSON document has them as `"overlaps"`.

## Testing

```text
truss test [--match TEXT] [--timings] [--rerun] [--json] [FILE_OR_DIRECTORY...]
```

`truss test` checks the package, stopping at any diagnostic, and then runs
its tests as CODEGEN.md's "Tests" describes: one test program, a worker per
core, and results kept by the key of the code each test can run. A test
whose result is kept is not built or run again. External tests, those with
`uses`, run every time, as SYNTAX.md requires.

- **Which tests.** All of them, by default, which is cheap because results
  are cached. Files and directories narrow the run to the tests defined in
  them, and `--match TEXT` to the tests whose name contains the text. There
  is no way to skip external tests: DESIGN.md has them run every time the
  suite runs.
- **Progress.** While the tests build and run, a status line on standard
  error, redrawn as each test starts and ends, shows how far the run has
  got, how many have not passed so far, how long the tests have been
  running, and the test that has been running longest, as Bazel's and
  nextest's do:

  ```text
  [ 97/143] 1 not passed · 0.6s · running weather::parse "reads hourly rows" (0.4s)
  ```

  Before the tests run it shows the build instead: lowering, then the C
  files compiled out of those that were not cached. The line is drawn only when standard error is a
  terminal and is erased when the run ends, so logs and CI output hold only
  the report. It is never on standard output, and never with `--json`.
- **The report** lists every test that did not pass, with its outcome, its
  message, and its `echo` output indented under it, in the order of the
  tests, and then a count of each outcome, how many passes came from the
  cache, and how long the run took:

  ```text
  weather::forecast "rain chance is a percentage": failed
      assert failed at forecast.truss:41:3
  weather::parse "reads hourly rows": incomplete
      todo at parse.truss:18:15

  141 passed (139 cached), 1 failed, 1 incomplete in 1.4s (check 0.1s, build 0.9s, tests 0.4s)
  ```

  Passing tests are left out, as `go test` leaves them out, because after a
  small edit nearly every test passes from the cache, and a list of them
  hides the few lines that matter. The report is in the order of the tests,
  never in the order they ended, so two runs of the same code give the same
  report apart from durations.
- **`--timings`** lists every selected test, passing or not, with how long
  it took, slowest first, after the report. A cached test shows the
  duration of the run that kept its result, marked `cached`, so the list
  shows the whole suite's cost, not only this run's:

  ```text
  2.31s  weather::forecast "a year of hourly data"
  420ms  weather::parse "reads hourly rows"
   87µs  weather::render "renders an empty report"  cached
  ```

  A duration is the test's time in its worker, from being handed the test to
  its end, which leaves out the build and the wait for a free worker.
- **Outcomes** are those of the test program: `passed`, `failed`,
  `panicked`, `incomplete`, `timed_out`, and `crashed`. **Every outcome but
  `passed` fails the run,** with exit status 1. A test written before the
  code it tests, as DESIGN.md allows, turns the suite red until that code is
  written, which is the red and green of test-first development. `incomplete`
  stays its own outcome, so the report says which tests wait on a `todo` and
  which are wrong, and `truss holes` lists the work each `todo` blocks.
- **`--rerun`** runs every selected test, using no kept results and keeping
  new ones, as `go test -count=1` does. Results are deterministic, so this
  is only for doubting the cache, after a suspected compiler bug, or for
  timing every test on this machine now.
- **The time limit** for each test is its project's, set in the project's
  manifest as `[test] time_limit = 10`, in seconds, with 10 as the default.
  It is not a flag, so that every machine and CI run uses the same limit. A
  run over several packages builds one test program for each.
- **The JSON document** is `{"format", "diagnostics", "tests", "timings"}`,
  where each test is `{"module", "name", "file", "line", "outcome",
  "cached", "microseconds", "message", "echo"}`, for every selected test,
  passing or not, and `"timings"` gives the microseconds of the check, the
  build, the tests, and the whole run. When the package has diagnostics,
  each test has only its name and place.

## Running and building

```text
truss run [--release] [--] [ARGUMENT...]
truss build [--output PATH] [--json]
```

A package's program starts at the `main` of its `main` module, as DESIGN.md's
"Packages" says, and a package compiles to a single program or library, as
IMPLEMENTATION.md has it. A package without that `main` is a library and
has no program, so `run` and `build` stop with 2. A function named `main` in
another module is an ordinary function.

**`truss run`** builds a development program, as CODEGEN.md's "C files and
optimization" describes, and runs it on the terminal with the arguments, so
it can prompt and read, then exits with its status. When the background
process builds it, it builds it in the store and the command runs it on its
own terminal, since the process has none. `echo` writes to
standard error, as SYNTAX.md says. A `todo` that `main` can reach is
refused, as in `build`: DESIGN.md rules out a `todo` that panics when
reached, since that would be a failure the signature does not show, and that
holds for a development run too. The first argument that is not an option
starts the program's arguments, and `--` marks the start when the first one
begins with `-`. **`--release`** builds as `truss build` does, refusing an
`echo` as it does, for timing the program.

**`truss build`** builds a release program, as CODEGEN.md's "C files and
optimization" describes: at `-O2`, optimized across every file as they are
linked, with ThinLTO where the C compiler is clang. It refuses a program
whose proofs are not done, as `check` reports them, and one whose `main` can
reach a `todo` or an `echo`, in code or in a proof, and lists each one, a
`todo` in code with the definitions on the way from `main` to it:

```text
render.truss:12:14: `todo` can be reached from `main`, so the program cannot be built.
    weather::main::main -> weather::render::render
``` Since every proof the program reaches is done, the program has none
of the run-time checks of a test build, as CODEGEN.md's "Test builds check
instead of waiting for proofs" says; `run --release` keeps them, since it
does not wait for proofs. The program is written to `--output`, or else
to a file named after the package in the current directory, as `go build`
does. Truss keeps every intermediate file in its cache, so there is no build
directory in the package, and nothing to add to `.gitignore` but the
program. The JSON document is `{"format", "diagnostics", "output"}`, or
`{"format", "diagnostics", "unshippable"}` when it refuses, each with its
kind, `todo` or `echo`, its file, line, and column, and its way from
`main`.

Building for another target, which CODEGEN.md allows through the target's
`USize`, would add `--target` to `build`. Stage0 builds for the host only.

## Tools for agents

These commands answer the questions that GOALS.md says dominate fast
development: unfinished code, a definition's contract, a change's
effects, and how to change a name everywhere at once.

### `truss holes`

```text
truss holes [--json] [FILE_OR_DIRECTORY...]
```

Lists every `todo` in the package, or in the named files, as DESIGN.md's
"Unfinished code" asks: its position, the type it must have, the names in
scope with their types, and the work it blocks, which is `main`, if `main` can
reach it, and each test that can. A `todo` in a theorem or a `proof` block
is a hole in a proof, listed the same way. Each hole is a task a person or
agent can take on its own. A type defined as `todo` is listed too.

```text
render.truss:12:14: hole of type String
    in scope: header: String, report: Report
    blocks: main; test weather::render "renders an empty report"
```

A `todo` whose type nothing fixes, such as one inside an interpolation, is
listed as "not decided yet". Name resolution records the names in scope at
each `todo`, and the type checker's tables give their types, through the `Inspect`
library. A hole blocks every test, and `main`, that reaches the
hole's definition through the definitions' reads, which the code
database keeps. The JSON document is
`{"format", "diagnostics", "holes"}`, each with its definition, file, line,
and column, its kind, `value` or `type`, its type, its names in scope with
their types, and the work it blocks. Listing holes is not a failure, so the
exit status is 0 unless the package has diagnostics.

### `truss show`

```text
truss show [--body] [--json] PATH...
```

Prints the signatures at each path, each after its file and line. A
signature is the definition's text with every body left out.

- for a definition, such as `weather::forecast::parse`, its signature with
  every clause: generic parameters, parameters with their defaults, the
  return type, `uses`, `cost`, `requires`, `ensures`, and `decreases`
- for a type, such as `weather::forecast::Forecast`, its definition, its
  `derives`, and the signatures of its methods and of the `impl`s in its
  package
- for a method, `weather::forecast::Forecast.summary`
- for a module, `weather::forecast`, every definition's signature, and for
  a package, `weather`, every public one

A module of another package, such as `standard::list`, shows only the parts
visible from this one, so an opaque type's fields stay hidden. A path that
names nothing visible is a bad argument, so the exit status is 2. `--body` prints whole definitions. Truss
has no comments, so a signature is the whole of a definition's
documentation, which makes this Truss's `go doc`. GOALS.md asks for tools
that give an agent the signatures it needs without whole files, and this is
that tool. The JSON document is `{"format", "diagnostics", "definitions"}`,
each with its path, its kind, its file and line, and its text.

### `truss impact`

```text
truss impact [--base REVISION] [--json]
```

Compares the worktree as it is with a base commit: the one `--base` names,
or else where the worktree's branch left the default branch, so that it
shows every change of the branch, uncommitted ones included. The code
database compares the two sessions, as DATABASE.md's "Comparing two states"
describes:
every result a changed file can reach is brought up to date in both and
compared, so a part checked again that came out the same is told apart
from one that changed, and reformatting, or moving a definition within its
file, changes nothing. For each definition that was added, removed, or
changed, it shows:

- **The parts that changed,** such as its tree, its signature, or its body.
- **For a changed signature,** the old and new one, since a
  reviewer must read those closely, and every definition that reads it, which are
  the callers to review.

Then it lists the tests whose code changed, which are the only tests the
change can affect, each with whether its result is already kept, so an
agent knows the cost of its change before running anything.

```text
Changed since 3f2a9c1e04b7:
  weather::forecast::parse: tree, signature, body
    was: public fn parse(text: String) -> Forecast
    now: public fn parse(text: String) -> Result[Forecast, ParseError]
    read by: weather::main::main, weather::forecast::test "parses a day"

Tests whose code changed: 1
  weather::forecast::test "parses a day"
```

A definition is matched with its earlier self by its path, so a renamed
definition is listed as removed and added. Two agents on the same
repository can each run it and compare the dependents of their changes, and `truss overlap`
does that for them. The JSON document is `{"format", "diagnostics",
"problems", "base", "changes", "tests"}`, where each change has its path,
`added`, `removed`, or `changed`, the parts that changed, its signature
before and after, and its readers, with the parts on each side.

### `truss references` and `truss dependencies`

```text
truss references [--json] NAME
truss dependencies [--json] NAME
```

List a definition's readers, or its dependencies, part by part,
such as `weather::main::main: its body reads the signature of
weather::forecast::parse`. `NAME` is a full path or the end of one, such
as `parse` or `Forecast.summary`, and names every definition it matches.
The answers come from the graph the code database keeps, so they are
exact: a read through a method chosen by type checking, or through an
`impl`, is found as well as one written by name.

### `truss explain`

```text
truss explain [--json] FILE:LINE:COLUMN
```

Describes the entity at a position, as diagnostics give positions: the
name or expression there, a name's meaning, its type, and the signature of the
definition it refers to, so an agent can ask about one name without
reading the file around it.

### `truss overlap`

```text
truss overlap [--with BRANCH] [--merge] [--json]
```

Lists where the worktree's changes from its common commit with another
meet the other's, as DATABASE.md's "Parallel work" describes: a part both
change, or a change of one that depends on a change of the other, such as a
new call to a function whose signature the other changes, which git merges
cleanly and which breaks once merged. It compares with every other worktree
of the repository that the background process has open, or with `--with`,
a branch. **`--merge`** also checks a merge of the two, without making it,
and lists the diagnostics the merge would have that neither side has.

### `truss rename`

```text
truss rename [--json] FROM TO
```

Renames a definition, every version of a method, or a module, and rewrites
every reference to it in every package of the project, whichever directory
it is run from. `TO` is a new name, as in `truss
rename weather::forecast::parse read`, or a full path that keeps the
definition in its module and a method with its type. Renaming a module, as
in `truss rename weather::forecast weather::outlook`, moves its file, and
every `use` of it and every full path to it changes. The rename is made in
a trial, a state that starts from the worktree's session and holds only
the rename's changes, and is checked there first; it is refused, changing nothing, if it would
cause any diagnostic, such as for a name that is taken, breaks a naming
rule, or would hide another, which are the diagnostics a hand-made rename
would cause. A worktree that already has diagnostics is refused too, since its
references are found through checked code. References in packages outside
the project cannot be changed, so renaming a public definition changes the
package's public interface, which `truss impact` reports like any other
changed signature. Each edit replaces the name's tokens alone, so the files
need no formatting afterward. The callers of the renamed definition are checked
again, but nothing is proven or tested again: a solver's answer and a
test's result are kept under keys that hold no names. Renaming a local
variable is left to the language server, which has the
cursor's position. The JSON document is `{"format", "diagnostics", "edits",
"moved"}`, with each edit's file, byte range, and replacement.

## Registry packages

A package whose name has an owner, and that is no package of the project,
comes from the registry, as DESIGN.md's "Packages" describes.

- **The registry is a directory,** which `TRUSS_REGISTRY` names. It holds,
  for each package, `owner/name/versions`, a line for each version with the
  hash of its files, the oldest first, and `owner/name/VERSION/`, the files
  published as that version. A registry is only added to. A command sends
  the registry its own environment names to the background process, so the
  answer does not depend on how that process was started.
- **A build's versions come from `truss.lock`,** at the project's root, and
  from the records of the packages it names, as SYNTAX.md's "The lock file"
  and DESIGN.md's "Choosing versions" say: for each package, the highest
  version that the lock file or any package of the build names. No command
  but `add` and `upgrade` chooses a version.
- **A package's files are fetched when the build does not have them,** from
  the registry into the store, in a directory named by their hash, and are
  kept only if they have the hash the lock file names. Fetching changes no
  answer, so any command does it. A package that is in the store needs no
  registry.
- **A registry package is checked as far as the project reads it,** like
  any code: the signatures the project's code uses, and the bodies its
  programs and tests reach. Its own tests are not the project's, and
  `truss test` does not run them.
- **The lock file is written one way.** It has a line for each registry
  package the build uses and no other, at the build's versions, with the
  capabilities each holds. One that differs is a problem that says how,
  and `truss check --fix` writes the one the manifests give. That never
  chooses a version: a dependency that no lock file and no record gives a
  version is a problem that says to run `truss add`.

### `truss add`

```text
truss add [--json] PACKAGE...
```

Makes each package a dependency of the package the command is run in. It
writes an entry in the manifest that grants the package nothing, since a
grant is a choice someone makes, and a line in the project's lock file at
the registry's newest version, or at the one written after `@`, as in
`truss add acme::geometry@1.4.2`. The packages it depends on come with it,
at the versions it was published with, unless the build already has newer
ones. It prints the packages that entered the build. A package the registry does not hold
is a bad argument, and nothing is written. The JSON document is `{"format",
"diagnostics", "changes", "signatures", "breaks"}`, as `upgrade` writes it.

### `truss upgrade`

```text
truss upgrade [--json] [PACKAGE...]
```

Moves every registry package of the build to its newest version, or only the
packages named, each to its newest or to the version written after `@`. The
other versions follow as a build's do, so a package named may bring newer
versions of its dependencies. A version can be asked for that is lower
than the build's, and is the build's only if no package of the build was
published with a higher one.

The new versions are checked before the lock file is written, in a state of
their own that starts from the project's session and holds their
changes, as a rename is checked. The command prints:

- **The lock file's changes:** each package that moves, enters, or
  leaves, and each that would hold a capability it did not.
- **The signatures the project reads that change,** each as it was and as it
  would be, with the project's definitions that read it. These are the
  places to review, and no others: a package whose signatures the project
  reads are all unchanged can only have changed its bodies' results.
- **The errors the project would have that it does not have now.**

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
have new errors, since the code then has a problem, and 0 otherwise. The
JSON document is `{"format", "diagnostics", "changes", "signatures",
"breaks"}`: each change with its kind, `moved`, `entered`, `left`, or
`holds`, its package, and its versions or the capabilities gained, each
signature with its path, its text before and after, and its readers, and
each error as a sentence.

### `truss publish`

```text
truss publish [--json]
```

Adds the package the command is run in to the registry, as DESIGN.md's
"Versions" and "The registry" describe. The package must have an owner in
its name. It is published only when:

- **It has no errors,** proofs included, and no problem with its manifest or
  the lock file.
- **It has no `todo` and no `echo`,** anywhere, since a library has no
  `main` to reach them from. Each is listed with its place.
- **Its tests that have no `uses` pass.** They are run as `truss test` runs
  them, so a result that is kept is not run again.
- **It is published with registry packages only.** A dependency that is one
  of the project's packages counts as the registry's when its files are
  those of a version the registry holds, which is how a project's packages
  are published one after another, and otherwise is to be published first.
- **It breaks nothing its last version offers** (below).

A release publishes the package's files, as SYNTAX.md's "The lock file"
lists them: its manifest as it is written, its modules, and the Markdown
files beside them, with a lock file in place of the project's that has a
line for each registry package the package's code uses, its tests apart,
and for each that those use in turn, at the build's versions. A dependency
that only tests use is left out, so that a project that uses the package
does not take it on. Files that are the newest version already are not
published again.

**The number is the registry's to give,** as DESIGN.md decides. The first
version is 1.0.0, or 2.0.0 for a name that ends in `_v2`. After that, the
package is compared with its newest version, which is loaded into a state
of its own with the packages it was published with:

- A release that breaks something is refused, with each definition that
  breaks, the reason, and its signature as it was and as it is, and
  the name to publish it under.
- A release that offers more gets the next minor number, and the additions are
  listed.
- Any other gets the next patch number.

```text
This would break the API of `acme::geometry` 1.4.2, so it cannot be published under that name:
  acme::geometry::vector::length has other parameters or another result.
    was: public fn length(self) -> Float64
    now: public fn length(self, scale: Float64) -> Float64
Publish it under a new name, such as `acme::geometry_v2`.
```

The comparison is of every public definition and every `impl`:

| Of | Breaks | Offers more |
|---|---|---|
| Any public definition | It is gone, moved, or no longer public | It is new |
| A function, method, or theorem | Other generic parameters, parameters, or result; a capability more in `uses`; a `requires` clause more; an `ensures` or `cost` clause fewer; a `time` clause gone; a default gone; a yielding method that could be pulled and no longer can | A capability fewer; a `requires` clause fewer; an `ensures` or `cost` clause more; a default more; a yielding method that can be pulled where it could not |
| A type that shows its fields | Other fields, variants, or invariant; `opaque` added; a derived trait fewer | A derived trait more |
| An opaque type | Other generic parameters; a derived trait fewer | `opaque` taken away; a derived trait more |
| A trait or capability | Other generic parameters, required traits, associated types, or laws; a method gone or changed as a function's may not; a method more without a body | A method more with a body |
| A constant | Another type or value | |
| An `impl` | It is gone | It is new |
| The package | `usize_bits = 64` where it ran on every target | |

Types are compared as the checker inferred them, so a type written
through another `use` is the same type. The exit status is 1 when the
package is not published, and the JSON document is `{"format",
"diagnostics", "problems", "package", "version", "hash", "grows"}`, each
entry of `grows` being `{"path", "addition"}`, or with
`"refused"`, the sentences that say why.

## The language server

```text
truss lsp
```

Speaks the Language Server Protocol on standard input and output, for an
editor. It holds the text of each file the editor has open and, after each
change, reports the diagnostics `truss check` would report of the open files
with that text in place of the files on disk. Nothing is written to a file.

- **The check runs where commands run:** in the project's background
  process, or with `--no-server` in the server's own process. It reads a
  trial session, which starts from the worktree's session and replaces the
  open files, so an edit costs only its changes.
- **Each open file's diagnostics** are published as
  `textDocument/publishDiagnostics`, with a diagnostic's notes as related
  information. A file's proofs are checked once it has no other
  diagnostic, as `truss check` checks them.
- **Each obligation's state** is sent as a `truss/proofStates`
  notification: for each open file, every obligation's range, its code,
  its goal, whether it is proven, and whether its proof trusts
  compiled code, for an editor to mark proven and unproven code apart and
  to show which proofs rely on running code.
- **Positions count UTF-16 code units,** the protocol's default, or bytes
  where the client offers `utf-8` among its position encodings.
- **A burst of changes is checked once:** a check waits until no message
  is waiting.

The server asks for each change as the whole text, and also accepts
ranges. It answers `initialize`, `shutdown`, and `exit`, and every other
request with the error that it is not supported.

## Making a package

```text
truss new NAME
```

Makes a directory with a `truss.toml` that names the package and the
toolchain's Truss, and a `main.truss` with an empty `main`:

```truss
fn main(arguments: List[String]) -> ExitCode {
  ExitCode.success
}
```

A library is a package without `main`, so it needs no flag: delete the
file. The name must be a package's, a `lower_snake_case` name or an owner
and a name, such as `acme::weather`, since it starts every module path. The
directory is named after the package without its owner. Made under a
project's root, the package is one of the project's.

## The background process

A fresh process must at least read every file to learn which changed, which
costs O(files). A long-running process that watches the files and keeps
results in memory makes each command O(change). The code database's
background process is that process, as DATABASE.md's "The background
process" describes, and the command line is its client:

- **A command that reads code asks its project's background process,
  and starts it if it is not running,** as Bazel and Gradle do. The project
  is the one the command's directory is in, which is the current directory
  or the one `-C` names. Each project has a process of its own, so commands
  in different worktrees are answered at once. The command sends the
  command line and the current directory, and prints the process's
  answer. It runs the command line's own code, from that
  directory, so the answer is the same as in the command's own process.
  A command's writes to standard error, such as the status line, comes
  to the command as it is written, and its output and exit status when it is
  done.
- **A process ends after three hours without a command,** when its
  project's directory is gone, or on `truss stop`, which stops every
  project's process. `truss status` lists the sessions of each. `truss sync` brings a worktree's
  session up to date and does nothing else.
- **`--no-server` and `TRUSS_NO_SERVER=1` run a command in its own
  process,** against the same store, for CI, where a process that lives past
  the job only gets in the way. Such a command is refused, saying why, while
  the background process has the worktree's session open.
- **`truss new` and `truss clean` always run in the command's own
  process,** since they read no code.

### The store

Sessions, test results, object files, and programs built to run are kept in
the code database's store, under `$TRUSS_CACHE`, or else
`$XDG_CACHE_HOME/truss`, or else `~/.cache/truss`, as DATABASE.md's "The
store" describes. Every entry is named by a key of its inputs, so
entries never go stale, the store collects old entries itself to keep within
its budget, and nothing in it is ever needed for a correct answer. **`truss clean`** stops the background process and
deletes the store, which only costs time.

## For working on the compiler

**`--sanitize`,** on `test` and `run`, builds with AddressSanitizer and
UndefinedBehaviorSanitizer and keeps no test results. A memory error in
Truss code can only come from a bug in the compiler, so any report is one.
It is left out of each command's help.

## Left out

- **`truss explain CODE`,** which rustc has. A diagnostic's message, notes,
  and fixes are meant to say everything needed to act on it, and a second
  text for each code would be a second place to keep up to date.
- **A watch mode,** such as `cargo watch` or `vitest --watch`. The
  background process already checks every open worktree as its files
  change, so running a command again does a watch's job, at once.
- **Selecting tests by the changed files,** as Nx's `affected` does. The cache
  already runs only the tests whose code changed, and exactly those, so a
  selection by files changed could only be less exact.

## Not built

- **A contract compared by its meaning.** DESIGN.md has a release keep a
  `requires` that the old one implies and an `ensures` that implies the old
  one, which is the prover's to show. `truss publish` compares a contract's
  clauses as they are written: one that is reworded breaks, and one whose
  words are the same and whose meaning changed, because a private
  definition it names did, is not seen.
- **The registry checking a release itself.** `truss publish` checks the
  package where it is run and writes to the registry's directory.
- **A registry that is not a directory.** DESIGN.md's registry is served
  over a network, keeps a public log of every version's hash, signs the
  proofs it computed, has owners who alone publish under their names, and
  can mark a release as one not to use. Stage0's is a directory that
  anyone who can write to it adds to, and a lock file's hash is checked
  against the files and against the records of the packages that name it,
  and against nothing else.
- **The tests whose code an upgrade changes,** listed by `truss upgrade` as
  `truss impact` lists them.
- **A package read as the Truss it names.** There is one version of Truss,
  so `truss` only says whether the toolchain is new enough.
- **`truss fmt [--check] [FILE...]`,** which waits for the formatter. It is
  to rewrite the package's files, or the named ones, into the one layout
  SYNTAX.md describes, and print the names of the files it changed, with no
  options for style. `--check` changes nothing and exits with 1, listing the
  files that are not formatted, for CI, as `gofmt -l` and `cargo fmt
  --check` do. A file with a syntax error is reported and left as it is.
  Formatting changes no definition, so it rebuilds nothing. `truss show` is
  then to print a signature as `truss fmt` writes it.
- **Code actions, hover, and go-to-definition in `truss lsp`.** A
  diagnostic's fixes are to be code actions, and `truss explain` and
  `truss references` are to answer hover and navigation.
- **Renaming a field or a variant** with `truss rename`.
- **Listing the proofs to check again** in `truss impact`, as it lists the
  tests whose code changed.
