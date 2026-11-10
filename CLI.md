# Truss Command Line

This document designs `truss`, the one program people and agents run to work
on Truss code: checking, testing, running, building, formatting, and the
tools that let an agent see what a change touches. It follows
[GOALS.md](GOALS.md) and the decisions in [DESIGN.md](DESIGN.md), and drives
the stages that [TYPECHECKER.md](TYPECHECKER.md) and
[CODEGEN.md](CODEGEN.md) describe, through the code database that
[DATABASE.md](DATABASE.md) designs. It is built in
[`stage0/cli/`](stage0/cli), which [`stage0/bin/truss.ml`](stage0/bin/truss.ml)
only starts, except `truss fmt` and `truss lsp`, which wait for the
formatter and the language server. The prover is not built either, so what
the commands will do with proofs is stated where it matters.

## Principles

- **One program.** Every tool a user of Truss runs is a subcommand of
  `truss`, as with `go` and `cargo`, so there is one thing to install, one
  version to report, and one place to load a package. The other parts of the
  compiler, the code database among them, are libraries with no command line
  of their own: they answer with data, and every command, report, and exit
  status is this program's. Tools for working on the compiler itself, which
  are not shipped, are separate programs in `stage0/tools/`.
- **Every command is O(change).** Each command asks the same query database
  for what it needs, so running the whole package's checks and tests after a
  small edit does a small amount of work. Commands therefore act on the whole
  package by default and seldom need to be told what to look at. Go and
  Cargo grow flags for picking packages and tests because running everything
  is slow; Truss leaves most of those out.
- **No warnings, no levels, no configuration of checks.** Every diagnostic is
  an error, as DESIGN.md decides, so there is no `-W`, no `--deny`, and no
  lint configuration. A command either succeeds or reports what is wrong.
- **Built for agents as much as for people.** Every command that reports
  something can report it as JSON, with stable diagnostic codes and exact
  fixes as byte ranges. The agent-facing commands, `holes`, `show`, `impact`,
  and `rename`, come from GOALS.md's "LLM-friendly" principle: tools that say
  what a change affects, show the signatures that matter, and change code in
  structured ways.
- **The same answer every time.** A command's output depends only on the
  code, the toolchain, and, for `run` and external tests, the world. It does
  not depend on whether a background process was running, what was cached,
  or how many cores the machine has. The exceptions are the facts that
  describe the run itself: which test results came from the cache, and how
  long things took.

## Commands

| Command | Does |
|---|---|
| `truss check` | Reports every diagnostic in the packages, and where the worktree's changes meet other worktrees'; `--fix` applies the fixes that have no alternative |
| `truss test` | Checks the packages, then runs the tests whose results are not kept |
| `truss run` | Checks the package, builds its program for development, and runs it |
| `truss build` | Checks the package and builds its program for release, refusing any `todo` or `echo` `main` can reach |
| `truss fmt` | Formats the packages' files (not built yet) |
| `truss holes` | Lists every `todo`, with its type, the names in scope, and what it blocks |
| `truss show` | Prints the signatures of a package, module, type, or definition |
| `truss impact` | Lists what the worktree's changes from a base commit change, and what they reach |
| `truss references`, `truss dependencies` | Lists what reads a definition, or what it reads, part by part |
| `truss explain` | Says what is at a position: what a name means, its type, and the signature it refers to |
| `truss overlap` | Lists where the worktree's changes meet other worktrees', or a branch's |
| `truss rename` | Renames a definition, method, or module, and every reference to it in the worktree |
| `truss new` | Makes a new package |
| `truss sync`, `truss status`, `truss stop` | Brings a worktree's session up to date, lists the background process's sessions, and stops it |
| `truss lsp` | Runs the language server on standard input and output (not built yet) |
| `truss clean` | Stops the background process and deletes the store |

`truss --version` prints the version of each stage that has one: code
generation and the Unicode tables. Those are the versions in exact keys, so a
report of a stale result can say which stage it came from. Every other
result is kept under the compiler's identity, the hash of its executable.
The parser, the type checker, and the prover, with its solver, are to have
versions of their own as DESIGN.md's "Incremental builds" asks.

### Finding the packages

A command acts on the packages of the worktree it is run in, through that
worktree's session in the code database, as DATABASE.md's "Sessions"
describes. The worktree is the top of the git worktree, or outside git, the
nearest directory at or above the current one that holds a `truss.toml`,
the way Cargo and Go find a package. The command is about the packages at
or under the current directory, or else the one it is in, so running in a
package's directory, or any directory below it, is about that package, and
running at the top of a repository of several packages is about all of
them. `run` and `build` need exactly one, and say so when there are more.
`-C DIRECTORY`, as in `git` and `make`, runs as if from that directory,
written before the command or after it. The positional arguments are free
for what each command acts on.

A package's modules are the `.truss` files under its directory, as
SYNTAX.md says, with two exceptions:

- **A directory with its own `truss.toml` is another package,** and none of
  its files are modules of this one, as with Cargo's and Go's nested
  modules.
- **Directories whose names start with `.`, and `_build` and
  `node_modules`, are skipped,** so `.git` and an editor's hidden
  directories are never read.

A manifest that cannot be read, or a package name used twice, is a problem
in the code, reported with the diagnostics, and the exit status is 1.

### Common options

- **`--json`** writes one JSON document to standard output in place of the
  report for people, for every command except `run`, `fmt`, `new`, `lsp`,
  and `clean`, whose output is a program's, a list of files, or nothing.
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

There is no `--quiet` or `--verbose` beyond what a command lists. Reports
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

- **What a command produces goes to standard output:** a test report, a
  list of holes, signatures, a JSON document. **Diagnostics for people go
  to standard error,** as rustc, Go, and Cargo send them, so that `truss run`
  can give its program's output alone on standard output. With `--json`,
  diagnostics are inside the document on standard output, and standard error
  is empty unless the command could not run.
- **Exit status:**

  | Status | Means |
  |---|---|
  | 0 | The command did what was asked, and the code had no problem |
  | 1 | The code has a problem: a diagnostic, a failed test, a build refused for a `todo` |
  | 2 | The command could not do its job: a bad argument, a path that names nothing, no `truss.toml`, no C compiler, a compiler bug |

  `truss run` exits with its program's
  status once the program starts, as `go run` and `cargo run` do; before
  that, it exits as above.

## Checking

```text
truss check [--fix] [--json]
```

`truss check` runs every stage that can report a diagnostic: lexing,
parsing, name resolution, type checking, ownership, capabilities and
dependency grants, package-wide checks, and proofs, once the prover exists.
Proofs are part of checking, not a separate command, because DESIGN.md
makes every promise in a signature something the compiler proves; a package
whose proofs have not been checked has not been checked. Proofs are modular
and cached, so this costs O(change) like the rest. Code generation reports
nothing, so `check` never builds.

It prints each diagnostic as `Diagnostic.render` does, at most
`Diagnostic.limit` of them in each file, and then a count. The JSON document
is `{"format", "diagnostics"}`.

**`--fix`** applies every fix that is the only fix its diagnostic offers,
writes the files, checks again, and repeats until no such fix is left, then
reports what remains. Two fixes whose edits overlap are not applied in the
same round, since applying both could give what neither meant; the second
waits for the next round, after the file is checked again. Rounds stop
after 32, so fixes that undo each other cannot run forever. A diagnostic with several fixes, such as an addition
that may overflow, which offers four, is a choice for the person or agent,
so it is reported and left alone. An agent that has chosen applies the
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
  says what the whole suite costs and not only what ran this time:

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
  which are wrong, and `truss holes` lists what each `todo` blocks.
- **`--rerun`** runs every selected test, using no kept results and keeping
  new ones, as `go test -count=1` does. Results are deterministic, so this
  is only for doubting the cache, after a suspected compiler bug, or for
  timing every test on this machine now.
- **The time limit** for each test is its package's, set in the manifest as
  `[test] time_limit = 10`, in seconds, with 10 as the default. It is not a
  flag, so that every machine and CI run uses the same limit. A run over
  several packages builds one test program for each.
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

A package has at most one `main`, and its program is built from it, as
IMPLEMENTATION.md has a package compile to a single program or library. A
package with no `main` has no program, so `run` and `build` stop with 2; one
with several has a problem in its code, so they stop with 1.

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
whose `main` can reach a `todo` or an `echo`, in code or, once the prover
exists, in a proof, and lists each one with the definitions on the way from
`main` to it:

```text
render.truss:12:14: `todo` can be reached from `main`, so the program cannot be built.
    weather::main::main -> weather::render::render
``` The program is written to `--output`, or else
to a file named after the package in the current directory, as `go build`
does. Truss keeps every intermediate file in its cache, so there is no build
directory in the package, and nothing to add to `.gitignore` but the
program. The JSON document is `{"format", "diagnostics", "output"}`, or
`{"format", "diagnostics", "unshippable"}` when it refuses, each with its
kind, `todo` or `echo`, its file, line, and column, and its way from
`main`.

Building for another target, which CODEGEN.md allows through the target's
`USize`, would add `--target` to `build`. Stage0 builds for the host only.

## Formatting

```text
truss fmt [--check] [FILE...]
```

`truss fmt` is not built yet; it waits for the formatter. It rewrites the
package's files, or the named ones, into the one
layout SYNTAX.md describes, and prints the names of the files it changed.
It has no options for style. **`--check`** changes nothing and exits with 1,
listing the files that are not formatted, for CI, as `gofmt -l` and
`cargo fmt --check` do. A file with a syntax error is reported and left as
it is. Formatting changes no hash, so it rebuilds nothing.

## Tools for agents

These commands answer the questions that GOALS.md says dominate fast
development: what is unfinished, what a definition promises, what a change
touches, and how to change a name everywhere at once.

### `truss holes`

```text
truss holes [--json] [FILE_OR_DIRECTORY...]
```

Lists every `todo` in the package, or in the named files, as DESIGN.md's
"Unfinished code" asks: its position, the type it must have, the names in
scope with their types, and what it blocks, which is `main`, if `main` can
reach it, and each test that can, and once the prover exists, each proof
that depends on it. Each hole is a task a person or agent can take on its
own. A type defined as `todo` is listed too.

```text
render.truss:12:14: hole of type String
    in scope: header: String, report: Report
    blocks: main; test weather::render "renders an empty report"
```

A `todo` whose type nothing fixes, such as one inside an interpolation, is
listed as "not decided yet". Name resolution records the names in scope at
each `todo`, and the checked form gives their types, through the `Inspect`
library. What a hole blocks is every test, and `main`, that reaches the
hole's definition through what each definition reads, which the code
database keeps. The JSON document is
`{"format", "diagnostics", "holes"}`, each with its definition, file, line,
and column, its kind, `value` or `type`, its type, its names in scope with
their types, and what it blocks. Listing holes is not a failure, so the
exit status is 0 unless the package has diagnostics.

### `truss show`

```text
truss show [--body] [--json] PATH...
```

Prints the signatures at each path, each after its file and line. A
signature is the definition's text with every body left out; once the
formatter exists, it is printed as `truss fmt` writes it.

- for a definition, such as `weather::forecast::parse`, its signature with
  every clause: generic parameters, parameters with their defaults, the
  return type, `uses`, `cost`, `requires`, `ensures`, and `decreases`
- for a type, such as `weather::forecast::Forecast`, its definition, its
  `derives`, and the signatures of its methods and of the `impl`s in its
  package
- for a method, `weather::forecast::Forecast.summary`
- for a module, `weather::forecast`, every definition's signature, and for
  a package, `weather`, every public one

A module of another package, such as `standard::list`, shows only what is
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
or else where the worktree's branch left the default branch, so that a
branch's every change is what it shows, uncommitted ones included. The code
database compares the two sessions, as its "Impact" section describes:
every result a changed file can reach is brought up to date in both and
compared, so a part checked again that came out the same is told apart
from one that changed, and reformatting, or moving a definition within its
file, changes nothing. For each definition that was added, removed, or
changed, it shows:

- **The parts that changed,** such as its tree, its signature, or its body.
- **For a changed signature,** the old and new one, since those are what a
  reviewer must read closely, and every definition that reads it, which are
  the callers to review.

Then it lists the tests whose code changed, which are the only tests the
change can affect, each with whether its result is already kept, so an
agent knows the cost of its change before running anything. Once the
prover exists, the proofs to check again are listed the same way.

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
repository can each run it and compare what they reach, and `truss overlap`
does that for them. The JSON document is `{"format", "diagnostics",
"problems", "base", "changes", "tests"}`, where each change has its path,
`added`, `removed`, or `changed`, the parts that changed, its signature
before and after, and what reads it, with the parts on each side.

### `truss references` and `truss dependencies`

```text
truss references [--json] NAME
truss dependencies [--json] NAME
```

List what reads a definition, or what a definition reads, part by part,
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

Says what is at a position, as diagnostics give positions: the name or
expression there, what a name means, its type, and the signature of the
definition it refers to, so an agent can ask about one name without
reading the file around it.

### `truss overlap`

```text
truss overlap [--with BRANCH] [--merge] [--json]
```

Lists where the worktree's changes from its common commit with another
meet the other's, as DATABASE.md's "Parallel work" describes: a part both
change, or a change of one that reads what the other changes, such as a
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
every reference to it in every package of the worktree, whichever directory
it is run from. `TO` is a new name, as in `truss
rename weather::forecast::parse read`, or a full path that keeps the
definition in its module and a method with its type. Renaming a module, as
in `truss rename weather::forecast weather::outlook`, moves its file, and
every `use` of it and every full path to it changes. Renaming a field or a
variant is not built yet. The rename is made in a trial, a state that
starts from the worktree's session and holds only what the rename changes,
and is checked there first; it is refused, changing nothing, if it would
cause any diagnostic, such as for a name that is taken, breaks a naming
rule, or would hide another, which are the diagnostics a hand-made rename
would cause. A worktree that already has diagnostics is refused too, since its
references are found through checked code. References in packages outside
the worktree cannot be changed, so renaming a public definition changes the
package's public interface, which `truss impact` reports like any other
changed signature. Each edit replaces the name's tokens alone, so the files need no
formatting afterward. Renaming changes callers'
hashes but not their proofs or test results, since those are keyed with
names replaced by numbers, so a rename re-proves and re-runs nothing.
Renaming a local variable is left to the language server, which has the
cursor's position. The JSON document is `{"format", "diagnostics", "edits",
"moved"}`, with each edit's file, byte range, and replacement.

## Making a package

```text
truss new NAME
```

Makes a directory `NAME` with a `truss.toml` naming the package and a
`main.truss` with an empty `main`:

```truss
fn main(arguments: List[String]) -> ExitCode {
  ExitCode.success
}
```

A library is a package without `main`, so it needs no flag: delete the
file. The name must be a `lower_snake_case` name, since it is the first
part of every module path.

## The background process

IMPLEMENTATION.md notes that starting fresh costs O(files), because a fresh
process must at least read every file to learn which changed, and that a
long-running process that watches the files and keeps the query results in
memory makes each command O(change). The code database's background
process is that process, as DATABASE.md's "The background process"
describes, and the command line is its client:

- **A command that reads code starts it if it is not running,** as Bazel
  and Gradle do, sends it the command line and the current directory, and
  shows what it answers. It runs the command line's own code, from that
  directory, so the answer is the same as in the command's own process.
  What a command writes to standard error, such as the status line, comes
  to the command as it is written, and its output and exit status when it is
  done.
- **It ends after three hours without a command,** or on `truss stop`, and
  `truss status` lists its sessions. `truss sync` brings a worktree's
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
store" describes. Every entry is named by a key of
what it was made from, so entries never go stale, the store collects old
entries itself to keep within its budget, and nothing in it is ever needed
for a correct answer. **`truss clean`** stops the background process and
deletes the store, which only costs time.

## For working on the compiler

- **`--sanitize`,** on `test` and `run`, builds with AddressSanitizer and
  UndefinedBehaviorSanitizer and keeps no test results, as CODEGEN.md's
  "Testing" describes. It is left out of each command's help.
- **`--check-proofs`,** on `test`, `run`, and `build`, is to emit a run-time
  check for every proven obligation once the prover exists. Stage0 has no
  prover, so all its builds check what a prover would prove, and the flag
  comes with the prover.
- **`stage0/tools/debug`** prints a file's tokens, one a line, or each
  definition's syntax tree as an S-expression, with its diagnostics, as
  `dune exec stage0/tools/debug/debug.exe -- tokens FILE` or `tree FILE`.
  It is a tool of this repository, like the fuzzer and the benchmarks, and
  not part of `truss`.

## Left out

- **`truss explain CODE`,** which rustc has. A diagnostic's message, notes,
  and fixes are meant to say everything needed to act on it, and a second
  text for each code would be a second place to keep up to date.
- **A watch mode,** such as `cargo watch` or `vitest --watch`. The
  background process already checks every open worktree as its files
  change, so running a command again does what a watch would, at once.
- **`truss add`, `truss publish`, and a lock file.** There is no package
  registry yet. Adding a dependency is a manifest edit that grants
  capabilities, which is the change DESIGN.md wants reviewers to see, so a
  command for it should only come with the registry.
- **Selecting tests by what changed,** as Nx's `affected` does. The cache
  already runs only the tests whose code changed, and exactly those, so a
  selection by files changed could only be less exact.

## Implementation in stage0

- **`stage0/bin/truss.ml` only starts the command line,** as the command a
  person or agent runs, or with `__serve`, as the background process. All
  of it is the `cli` library, so tests drive commands directly.
- **Arguments are parsed with Cmdliner,** the usual OCaml library, which
  gives every command `--help` and a manual page from the same
  definitions. `Cli.Main.evaluate` parses a command line and runs it, in
  either process. Before parsing, `Cli.Arguments` moves a leading `-C
  DIRECTORY` after the command and marks where `run`'s program arguments
  start, which Cmdliner's own rules would read differently.
- **Commands write through `Output`,** which is the process's own standard
  output and error, or in the background process, a buffer for the output
  and the client's progress for the errors.
- **`Project` is the packages a command is about,** from the database's
  session, with their files and manifests and how paths are shown; `Report`
  writes diagnostics for people or as JSON; and each command has a module
  of its own. `References`, which finds every place a definition or module
  is named from resolution's names and the checked form's calls and
  members, gives `rename` its edits; `Signatures`, which cuts the bodies
  out of a definition's text, serves `show`, `impact`, and `explain`.
- **The test program reports each test as it starts and ends,** with its
  duration, as CODEGEN.md's "The test program" describes, and
  `Compile.run_tests` reads those records while the program runs, handing
  each to `truss test` for the status line.
- **The tests** are in [`stage0/test/cli/`](stage0/test/cli): each makes a
  small package, or a git repository, in a temporary directory, with a store
  of its own, and states one fact about what a command does with it.
