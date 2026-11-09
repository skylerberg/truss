# Truss Command Line

This document designs `truss`, the one program people and agents run to work
on Truss code: checking, testing, running, building, formatting, and the
tools that let an agent see what a change touches. It follows
[GOALS.md](GOALS.md) and the decisions in [DESIGN.md](DESIGN.md), and drives
the stages that [TYPECHECKER.md](TYPECHECKER.md) and
[CODEGEN.md](CODEGEN.md) describe. It is built in
[`stage0/cli/`](stage0/cli), with the arguments parsed in
[`stage0/bin/truss.ml`](stage0/bin/truss.ml), except `truss fmt`, `truss
lsp`, and the background process, which wait for the formatter, the
language server, and file watching. The prover is not built either, so what
the commands will do with proofs is stated where it matters.

## Principles

- **One program.** Every tool is a subcommand of `truss`, as with `go` and
  `cargo`, so there is one thing to install, one version to report, and one
  place to load a package. The tools for working on the compiler are
  `truss debug tokens` and `truss debug tree`, left out of `truss --help`.
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
| `truss check` | Reports every diagnostic in the package; `--fix` applies the fixes that have no alternative |
| `truss test` | Checks the package, then runs the tests whose results are not cached |
| `truss run` | Checks the package, builds its program for development, and runs it |
| `truss build` | Checks the package and builds its program for release, refusing any `todo` or `echo` `main` can reach |
| `truss fmt` | Formats the package's files (not built yet) |
| `truss holes` | Lists every `todo`, with its type, the names in scope, and what it blocks |
| `truss show` | Prints the signatures of a module, type, or definition |
| `truss impact` | Lists what changed since a revision, or what depends on a definition |
| `truss rename` | Renames a definition, method, or module, and every reference to it in the package |
| `truss new` | Makes a new package |
| `truss lsp` | Runs the language server on standard input and output (not built yet) |
| `truss clean` | Deletes the cache |

`truss --version` prints the version of each stage that has one: the hash
format, code generation, and the Unicode tables. Those are the versions in
cache keys, so a report of a stale result can say which stage it came from.
The parser, the type checker, and the prover, with its solver, are to have
their own as DESIGN.md's "Incremental builds" asks.

### Finding the package

A command finds its package the way Cargo and Go do: it looks for
`truss.toml` in the current directory and then in each directory above it,
and uses the first one found. `-C DIRECTORY`, as in `git` and `make`, runs
as if from that directory, written before the command or after it. The
positional arguments are free for what each command acts on.

The package's modules are the `.truss` files under its directory, as
SYNTAX.md says, with two exceptions:

- **A directory with its own `truss.toml` is another package,** and none of
  its files are modules of this one, as with Cargo's and Go's nested
  modules.
- **Directories whose names start with `.` are skipped,** so `.git` and an
  editor's hidden directories are never read.

### Common options

- **`--json`** writes one JSON document to standard output in place of the
  report for people, for every command except `run`, `fmt`, `new`, `lsp`,
  and `clean`, whose output is a program's, a list of files, or nothing.
  Its fields are listed with each command. Every document has
  `"format": 1`, which changes only when a field is removed or changes
  meaning, and `"diagnostics"`, an array of diagnostics as
  `Diagnostic.to_json_object` writes them, with each one's file. A command
  that stops at diagnostics still writes its document.
- **`-C DIRECTORY`**, above.

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
- **The time limit** for each test is the project's, set in the manifest as
  `[test] time_limit = 10`, in seconds, with 10 as the default. It is not a
  flag, so that every machine and CI run uses the same limit.
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
it can prompt and read, then exits with its status. `echo` writes to
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
each `todo`, and the checked form gives their types. What a hole blocks
comes from lowering the code that `main` and each test can run, so it is
listed only for a package without diagnostics. The JSON document is
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
truss impact [--since REVISION] [--json]
truss impact [--json] PATH...
```

**With no path,** it compares the package as it is with the package at a
git revision, `HEAD` by default, so that uncommitted changes are what it
shows. For each definition that was added, removed, or changed, it says
which of its hashes changed, as DESIGN.md splits them: its interface, its
contract, a default, or its body. Then it lists what the change reaches:

- **For an interface or a contract,** the old and new signature, since those
  are what a reviewer must read closely, and every definition whose check
  read it, which are the callers to review.
- **For every change,** the tests that can reach it, which must run again,
  with how many already have a kept result for the code as it is now, so an
  agent knows the cost of its change before running anything. Once the
  prover exists, the proofs to check again are listed the same way.

A definition is matched with its earlier self by its path, so a renamed
definition is listed as removed and added, and one moved within its file is
not listed at all, since its hashes do not change.

`--since main` shows everything a branch changes. Two agents on the same
package can each run it and compare the definitions they reach, which is
GOALS.md's "find exactly where and how their work overlapped". The revision
is read with `git show`, so this form needs the package to be in a git
repository.

**With paths,** it lists what depends on each definition now: every
definition whose code names it, and every test that can reach it, which
serves as finding references.

What reads a definition comes from what resolution and type checking
decided each name in the package's code means; which tests reach a
definition comes from lowering the code each test can run, so tests are
listed only for a package without diagnostics. Both look through the whole
package, which costs O(package); the background process is to keep the
reverse index of the traces queries record, which makes it O(change). The
JSON document is `{"format", "diagnostics", "changes", "tests"}` without
paths, where each change has its path, `added`, `removed`, or `changed`,
the parts that changed, its signature before and after, and what reads it,
and `{"format", "diagnostics", "dependents", "not_found"}` with paths.

### `truss rename`

```text
truss rename [--json] FROM TO
```

Renames a definition, every version of a method, or a module, and rewrites
every reference to it in the package. `TO` is a new name, as in `truss
rename weather::forecast::parse read`, or a full path that keeps the
definition in its module and a method with its type. Renaming a module, as
in `truss rename weather::forecast weather::outlook`, moves its file, and
every `use` of it and every full path to it changes. Renaming a field or a
variant is not built yet. The rename is made in memory and the package
checked first; it is refused, changing nothing, if it would cause any
diagnostic, such as for a name that is taken, breaks a naming rule, or
would hide another, which are the diagnostics a hand-made rename would
cause. A package that already has diagnostics is refused too, since its
references are found through checked code. References in other packages
cannot be changed, so renaming a public definition changes the package's
public interface, which `truss impact` reports like any other changed
interface. Each edit replaces the name's tokens alone, so the files need no
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
long-running process that watches the files and keeps the query database in
memory makes each command O(change). The language server and the commands
share it.

- **Commands start it without being asked,** as Bazel and Gradle do, and
  talk to it over a socket in the cache directory named by the package's
  absolute path and the toolchain's version. A command from another toolchain
  version starts its own. Anything that can be done without it is done the
  same way in the command's own process, so the process only makes commands
  faster: their output is the same either way.
- **It ends after three hours without a command,** as Gradle's daemon does,
  and `TRUSS_NO_SERVER=1` runs every command in its own process, for CI,
  where a process that lives past the job only gets in the way.
- **Each package directory has its own,** so agents working in different git
  worktrees of one repository each have one, and they share the cache of
  objects and test results, whose writes are atomic renames.

Stage0 runs every command in its own process and has no background process
yet. The commands do not change when it comes.

## The cache

Results are kept under `$TRUSS_CACHE`, or else `$XDG_CACHE_HOME/truss`, or
else `~/.cache/truss`: object files in `objects`, test results in
`results`, and later checked forms and proofs. Every entry is named by a key
of what it was made from, so entries never go stale, and nothing in the
cache is ever needed for a correct answer. **`truss clean`** deletes it all,
which only costs time. Removing old entries on its own, by last use, is
left for later.

## For working on the compiler

These are left out of `truss --help` and listed by `truss debug --help`:

- **`truss debug tokens FILE`** and **`truss debug tree FILE`** print a
  file's tokens, one a line, and each definition's syntax tree as an
  S-expression, with its diagnostics on standard error, or with `--json`,
  only the diagnostics, on standard output.
- **`--sanitize`,** on `test` and `run`, builds with AddressSanitizer and
  UndefinedBehaviorSanitizer and keeps no test results, as CODEGEN.md's
  "Testing" describes. It is left out of each command's help.
- **`--check-proofs`,** on `test`, `run`, and `build`, is to emit a run-time
  check for every proven obligation once the prover exists. Stage0 has no
  prover, so all its builds check what a prover would prove, and the flag
  comes with the prover.

## Left out

- **`truss explain CODE`,** which rustc has. A diagnostic's message, notes,
  and fixes are meant to say everything needed to act on it, and a second
  text for each code would be a second place to keep up to date.
- **A watch mode,** such as `cargo watch` or `vitest --watch`. The language
  server checks as files change, and with the background process each
  command is already fast, so running a command again does what a watch
  would.
- **`truss add`, `truss publish`, and a lock file.** There is no package
  registry yet. Adding a dependency is a manifest edit that grants
  capabilities, which is the change DESIGN.md wants reviewers to see, so a
  command for it should only come with the registry.
- **Selecting tests by what changed,** as Nx's `affected` does. The cache
  already runs only the tests whose code changed, and exactly those, so a
  selection by files changed could only be less exact.

## Implementation in stage0

- **Arguments are parsed with Cmdliner,** the usual OCaml library, which
  gives every command `--help` and a manual page from the same
  definitions. Before parsing, `Cli.Arguments` moves a leading `-C
  DIRECTORY` after the command and marks where `run`'s program arguments
  start, which Cmdliner's own rules would read differently.
- **The commands are the `cli` library,** apart from parsing arguments, so
  tests drive them directly. `Project` finds and loads a package and shows
  paths, `Report` writes diagnostics for people or as JSON, and each command
  has a module of its own. `References`, which finds every place a
  definition or module is named from resolution's names and the checked
  form's calls and members, serves `rename` and `impact`; `Signatures`,
  which cuts the bodies out of a definition's text, serves `show` and
  `impact`.
- **The test program reports each test as it starts and ends,** with its
  duration, as CODEGEN.md's "The test program" describes, and
  `Compile.run_tests` reads those records while the program runs, handing
  each to `truss test` for the status line.
- **What code reaches comes from lowering,** with `Compile.reached_definitions`
  and `Compile.unshippable`, which walk the instances a root reaches as a
  build would and never compile them, so `holes` and `impact` need no C
  compiler.
- **The tests** are in [`stage0/test/cli/`](stage0/test/cli): each makes a
  small package in a temporary directory and states one fact about what a
  command does with it.
