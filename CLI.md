# Truss Command Line

This document designs `truss`, the one program people and agents run to work
on Truss code: checking, testing, running, building, formatting, and the
tools that let an agent see what a change touches. It follows
[GOALS.md](GOALS.md) and the decisions in [DESIGN.md](DESIGN.md), and drives
the stages that [TYPECHECKER.md](TYPECHECKER.md) and
[CODEGEN.md](CODEGEN.md) describe. `truss test` and `truss run` are built,
in [`stage0/bin/truss.ml`](stage0/bin/truss.ml), and take a package's
directory as their first argument; everything else here is designed but not
built yet. The prover and the formatter are not built either, so the
commands that use them say what they will do.

## Principles

- **One program.** Every tool is a subcommand of `truss`, as with `go` and
  `cargo`, so there is one thing to install, one version to report, and one
  place to load a package. `truss-check` is replaced by `truss check`, and
  `truss-lex` and `truss-parse`, which exist for working on the compiler,
  become `truss debug tokens` and `truss debug tree`, left out of
  `truss --help`.
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
| `truss fmt` | Formats the package's files |
| `truss holes` | Lists every `todo`, with its type, the names in scope, and what it blocks |
| `truss show` | Prints the signatures of a module, type, or definition |
| `truss impact` | Lists what changed since a revision, or what depends on a definition |
| `truss rename` | Renames a definition or module, and every reference to it in the package |
| `truss new` | Makes a new package |
| `truss lsp` | Runs the language server on standard input and output |
| `truss clean` | Deletes the cache |

`truss --version` prints the toolchain's version and each stage's version:
the hash format, the parser, the type checker, the prover with its solver,
and code generation. Those are the versions in cache keys, so a report of a
stale result can say which stage it came from.

### Finding the package

A command finds its package the way Cargo and Go do: it looks for
`truss.toml` in the current directory and then in each directory above it,
and uses the first one found. `-C DIRECTORY`, as in `git` and `make`, runs
as if from that directory. A positional package directory, which `truss test`
and `truss run` take today, is dropped, so that the positional arguments are
free for what each command acts on.

The package's modules are the `.truss` files under its directory, as
SYNTAX.md says, with two exceptions, which `Type_checker.read_directory`
does not make yet:

- **A directory with its own `truss.toml` is another package,** and none of
  its files are modules of this one, as with Cargo's and Go's nested
  modules.
- **Directories whose names start with `.` are skipped,** so `.git` and an
  editor's hidden directories are never read.

### Common options

- **`--json`** writes one JSON document to standard output in place of the
  report for people, for every command except `run`, `fmt`, `new`, `lsp`,
  and `clean`, whose output is a program's, a list of files, or nothing. Its fields are listed with each command. Every document has
  `"format": 1`, which changes only when a field is removed or changes
  meaning, and `"diagnostics"`, an array of diagnostics as
  `Diagnostic.to_json_object` writes them, with each one's file. A command
  that stops at diagnostics still writes its document.
- **`-C DIRECTORY`**, above.

There is no `--quiet` or `--verbose` beyond what a command lists, and no
color option: reports for people use color only when the stream is a
terminal and `NO_COLOR` is not set.

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
  | 2 | The command could not do its job: a bad argument, no `truss.toml`, no C compiler, a compiler bug |

  `truss-check` already uses these. `truss run` exits with its program's
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
`Diagnostic.limit` of them, and then a count. The JSON document is
`{"format", "diagnostics"}`.

**`--fix`** applies every fix that is the only fix its diagnostic offers,
writes the files, checks again, and repeats until no such fix is left, then
reports what remains. A diagnostic with several fixes, such as an addition
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
  error, redrawn as each test ends, shows how far the run has got, what has
  not passed so far, and the test that has been running longest, as Bazel's
  and nextest's do:

  ```text
  [ 97/143] 1 failed · 0.6s · running weather::parse "reads hourly rows" (0.4s)
  ```

  Before the tests run it shows the build instead, as instances compiled out
  of those to compile. The line is drawn only when standard error is a
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
   0.42s  weather::parse "reads hourly rows"
   0.08s  weather::render "renders an empty report"  cached
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
  flag, so that every machine and CI run uses the same limit. The manifest
  reader does not read it yet, and the limit is fixed at 10 seconds.
- **The JSON document** is `{"format", "diagnostics", "tests", "timings"}`,
  where each test is `{"module", "name", "file", "line", "outcome",
  "cached", "milliseconds", "message", "echo"}`, for every selected test,
  passing or not, and `"timings"` gives the milliseconds of the check, the
  build, the tests, and the whole run.

## Running and building

```text
truss run [--release] [--] [ARGUMENT...]
truss build [--output PATH] [--json]
```

A package has at most one `main`, and its program is built from it, as
IMPLEMENTATION.md has a package compile to a single program or library.

**`truss run`** builds a development program, as CODEGEN.md's "C files and
optimization" describes, and runs it on the terminal with the arguments, so
it can prompt and read, then exits with its status. `echo` writes to
standard error, as SYNTAX.md says. A `todo` that `main` can reach is
refused, as in `build`: DESIGN.md rules out a `todo` that panics when
reached, since that would be a failure the signature does not show, and that
holds for a development run too. The first argument that is not an option
starts the program's arguments, and `--` marks the start when the first one
begins with `-`. **`--release`** builds as `truss build` does, for timing
the program.

**`truss build`** builds a release program: each module's instances in one C
file at `-O2`, linked with ThinLTO. It refuses a program whose `main` can
reach a `todo` or an `echo`, in code or in a proof, and lists each one with
the path from `main` to it. The program is written to `--output`, or else
to a file named after the package in the current directory, as `go build`
does. Truss keeps every intermediate file in its cache, so there is no build
directory in the package, and nothing to add to `.gitignore` but the
program. The JSON document is `{"format", "diagnostics", "output"}`.

Building for another target, which CODEGEN.md allows through the target's
`USize`, would add `--target` to `build`. Stage0 builds for the host only.

## Formatting

```text
truss fmt [--check] [FILE...]
```

`truss fmt` rewrites the package's files, or the named ones, into the one
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
scope with their types, and what it blocks, which is each test that can
reach it, each proof that depends on it, and `main`, if `main` can reach
it. Each hole is a task a person or agent can take on its own. A type
defined as `todo` is listed with the definitions that need its contents.

```text
weather/render.truss:12:14: hole of type String
    in scope: report: Report, header: String
    blocks: main; test weather::render "renders an empty report"
```

The JSON document is `{"format", "diagnostics", "holes"}`. Listing holes is
not a failure, so the exit status is 0 unless the package has diagnostics.

### `truss show`

```text
truss show [--body] [--json] PATH...
```

Prints the signatures at each path, formatted as `truss fmt` writes them:

- for a definition, such as `weather::forecast::parse`, its signature with
  every clause: generic parameters, parameters with their defaults, the
  return type, `uses`, `cost`, `requires`, `ensures`, and `decreases`
- for a type, such as `weather::forecast::Forecast`, its definition, its
  `derives`, and the signatures of its methods and of the `impl`s in its
  package
- for a method, `weather::forecast::Forecast.summary`
- for a module, `weather::forecast`, every definition's signature, and for
  a package, `weather`, every public one

A module of another package shows only what is visible from this one, so an
opaque type's fields stay hidden. `--body` prints whole definitions. Truss
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
- **For a body,** the tests that can reach it.
- **For every change,** the proofs and tests that must be checked or run
  again, with how many are already in the cache, so an agent knows the cost
  of its change before running anything.

`--since main` shows everything a branch changes. Two agents on the same
package can each run it and compare the definitions they reach, which is
GOALS.md's "find exactly where and how their work overlapped". The revision
is read with `git show`, so this form needs the package to be in a git
repository.

**With paths,** it lists what depends on each definition now: every
definition whose check read its signature, and every test that can reach
it, which serves as finding references.

Both come from the traces that queries already record. A trace points from
a result to what it read, so finding what read a definition means looking
through traces; the background process keeps the reverse index, and a cold
run builds it. The JSON document is `{"format", "diagnostics", "changes",
"dependents"}`.

### `truss rename`

```text
truss rename [--json] FROM TO
```

Renames a definition, a method, a field, a variant, or a module, and
rewrites every reference to it in the package. Renaming a module, as in
`truss rename weather::forecast weather::outlook`, moves its file, and every
`use` of it changes. The rename is refused, changing nothing, if the new
name is taken, breaks a naming rule, or would hide a name, which are the
diagnostics a hand-made rename would cause. References in other packages
cannot be changed, so renaming a public definition changes the package's
public interface, which `truss impact` reports like any other changed
interface. Each edit replaces the name's tokens
alone, so the files need no formatting afterward. Renaming changes callers'
hashes but not their proofs or test results, since those are keyed with
names replaced by numbers, so a rename re-proves and re-runs nothing.
Renaming a local variable is left to the language server, which has the
cursor's position.

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
  file's tokens and syntax trees, as `truss-lex --tokens` and
  `truss-parse --tree` do now, with `--json` for their diagnostics.
- **`--sanitize`,** on `test` and `run`, builds with AddressSanitizer and
  UndefinedBehaviorSanitizer and keeps no test results, as CODEGEN.md's
  "Testing" describes.
- **`--check-proofs`,** on `test`, `run`, and `build`, emits a run-time
  check for every proven obligation. Stage0 has no prover, so its builds
  always check what a prover would prove, and the flag will mean something
  once the prover exists.

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
  gives every command `--help` and a manual page from the same definitions,
  and shell completion.
- **One library loads a package for every command:** finding `truss.toml`,
  reading the manifest and the modules, and loading the standard library,
  which `truss.ml` and `truss_check.ml` each do on their own now. Another
  writes diagnostics for people or as JSON, with each one's file.
- **The test program reports each test as it ends,** with its duration, as
  CODEGEN.md's "The test program" describes, and `Compile.run_tests` reads
  those records while the program runs rather than its whole output at the
  end, handing each one to `truss test` for the status line. The program
  and the parser of its report change together, and kept results gain the
  duration.
- **Each command is its own module** in `stage0/bin`, built into the one
  `truss` executable, and `truss_check.ml`, `truss_lex.ml`, and
  `truss_parse.ml` are removed.
- **The order of building** follows what exists: `check`, `test`, `run`,
  and `build` drive stages that are built; `show` and `holes` read checked
  forms; `impact` needs a reverse index of traces and a second database
  loaded from a git revision; `rename` needs resolution's references; and
  `fmt`, `lsp`, and the background process wait for the formatter, the
  language server, and file watching.
