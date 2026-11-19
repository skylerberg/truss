> 🧔 This part of this doc was written by a human. LLMs are not allowed to edit it.

# Truss Implementation

The stage0 compiler is written in OCaml and is compiled to a static binary. When
the Truss compiler builds a program it emits C code as its backend. Truss
programs do not link to a separate runtime, they use libc. Truss packages
compile to a single binary or library.

## Modular Design

Each part of Truss should be modular. This will help make the compiler easier to
develop as well as make it easier to bootstrap the compiler in parts.

> 🤖 LLMs are allowed to edit the doc below this point

## Notes for stage0

### Building

- **Dependencies** are declared in `dune-project`, which generates
  `truss.opam`. Install them with
  `opam install . --deps-only --with-test --with-dev-setup`. On macOS, Zarith
  also needs GMP and `pkgconf` from Homebrew.
- **Z3 5.3.3** runs the prover's queries, and the prover refuses any other
  version, since another could answer differently. Install it with
  `brew install z3` on macOS, or from the release's archive, and put it on
  the path or name it in `TRUSS_Z3`. CI downloads that release and checks
  its hash.
- **`stage0/tools/prover_queries`** prints the solver's input for each
  obligation that starts at a position, written as a diagnostic writes it:
  `dune exec ./stage0/tools/prover_queries/prover_queries.exe --
  standard/numbers/floats/floats.truss:6:13`. A file of a package is named
  by its path. The output is one script for `z3 -in`, which prints each
  obligation's answer, Z3's reason for an unknown answer, and the steps Z3
  used.
- **The Unicode tables are generated** from the Unicode character database
  files that `stage0/tools/unicode/sources.txt` lists with their hashes:
  the compiler's into `stage0/support/unicode/unicode_tables.ml`, and the standard
  library's into `standard/text/unicode_data/unicode_data.truss`. To move to a new
  version of Unicode, change that list and run
  `stage0/tools/unicode/regenerate.sh`.
- **`dune build`** builds everything, and **`dune fmt`** formats the code
  with the ocamlformat version that `.ocamlformat` pins.
- **`stage0/tools/docs/build.sh`** builds the odoc documentation of every
  library, a page of the library dependency graph, and a page of the
  dependencies between areas into `_build/docs`. On the page of each
  library, `stage0/tools/docs/library_uses` lists the names that the
  library's `.cmt` and `.cmti` files reference in other libraries and the
  names that other libraries reference in it, each linked to its entry in
  odoc's index. The script needs odoc and dune-deps from opam and Graphviz
  and jq from Homebrew, which `dune-project` does not list because CI never
  builds the documentation.
- **CI** (`.github/workflows/ci.yml`) builds, checks formatting, checks that
  `truss.opam` matches `dune-project`, rejects comments, runs every test
  suite, and proves the standard library, on every pull request and every
  push to `main`. It must stay fast: it installs nothing in an ordinary run,
  restores dune's cache, the solver's answers, and compiled objects from
  `main`, and gives the longest suites runners of their own.

### Libraries

- **A library is a contract with more than one consumer, or a unit that
  must not see its consumer's dependencies,** as `parser` lists `token` but
  not `lexer`, so it cannot call the scanner.
- **Each library belongs to one area of stage0,** a directory under
  `stage0`. The dependencies between areas form no cycle.
- **A unit of several modules inside a library is a subdirectory.** The
  library's `dune` file sets `(include_subdirs qualified)`, the
  subdirectory's module of its own name is its interface, and its other
  modules are hidden from the rest of the library, as `lexer/scanner` is.

### The lexer

- **The scanner reads Truss, and the habits read other languages.** The
  scanner's core scans the grammar of [SPECIFICATION.md](SPECIFICATION.md).
  Each form of another language, such as a `//` comment, `===`, `f"..."`,
  or `0755`, belongs to a module of `Habits`, which the scanner asks first
  wherever such a form can start. A habit reports the form and lexes it as
  the Truss token it stands for. A change to Truss's grammar edits the core,
  and a new form of another language edits only the habits.

### The parser

- **The parser reads tokens, never the source text.** A fix that would move
  code edits around it instead, so the fix never respells the code:
  `x as Int64` becomes `Int64.from_integer(x)` by inserting
  `Int64.from_integer(` and replacing ` as Int64` with `)`.
- **The tree holds no positions.** A node holds an id, and its item's span
  table holds the node's span at that index. A definition that only moved
  parses to an equal tree, so a change to positions alone re-runs only the
  parts that report positions, and no stage strips spans to compare two
  trees.

### Stages

- **Every stage after the type checker reads the MIR.** Ownership, the
  prover, and code generation read no core expression.
- **No stage rebuilds what an earlier stage had,** since a rebuilt fact can
  disagree with the original. The builder lowers each expression once and
  records each fact where it has it, and no stage finds a loop in the
  control-flow graph. A stage that needs a value in another state runs the
  MIR's statements in that state.

### Documents

Each document has one job, and a fact is stated in one of them:

- **[SPECIFICATION.md](SPECIFICATION.md) and [PACKAGES.md](PACKAGES.md)
  define Truss,** its grammar and the rules of the language and of
  packages, **and [DESIGN.md](DESIGN.md) says why.** They describe the
  language, whether or not stage0 builds all of it yet.
- **This document holds the rules for working on stage0.**

Stage0 and the standard library have no documents of their own. Stage0's
code and interfaces describe it, and the standard library's signatures and
contracts describe it.

A design document describes the design as it is. How it got there belongs in
version control, in commit messages and pull request descriptions. A
document has no sections that list changes, an earlier version's behavior,
or the review that settled a question; when the design changes, the document is
rewritten to describe the new design.

A document records no measurement. A time or a size is true of one commit,
and a document that states one gives every later change something to measure
again. A measurement belongs in the commit message or the pull request
it explains.

### Comments

Code has no comments. Nothing checks a comment against the code it
describes, so the comment drifts. A reason, an invariant, or a trap is
stated instead by a name, by code that cannot be gotten wrong, or by a test
named after the failure it prevents. A rule of the language belongs in
[SPECIFICATION.md](SPECIFICATION.md). CI rejects a comment in any tracked
file with `stage0/tools/comments`. The tool also rejects a file type that it
has no comment syntax for, so a new type of file cannot add comments
unchecked.

### Module names

Code names each module by its path, such as `Resolve.Names` or
`Emit_c.Ir_builder`, so a reader finds a definition without searching for the
module a short name stands for. Code has no `open`: a name from another
module is qualified, as in `Facts.find_visible_type`, and no `open` can
shadow a name in scope. Code has no module alias either. Many modules share a name,
such as the scanner's `Names` and `Resolve.Names`, so an alias's short name
does not say which module it is. A library's main module exposes a
submodule with `module Names = Names`; that line is the library's
interface, not an alias.

An expression may open a module for its infix operators: `Logic`, or
Cmdliner's `Arg` or `Term`, as in `Logic.(a &&& b)`. Warnings 44 and 45
reject such an open when it shadows a name in scope. CI rejects every other
open, and every alias, with `stage0/tools/qualified_names`.

### Testing

Every stage of stage0 is tested the same way:

- **A test states its claim.** Each test gives a small input and asserts
  exact facts about the result: the tokens, a diagnostic's code and
  position, the text after applying a fix. Its name names the behavior it
  covers.
- **Tests are fast and deterministic.** No randomness, no large inputs, and
  no test cases generated by combining options, so the suite can run on
  every change.
- **No golden files.** A golden file compares a whole dump of output, so it
  breaks when anything in the dump changes, whether or not the behavior it
  meant to check did, and it never says which fact mattered.
- **A fix is tested by applying it.** A test that expects a fix applies it,
  checks again, and asserts that the diagnostic is gone with no new one in
  its place.
- **Fuzzing and benchmarks are tools, not tests.** They live in
  `stage0/tools/` and are run by hand. Each problem a fuzzer finds becomes a
  focused test of its own.
- **Tests share one checked standard library.** A test that needs the
  standard library creates its database over the standard library's stored
  package database, which a test executable loads once from the user's cache.
  A test must not give a new database the library's sources: that parses
  and checks the whole library again, so every such test gets slower each
  time the library grows. A test whose probe module must be in the standard
  package, such as one that calls an intrinsic, extends the stored package
  with `Database.For_testing.extend_package`, which checks only the probe.
- **A test whose only claim is that it passes is written in Truss.** Each
  file under `stage0/test/codegen/modules/` is a module of tests. A file of
  `modules/library/` tests one module of the standard library and is named
  after it. The other directories, such as `modules/feature/` and
  `modules/owning/`, test the code generated for a construct. `module_tests`
  divides the modules into the shares that `TRUSS_TEST_SHARE` names, builds
  the tests of every module in its share into one program, and runs it. The
  `runtest` alias runs two shares in parallel. A new test therefore adds
  its code to one build and starts no build of its own. A test of a panic
  goes in the module `library::panics`: each of its tests must panic with a
  message that contains the test's name. A test written in OCaml that
  compiles a program of its own is for what a passing test cannot show: a
  diagnostic, the generated code, a reported source location, or a whole
  program's output.
- **A test's Truss source is a fixture file, not an OCaml string.** The
  text a test checks lives in `fixtures/<suite>/<name>.truss` beside the
  suite, where it can be read, edited, and renamed as Truss.
  `embed_fixtures` compiles each directory of fixtures into the module
  `Fixtures`, so the test names one as
  `Fixtures.Prover.addition_that_can_overflow`, and a fixture that is
  missing fails to compile. Text that is not a whole module stays in OCaml:
  a template with a hole that the test fills, a line given to the lexer or
  the parser, and a snippet of one or two lines.
- **Checks against the documents are tests,** as long as each one states a
  single property, such as "SPECIFICATION.md's keyword list matches the lexer's",
  or "every example in the documents lexes cleanly".
- **One test can be run alone.** With `TRUSS_TEST` set, a test executable
  runs only the tests whose names contain it, for working on one:
  `TRUSS_TEST=standard::text _build/default/stage0/test/standard_library_tests.exe`.
  A test must not depend on what an earlier test did, since `TRUSS_TEST`
  and `TRUSS_TEST_SHARE` run it without the tests before it. The harness
  restores the environment after each test, so a test sets or unsets the
  variables it needs and does not restore them itself.
