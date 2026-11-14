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
- **The Unicode tables are generated** from the Unicode character database
  files that `stage0/tools/unicode/sources.txt` lists with their hashes:
  the compiler's into `stage0/support/unicode/unicode_tables.ml`, and the standard
  library's into `standard/text/unicode_data/unicode_data.truss`. To move to a new
  version of Unicode, change that list and run
  `stage0/tools/unicode/regenerate.sh`. Each function of
  `standard/text/unicode_tables/unicode_tables.truss` that names a table assigns its
  result to a `var`, so that callers know it by its contract: with a
  functional body the prover would copy the table into every caller's
  queries.
- **`dune build`** builds everything, and **`dune fmt`** formats the code
  with the ocamlformat version that `.ocamlformat` pins.
- **`stage0/tools/docs/build.sh`** builds the odoc documentation of every
  library, a page of the library dependency graph, and a page of the
  dependencies between areas into `_build/docs`. It
  needs odoc and dune-deps from opam and Graphviz from Homebrew, which
  `dune-project` does not list because CI never builds the documentation.
- **CI** (`.github/workflows/ci.yml`) builds, checks formatting, checks that
  `truss.opam` matches `dune-project`, runs every test suite, and proves the
  standard library, on every pull request and every push to `main`. It must
  stay fast: it installs nothing in an ordinary run, restores dune's cache,
  the solver's answers, and compiled objects from `main`, and gives the
  longest suites runners of their own. The workflow's comments say why each
  job is laid out as it is; when the proofs' jobs become the longest again,
  add a runner to their list.
- **A pull request that takes out a recent merge fails** before anything is
  built (`.github/scripts/reverts.sh`). Several sessions fetch into one
  repository, so `origin/main` can move between a branch's merge of it and a
  squash onto it, and the squashed commit then undoes every merge its older
  tree lacks, with no conflict. To squash safely, read `origin/main` once
  into a variable, merge that commit, and squash onto that commit. A pull
  request that means to revert has a title that starts with "Revert".

### Libraries

- **A library is a contract with more than one consumer, or a unit that
  must not see its consumer's dependencies.** Code that one library alone uses
  is a module of that library, so that nothing else can come to depend on
  it. It stays a library of its own when its short dependency list
  keeps it apart from a layer, as `session` knows no compiler stage and the
  move analysis, `moves`, knows nothing of code generation.
- **Each library belongs to one area of stage0,** a directory under
  `stage0`, and the dependency graph that `stage0/tools/docs/build.sh`
  draws colors libraries by area:

  | Area | Holds |
  |---|---|
  | `support` | Leaf libraries every area uses: sources, diagnostics, paths, encodings, hashing, and the operating system |
  | `standard_library` | What the compiler knows of the standard library: its embedded source, the definitions it names, its intrinsics, and the C library it calls |
  | `packages` | Manifests, the registry, and a build's packages and files |
  | `query` | The incremental query engine, its phases, sessions, and the saved store |
  | `lexer`, `parser` | Text to tokens, and tokens to syntax trees |
  | `type_checker` | Syntax trees to the core form, and the checks of patterns, use, and packages |
  | `mir` | The MIR and its builder |
  | `ownership`, `prover`, `codegen` | The MIR's three consumers |
  | `tools`, `test` | Executables that are not shipped, and the tests |

  The libraries at the top of `stage0` put the areas together: `checks`
  runs every check before the prover, `database` is the project's layer over
  sessions, `evaluator` gives the prover code generation, and `cli` is the
  command line. No area depends on them, so the areas form no cycle.
- **A unit of several modules inside a library is a subdirectory.** The
  library's `dune` file sets `(include_subdirs qualified)`, the
  subdirectory's module of its own name is its interface, and its other
  modules are hidden from the rest of the library, as `lexer/scanner` is.
- **Every dependency is listed.** `dune-project` sets
  `(implicit_transitive_deps false)`, so a module names only the libraries
  its own `dune` file lists, and those lists are the whole graph.
- **Tests reach internal values through `For_testing`,** a submodule of an
  interface that exports only the values tests and tools read. CI rejects a
  use anywhere else.

### Documents

Each document has one job, and a fact is stated in one of them:

- **[SPECIFICATION.md](SPECIFICATION.md) and [PACKAGES.md](PACKAGES.md)
  define Truss,** its grammar and the rules of the language and of
  packages, **and [DESIGN.md](DESIGN.md) says why.** They describe the
  language, whether or not stage0 builds all of it yet.
- **The Markdown files beside the modules of [`standard/`](standard)
  document the standard library,** each its module's types and functions.
- **[LEXER.md](LEXER.md), [PARSER.md](PARSER.md),
  [TYPECHECKER.md](TYPECHECKER.md), [MIR.md](MIR.md), [PROVER.md](PROVER.md),
  [CODEGEN.md](CODEGEN.md), [DATABASE.md](DATABASE.md), and
  [CLI.md](CLI.md) describe stage0,**
  each for its own stage, and each ends with the one list of the features
  that stage does not build yet. How results are kept current and kept from being
  computed twice is DATABASE.md's, and the other documents describe only
  their own stage's additions to it.
- **This document holds the rules for working on stage0.**

A document does not restate the code: a module's contents, a signature, or a
test's coverage is read from the code, where it cannot go stale.
A stage's document gives its structure, the decisions that need a reason,
and its interfaces to other stages. A mechanism, a data format, a JSON
field, or a diagnostic's code is read from the code. A reason belongs in
one document: a stage's document does not argue again what DESIGN.md
argues, and CLI.md does not restate PACKAGES.md's rules.

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

A comment holds information the code cannot express: a reason, an invariant, or a trap. One
that restates the code, labels a section, or retells a document is left
out. A comment never points at a document, a section of one, or another
file, since such a pointer goes stale when its target moves.

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
  standard library creates its engine over a frozen base engine that
  checked the library once for the whole test executable. A test of the
  code database copies a store that already holds the library's state. A
  test must not load the library's sources into a new engine: that parses
  and checks the whole library again, so every such test gets slower each
  time the library grows.
- **A test run reuses the previous run's results.** Two results are
  keyed by their inputs, so they can be kept between
  runs: the solver's answer to a query, and the object compiled from a
  file of generated C. `TRUSS_SOLVER_CACHE` and `TRUSS_OBJECT_CACHE` name
  the directories. CI restores both from `main`'s last run, so a run
  solves and compiles only the changes.
- **The standard library's own tests are written in Truss.** Each file of
  `stage0/test/codegen/library/` is a module of tests for one module of the
  library, named after it. `library_tests` builds every file's tests into
  one program and runs it, so a new test adds its own code to that build
  and no build of its own. A test of a library function's result goes
  there. A test of a panic goes in the module `panics`: each of its tests
  must panic with a message that contains the test's name. A test written
  in OCaml that compiles a program of its own is for the compiler: a
  diagnostic, generated code, or a whole program's output.
- **A test's Truss source is a fixture file, not an OCaml string.** The
  text a test checks lives in `fixtures/<suite>/<name>.truss` beside the
  suite, where it can be read, edited, and renamed as Truss.
  `embed_fixtures` compiles each directory of fixtures into the module
  `Fixtures`, so the test names one as `Fixtures.Prover.overflow`, and a
  fixture that is missing fails to compile. A fixture is named after its
  test. Text that is not a whole module stays in OCaml: a template with a
  hole that the test fills, a line given to the lexer or the parser, and a
  snippet of one or two lines.
- **Every test checks the code database too.** When a test ends, the harness
  computes every result the test's engines hold again, in a new engine with
  the same inputs, and fails the test if one differs. So a query that is not
  a function of its reads, or a result the database left stale, fails
  whichever test met it.
- **Checks against the documents are tests,** as long as each one states a
  single property, such as "SPECIFICATION.md's keyword list matches the lexer's",
  or "every example in the documents lexes cleanly".
- **One test can be run alone.** With `TRUSS_TEST` set, a test executable
  runs only the tests whose names contain it, for working on one:
  `TRUSS_TEST=standard::text _build/default/stage0/test/standard_library_tests.exe`.
  A test must not depend on what an earlier test did, since `TRUSS_TEST`
  and `TRUSS_TEST_SHARE` run it without the tests before it.
