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
- **The Unicode tables are generated.** `standard/text/unicode_data.truss`
  holds the tables of character properties and case mappings, and nothing
  else. `stage0/unicode_tables` writes it from five files of the Unicode
  character database: `UnicodeData.txt`, `DerivedCoreProperties.txt`,
  `SpecialCasing.txt`, `CaseFolding.txt`, and `EastAsianWidth.txt`. To move
  to a new version of Unicode, download those files of that version into
  one directory and run
  `dune exec stage0/unicode_tables/unicode_tables.exe -- DIRECTORY > standard/text/unicode_data.truss`.
  The functions that search the tables are written by hand, in
  `standard/text/unicode_tables.truss`. Each function there that names a
  table assigns its result to a `var`, so that its body is not functional
  and callers know it by its contract. With a functional body the function
  would be known by its definition, and the prover would copy the table
  into every query of every caller.
- **`dune build`** builds everything, **`dune test`** runs the tests, and
  **`dune fmt`** formats the code with the ocamlformat version that
  `.ocamlformat` pins.
- **CI** (`.github/workflows/ci.yml`) builds, checks formatting, checks that
  `truss.opam` matches `dune-project`, and runs the tests, on every pull
  request and every push to `main`. It must stay fast, so:
  - **Nothing is installed in an ordinary run.** OCaml and every dependency
    come from a cache of the whole opam root, keyed by the opam and OCaml
    versions, the runner's image, and `truss.opam`
    (`.github/actions/opam`). A change to `truss.opam` starts from the newest
    cache with the same opam, OCaml, and image, and installs only what
    changed. Only a new opam, OCaml, or image builds the switch from nothing,
    with the opam binary downloaded from its release and checked against a
    pinned hash. Nothing comes from apt, so a slow package mirror cannot slow
    a run.
  - **Dune's cache carries over from `main`,** so a pull request builds only
    what it changed. Only pushes to `main` save it, trimmed so that it stays
    quick to restore.
  - **The build, formatting, the opam file, and the tests are one dune run,**
    so they overlap. Two things run beside it, each on a runner of its own:
    the codegen tests under sanitizers, and the standard library's proofs.
    The sanitizers' job runs the programs that use several threads a second
    time under ThreadSanitizer, which cannot run beside the others.
  - **The standard library's proofs have their own jobs.** They are the
    longest test, and the one that grows with the library, so they do not
    share a runner's cores with the rest. The dune run sets
    `TRUSS_SKIP_LIBRARY_PROOFS`, which makes `standard_library_tests` say it
    is skipped and stop, and the proofs' jobs build and run that one
    executable.
  - **The proofs are dealt out to several runners.** `TRUSS_PROOF_SHARE`
    names a run's share as `index/count`, and `standard_library_tests` then
    checks and proves only that share's modules. The modules are dealt out
    by the size of their source, so the shares take about as long as each
    other. When the proofs' jobs become the longest again, add a share: one
    more entry in the workflow's list.
  - **Solver answers are cached between runs.** Most of proving the
    standard library is the solver. The cache key of an answer is the query
    text, the solver version, and the step limit. A run restores the cache
    from `main` and solves only the queries whose text changed. Only pushes
    to `main` save the cache. Each share of the proofs keeps its own.
  - **A new push to a pull request cancels the run it replaces.**
- **A pull request that takes out a recent merge fails,** before anything is
  built (`.github/scripts/reverts.sh`). Several sessions fetch into one
  repository, so `origin/main` can move between a branch's merge of it and
  a squash onto it, and the squashed commit then carries the branch's older
  tree onto the newer `main`: every merge the tree lacks is undone, with no
  conflict. The check fails a pull request that changes every file one of
  the last merges changed and puts one of them back to what it was before
  that merge. A pull request that means to do so has a title that starts
  with "Revert". To squash safely, read `origin/main` once into a variable,
  merge that commit, and squash onto that commit.

### Documents

Each document has one job, and a fact is stated in one of them:

- **[DESIGN.md](DESIGN.md), [SYNTAX.md](SYNTAX.md), and
  [GRAMMAR.md](GRAMMAR.md) say what Truss is:** what code means and why, how
  it is written, and its exact grammar. They describe the language, whether
  or not stage0 builds all of it yet.
- **[LEXER.md](LEXER.md), [PARSER.md](PARSER.md),
  [TYPECHECKER.md](TYPECHECKER.md), [PROVER.md](PROVER.md),
  [CODEGEN.md](CODEGEN.md), [DATABASE.md](DATABASE.md), and
  [CLI.md](CLI.md) say what stage0 does,**
  each for its own stage, and each ends with the one list of what that stage
  does not build yet. How results are kept current and kept from being
  computed twice is DATABASE.md's, and the other documents say only what
  their own stage adds to it.
- **This document holds the rules for working on stage0.**

A document does not restate the code: which module holds what, a signature,
or what each test covers is read from the code, where it cannot go stale.

A design document describes the design as it is. How it got there belongs in
version control, in commit messages and pull request descriptions. A
document has no sections that list what changed, what an earlier version
did, or which review settled what; when the design changes, the document is
rewritten to describe the new design.

A document records no measurement. A time or a size is true of one commit,
and a document that states one gives every later change something to measure
again. What was measured belongs in the commit message or the pull request
it explains.

### Comments

A comment says what the code cannot: a reason, an invariant, or a trap. One
that restates the code, labels a section, or retells a document is left
out. A comment never points at a document, a section of one, or another
file, since such a pointer goes stale when what it names moves.

### Testing

Every stage of stage0 is tested the same way:

- **A test states what it checks.** Each test gives a small input and asserts
  exact facts about the result: the tokens, a diagnostic's code and
  position, the text after applying a fix. Its name says what behavior it
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
- **A test run reuses what the last one worked out.** Two results are
  kept by what they were worked out from, so they can be kept between
  runs: the solver's answer to a query, and the object compiled from a
  file of generated C. `TRUSS_SOLVER_CACHE` and `TRUSS_OBJECT_CACHE` name
  the directories. CI restores both from `main`'s last run, so a run
  solves and compiles only what changed.
- **The standard library's own tests are written in Truss.** Each file of
  `stage0/test/codegen/library/` is a module of tests for one module of the
  library, named after it. `library_tests` builds every file's tests into
  one program and runs it, so a new test adds its own code to that build
  and no build of its own. A test of what a library function returns goes
  there. A test of a panic goes in the module `panics`: each of its tests
  must panic with a message that contains the test's name. A test written
  in OCaml that compiles a program of its own is for the compiler: a
  diagnostic, generated code, or a whole program's output.
- **Every test checks the code database too.** When a test ends, the harness
  computes every result the test's engines hold again, in a new engine with
  the same inputs, and fails the test if one differs. So a query that is not
  a function of what it reads, or a result the database left stale, fails
  whichever test met it.
- **Checks against the documents are tests,** as long as each one states a
  single property, such as "GRAMMAR.md's keyword list matches the lexer's",
  or "every example in the documents lexes cleanly".
- **One test can be run alone.** With `TRUSS_TEST` set, a test executable
  runs only the tests whose names contain it, for working on one:
  `TRUSS_TEST=standard::text _build/default/stage0/test/standard_library_tests.exe`.
