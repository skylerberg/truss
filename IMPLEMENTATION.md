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
  `stage0/tools/unicode/regenerate.sh`.
- **`dune build`** builds everything, and **`dune fmt`** formats the code
  with the ocamlformat version that `.ocamlformat` pins.
- **`stage0/tools/docs/build.sh`** builds the odoc documentation of every
  library, a page of the library dependency graph, and a page of the
  dependencies between areas into `_build/docs`. It
  needs odoc and dune-deps from opam and Graphviz from Homebrew, which
  `dune-project` does not list because CI never builds the documentation.
- **CI** (`.github/workflows/ci.yml`) builds, checks formatting, checks that
  `truss.opam` matches `dune-project`, rejects comments, runs every test
  suite, and proves the standard library, on every pull request and every
  push to `main`. It must stay fast: it installs nothing in an ordinary run,
  restores dune's cache, the solver's answers, and compiled objects from
  `main`, and gives the longest suites runners of their own. When the
  proofs' jobs become the longest again, add an entry to the `share` matrix
  of the `proofs` job.

### Libraries

- **A library is a contract with more than one consumer, or a unit that
  must not see its consumer's dependencies.** Code that one library alone uses
  is a module of that library, so that nothing else can come to depend on
  it. It stays a library of its own when its short dependency list
  keeps it independent of a layer, as `cache` knows no compiler stage and the
  move analysis, `moves`, knows nothing of code generation.
- **Each library belongs to one area of stage0,** a directory under
  `stage0`. The dependencies between areas form no cycle.
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

### The lexer

- **The scanner reads Truss, and the habits read other languages.** The
  scanner's core scans the grammar of [SPECIFICATION.md](SPECIFICATION.md).
  Each form of another language, such as a `//` comment, `===`, `f"..."`,
  or `0755`, belongs to a module of `Habits`, which the scanner asks first
  wherever such a form can start. A habit reports the form and lexes it as
  the Truss token it stands for. A change to Truss's grammar edits the core,
  and a new form of another language edits only the habits.
- **A decision about a token looks at the next token, not at bytes.** `1.`
  is a float unless a word follows the `.`, and `...` is a range, `todo`, or
  nothing, by the operands on its two sides. The scanner scans the next token
  with its own scanning function and holds it, so the decision sees the
  token that follows in fact, inside an interpolation as well. A token
  carries the trivia before it, so a token scanned ahead never takes a line
  break that precedes the token before it.
- **A file's tokens are the tokens of its fixed text.** The lexer applies
  every machine-applicable fix, lexes the result, and maps the tokens back
  to the file's offsets, so the parser reads the file as its fixes would
  write it. A fix whose text adds an error, or joins or splits a neighboring
  token, is withheld, so a habit needs no guard of its own against those.
  Recovery cannot see a fix that lexes cleanly but changes a value, such as
  a string's text that would become an escape or an interpolation; the
  habit that offers the fix must withhold it.
- **Recovery checks fixes in groups, never one lex per fix.** A fix changes
  how the text lexes only between the tokens on either side of its edits,
  so fixes whose edits an untouched token separates are independent, and
  one lex checks them all. When the lex fails, halving the group finds the
  fixes that fail. Fixes whose edits touch form a set, and each round takes
  one fix from each set: the fix is applied if it works alone and with the
  fixes its set already applied. A set of more than eight touching fixes is
  withheld unchecked, so the rounds are few. If the applied fixes then fail
  together, the fixes were not independent, which is a compiler bug. A
  check that lexes once for each fix makes a file with a fix on every line
  quadratic.
- **A token says what the lexer inserted.** A closer that the lexer inserts
  for an unclosed bracket is marked, and an interpolation records whether
  its `}` closed it. The parser reads these marks, never zero widths or
  the text: a closer that a fix inserts is also zero-width after mapping,
  and taking it for the lexer's would silence the errors after it.

### The parser

- **The parser reads tokens, never the source text.** A fix, and a message
  that quotes code, spell tokens: names, keywords, and punctuation
  exactly, and literals by value. A fix that would move code edits around
  it instead, as `x as T` becomes `T.from(x)` by inserting `T.from(` and
  replacing ` as T` with `)`.
- **A file's tree is the tree of its fixed text.** A habit reports the form
  of another language with its fix, and recovers with the nodes its own
  tokens write, or with an error node. It never builds the tree its fix
  writes: such a tree drifted from the fix's text and put nodes out of
  source order. `Parsed` applies the fixes of the diagnostics where the
  parser recovered, lexes the fixed text, maps the tokens back to the
  file's offsets, and parses them again, and that tree is the file's.
- **The parser's fixes are checked as the lexer's are,** in groups, by
  `Lexer.Recovery`. The fix of a diagnostic where the parser did not
  recover, such as moving a misplaced `use` line, is checked but not
  applied: the tree is already right, and code a fix moves maps to
  zero-width spans.
- **The tree holds no positions.** A node holds an id, and its item's span
  table holds the node's span at that index. The parser fills the table as
  it allocates ids, so the definition's id is the last. A definition that
  only moved parses to an equal tree, so a change to positions alone
  re-runs only the parts that report positions, and no stage strips spans
  to compare two trees.

### Stages

- **Every stage after the type checker reads the MIR.** Ownership, the
  prover, and code generation read no core expression.
- **The MIR is a tree, and the builder lowers each expression once.** A
  body's code is a block: statements, and the block's value where control
  reaches its end. An `if` is one `Conditional`, a `match` its `Cases`, and
  a short-circuit operator one `Connective`, each with its operands as
  blocks. A loop is one statement that holds its body. A `return`, a
  `break`, and a `continue` are each a `Jump`, the last statement of its
  block. A clause that can run is one formula. A quantifier that runs is
  its loop, whose body holds the quantifier's body.
- **A MIR part holds the control-flow graph beside the tree.** Ownership
  and code generation read the graph, a `Mir.Graph.t`: blocks and
  terminators. It is derived once for a definition, a default, and a
  constant. No stage
  builds a graph but the expansion, and no stage finds a loop in a
  graph. Where a `Connective` or its negation decides a branch, control
  goes straight to the branch's target, so a name that `is` binds is read
  only where it is bound.
- **The prover reads the tree by structural recursion.** The frame after
  an `if` is the merge of the frames after its two blocks, under the
  `if`'s condition and its negation. A jump takes its frame to the loop or
  the return that it leaves by, so paths are joined only there: after a
  loop, at the end of a branch of tasks, and where a body returns.
- **No stage rebuilds what an earlier stage had.** The builder records a
  fact where it has it: a loop's condition and body, a loop's collection,
  the operands of a loop's comparison, the function reference or the
  lambda expression that an argument is. A stage that needs a value in
  another state runs the MIR's statements in that state.
- **What a path knows is in the path's frame.** In the prover, the place
  of a `mut` binding, the collection of a local's slice, and the
  write-back of a part lent `mut` are merged with the paths, and a loop's
  head forgets the slice of a local that the loop assigns. One table for a
  body gave every path the answer of one path.
- **`Mir` is the one module of the MIR library that other libraries
  name,** and it includes `Tree` and `Walk`. The emitter's state is
  abstract: the lowering changes it through the emitter's operations
  alone, and passes what a callee needs to know as an argument.
- **A module of the prover opens only the modules before it:** `State`,
  `Facts`, `Contracts`, the rules from `Validity` to `Loops`, `Assertions`,
  `Reader`, and `Translate`. A rule reads a body or a formula through the context, which
  `Reader` fills, so the one cycle, between a call and a formula that holds
  calls, is in one place.

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
  standard library creates its pipeline over the standard library's stored
  state, which a test executable loads once from the user's cache.
  A test must not give a new pipeline the library's sources: that parses
  and checks the whole library again, so every such test gets slower each
  time the library grows.
- **A test run reuses the previous run's results.** Two results are
  keyed by their inputs alone, so they hold for every compiler and are
  kept between runs in the user's cache, as the `truss` command
  keeps them: the solver's answer to a query, as a result of kind
  `solver`, and the object compiled from a file of generated C, in the
  cache's `caches/objects`. A run solves and compiles only what no earlier
  run did, and CI restores the caches of `main`'s last run.
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
- **Checks against the documents are tests,** as long as each one states a
  single property, such as "SPECIFICATION.md's keyword list matches the lexer's",
  or "every example in the documents lexes cleanly".
- **One test can be run alone.** With `TRUSS_TEST` set, a test executable
  runs only the tests whose names contain it, for working on one:
  `TRUSS_TEST=standard::text _build/default/stage0/test/standard_library_tests.exe`.
  A test must not depend on what an earlier test did, since `TRUSS_TEST`
  and `TRUSS_TEST_SHARE` run it without the tests before it.
