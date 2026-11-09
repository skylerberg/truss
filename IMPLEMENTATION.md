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

These notes collect implementation consequences of the decisions in
[DESIGN.md](DESIGN.md), [SYNTAX.md](SYNTAX.md), and [GRAMMAR.md](GRAMMAR.md).

### Lexer

The full design is in [LEXER.md](LEXER.md). In short:

- **Hand-written, in two passes.** A scanner turns bytes into raw tokens that
  record whether a line break came before them, and a layout pass inserts
  `NEWLINE` tokens and matches brackets.
- **Unicode tables generated from one pinned Unicode version,** including
  NFC, rather than taken from sedlex, `uucp`, and `uunf`, whose versions follow
  their own releases.
- **Integer literals do not fit OCaml's `int`,** which has 63 bits. Store them
  with Zarith, which the prover's exact integer arithmetic needs anyway. Float
  literals are kept as exact decimals until the type checker rounds them.

### Parser

The full design is in [PARSER.md](PARSER.md). In short:

- **A hand-written recursive-descent parser** that never backtracks. It parses
  operators with a total order and then reports the combinations Truss's
  partial order leaves out, with exact parentheses as fixes.
- **One tree per definition, with positions relative to it.** The lexer's
  balanced brackets let a file be split into definitions before parsing, so
  each definition parses on its own, and one that only moved gives the same
  tree.
- **An abstract tree, not a lossless one.** Truss has no comments, so the
  formatter needs only spans, blank lines, and parentheses from the source.
- **`grammar/truss.mly` as a reference.** A Menhir parser built from it, for
  tests only, must accept and reject the same files as the real one.
- **Diagnostics in a structured format,** with exact text replacements for
  fixes, shared with the lexer.

### Hashing and caching

- **Deterministic CBOR** (RFC 8949, section 4.2) is small enough to write
  directly, which keeps the exact byte format under the project's control. The
  same encoder must later be written in Truss and produce the same bytes.
- **BLAKE3** for content hashes. `digestif` provides BLAKE2 but, as far as I
  know, not BLAKE3, so stage0 needs a binding or its own implementation. Every
  hash carries a prefix naming the format version and algorithm, so this can
  change.
- **A content-addressed store** of results, each with the trace of what it
  depended on, can start as files in a cache directory named by hash.
  Each compiler stage has its own version in the key.

### Background process

- **Starting fresh on every command costs O(files),** because the compiler must
  at least check which files changed. A long-running process that watches the
  files (FSEvents on macOS, inotify on Linux) and keeps parsed definitions and
  traces in memory makes each command O(change). The language server and the
  command line can share it.

### Code generation through C

- **Why C rather than QBE.** Truss has no foreign code, so the standard
  library's hashing, crypto, and text handling run on Truss's own generated
  code, and nothing can drop to C for speed. QBE has no inliner, no 128-bit
  multiply, no bit-counting, rotate, or byte-swap instructions, no `sqrt`, no
  SIMD, no atomics, and no way to say that pointers do not alias. C compilers
  have all of these. Truss proves no aliasing, which C expresses with
  `restrict`. Linking libc already needs the platform's C toolchain, so
  emitting C adds almost no dependency.
- **A lowered IR in front of C.** Monomorphization, drops, yield lowering, and
  cursor state machines happen in the compiler's own IR. Early cutoff compares
  that IR, never object code, so a different C compiler version invalidates no
  proofs or test results. The compile-time evaluator interprets the same IR,
  which keeps it matching compiled code.
- **Generated C avoids undefined behavior by construction.** Wrapping
  arithmetic is emitted as unsigned. Shifts, indexes, and other checked
  operations are always proven. The compiler passes `-fno-strict-aliasing`,
  `-fno-finite-loops`, because a pure loop without a `time` clause may
  legitimately never end, and `-ffp-contract=off` with no fast-math, so floats
  follow IEEE 754 bit for bit.
- **Overflow checks use compiler builtins,** such as
  `__builtin_add_overflow`. Proven-safe arithmetic needs none.
- **Positions stay relative to each definition.** Locations for panics,
  `echo`, and failed asserts come from the position table built at the end of
  the build. Release builds may also emit `#line` directives for debuggers and
  profilers.
- **Linking is O(program).** It is the one step of an everyday edit whose cost
  grows with the whole program. Options: a fast linker such as mold or lld; or,
  for development and tests, a long-running test runner that loads only the
  code that changed, keeping full static links for programs that ship.

### Proofs

- **A pinned SMT solver with step limits.** Z3's `rlimit` and cvc5's
  `--rlimit` count work rather than time, so a proof gives the same answer on
  every machine as long as the solver version and options are the same. Both
  are part of the prover's version in cache keys.

### Running code while compiling

- **Tagged templates need an evaluator.** The compiler proves a tag's
  `requires` by running the check on the literal text, so stage0 needs an
  interpreter for pure, terminating Truss code that matches compiled code
  exactly, including float behavior and the size of `USize` on the target.
  Constants can use the same evaluator once they are allowed to call
  functions.
