> 🧔 This part of this doc was written by a human. LLMs are not allowed to edit it.

# Truss Implementation

The stage0 compiler is written in OCaml and is compiled to a static binary. When
the Truss compiler builds a program it uses QBE as its backend. Truss programs
do not link to a separate runtime, they use libc. Truss packages compile to a
single binary or library.

## Modular Design

Each part of Truss should be modular. This will help make the compiler easier to
develop as well as make it easier to bootstrap the compiler in parts.

> 🤖 LLMs are allowed to edit the doc below this point

## Notes for stage0

These notes collect implementation consequences of the decisions in
[DESIGN.md](DESIGN.md), [SYNTAX.md](SYNTAX.md), and [GRAMMAR.md](GRAMMAR.md).

### Lexer

- **Unicode.** Names follow UAX #31, must be in Normalization Form C, and are
  checked against UTS #39 for mixed scripts and confusables. sedlex is a
  Unicode-aware lexer generator for OCaml; `uucp` provides Unicode character
  properties and `uunf` normalization. The confusable data comes from UTS #39's
  published tables.
- **A stack of modes.** The lexer tracks open brackets (`(`, `[`, `{`,
  `${`), the kind of string it is inside (ordinary, or raw with a given number
  of quotes and `$` signs), and whether it is inside a `cost` clause, where it
  returns the cost words as their own tokens.
- **Line breaks need one token of lookahead.** Whether a line feed becomes a
  `NEWLINE` depends on the next token, so the lexer reads the first token of
  the next line before deciding.
- **Integer literals do not fit OCaml's `int`,** which has 63 bits. Store them
  with Zarith, which the prover's exact integer arithmetic needs anyway.

### Parser

- **A hand-written recursive-descent parser,** with the operator levels from
  GRAMMAR.md and an explicit check for operators that may not be combined.
  This gives better error messages and fixes than a generated parser, which
  matters because agents act on them.
- **`grammar/truss.mly` as a reference.** Menhir can build a parser from it, so
  a corpus of example files can be parsed by both, and any file one accepts
  and the other rejects points at a bug in one of them.
- **Recovery at definitions.** Every top-level definition parses on its own,
  and `truss fmt` starts each in the first column, so after an error the
  parser can skip to the next line that begins with a definition keyword.
- **Diagnostics in a structured format,** such as JSON, with exact text
  replacements for fixes, so tools and agents can apply them without parsing
  messages.

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

### Code generation with QBE

- **No overflow intrinsics.** `checked_add` and the other checked operations
  need explicit comparisons around the arithmetic. Proven-safe arithmetic
  needs none.
- **No debug information.** Locations for panics, `echo`, and failed asserts
  come from the position table built at the end of the build, which records
  positions relative to each definition.
- **Assembly output.** QBE produces assembly, so the build needs an assembler
  and a linker.
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
