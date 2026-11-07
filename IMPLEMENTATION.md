> 🧔 This doc was written by a human. LLMs are not allowed to edit this file.

# Truss Implementation

The stage0 compiler is written in OCaml and is compiled to a static binary. When
the Truss compiler builds a program it uses QBE as its backend. Truss programs
do not link to a separate runtime, they use libc. Truss packages compile to a
single binary or library.

## Modular Design

Each part of Truss should be modular. This will help make the compiler easier to
develop as well as make it easier to bootstrap the compiler in parts.
