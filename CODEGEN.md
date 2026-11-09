# Truss Code Generator

This document designs stage0's code generation: everything between the type
checker's output and a program that runs. It follows the decisions in
[DESIGN.md](DESIGN.md), [SYNTAX.md](SYNTAX.md), and
[IMPLEMENTATION.md](IMPLEMENTATION.md). It reads the checked form that
[TYPECHECKER.md](TYPECHECKER.md) describes. The prover is not designed yet,
so this document states what it expects from it. It is being built in
[`stage0/codegen/`](stage0/codegen).

## What code generation does

Code generation takes the checked form of each definition the program can
reach and produces C, which a C compiler turns into object files, which a
linker turns into a program. The checked form records the type of every
expression, the exact method, variant, field, `impl`, or associated type
each name means, the mode of every argument, and which places each statement
moves. Every proof obligation has been discharged by then.

Code generation:

- finds the instances the program needs: each definition with its type
  arguments and capability sets, starting from `main`, the tests, or the
  code run while compiling
- decides the memory layout of every type
- lowers each instance to the lowered IR (LIR), a small typed control-flow
  graph, inserting drops, copies, and the hidden parameters for capabilities
  and defaults
- turns yielding methods into calls that receive the caller's loop body, and
  pulled cursors into state machines
- emits C from the LIR, compiles it, and links the program, with the table
  that turns positions into file names and lines

It does not:

- check anything about the program. Every error a user can see is reported
  by an earlier stage. A failure here is a compiler bug.
- insert run-time checks. Indexes, overflow, division, shifts, and
  `unreachable` have all been proven. The only checks in generated code are
  the ones the program asks for, such as `checked_add` or `items.get(i)`.
- compile anything used only by proofs: theorems, laws, `proof` blocks,
  `requires`, `ensures`, invariants, `decreases`, cost clauses, and functions
  called only from those. Code generation starts from what can run, so they
  are never reached.

## Structure

```text
checked definitions
      │
      ▼
 Instances ──▶ Layout ──▶ Lower ──▶ Drops ──▶ Yields ──▶ Emit C ──▶ cc ──▶ link
                            │                                              ▲
                            └──────────── LIR, cached per instance ────────┘
```

| OCaml module | Job |
|---|---|
| `Ground` | Ground types: the fully monomorphic types that instances, layouts, and the LIR are written in |
| `Instance` | Instance keys, their C symbols, and collecting the instances reachable from a root |
| `Convention` | How each Truss parameter and result becomes C parameters and results, for lowering and the emitter alike |
| `Monomorphic` | The type checker's types, after substitution, as ground types, and the shape of each ground type |
| `Lir_builder` | Writing a function's LIR a statement at a time, for lowering, generated functions, and intrinsics |
| `Intrinsics` | The operations of `standard::intrinsic`, written into the caller's LIR |
| `Reachable` | The instances a root reaches, and test keys |
| `Build` | Emitting, compiling through the object cache, and linking |
| `Memory_layout` | Sizes, alignment, field placement, tags, and niches for every ground type |
| `Lir` | The lowered IR's types, and printing and hashing it canonically |
| `Lower` | Checked form to LIR: expressions, conditions, patterns, calls, capabilities and `provide`, defaults, derived traits, constants and their evaluators, and the checks in place of proofs |
| `Drops` | Drop elaboration: what each drop lowering wrote still owns, with flags for conditional moves and field-by-field drops for partial ones |
| `Yields` | Yielding methods to continuation calls, and pulled cursors to state machines |
| `Glue` | Generated code for each type: drop, copy, debug output, the binary form code run while compiling writes, and an `any` table's drop |
| `Emit_c` | LIR to C text |
| `Toolchain` | Finding and identifying the C compiler and linker, and running them |
| `Positions` | The table from definitions to files and lines, built at link time |
| `Startup` | The runtime, and the generated C `main` for programs, test runners, and code run while compiling |
| `Compile` | The driver: what each instance compiles to, made once, with its drops elaborated; running constants' evaluators; building and running tests and programs; and keeping test results |

Each is its own dune library, like the lexer's modules, under
`stage0/codegen/`. The larger ones are split into modules of their own,
each building on the ones before it, and the library's main module lists
them:
- **`Lower`:**
  - `Definitions` (the context, and finding an instance's code and signature)
  - `Lowering` (one function's state and scopes)
  - `Targets` (what a call reaches, and evidence)
  - `Matching` (patterns)
  - `Calls`, `Values`, `Expressions`, `Statements`
  - `Constants`, `Derived`, `Generated` (the instances lowering makes)

  The four mutually recursive parts call forward through `Forward`, which
  `Lower` ties.
- **`Emit_c`:** `C_runtime`, `C_types`, `C_values`, `C_code`, `C_data`.
- **`Lir`:** `Ir`, the types and the canonical form; `Encoding`; and
  `Printing`.

The codegen tests are split the same way, by the part they test, and share
`Codegen_support`. `Memory_layout` is not called `Layout`, which is the
lexer's layout stage. Only `Emit_c` and
`Toolchain` know about C.

### Why one IR before C

Lowering straight from the checked form to C text would put drops, yield
lowering, state machines, and hashing all inside a string printer. A small IR
between them gives:

- **One place for every transformation.** Drop elaboration and the cursor
  state machine are dataflow passes over a control-flow graph, which is the
  form they are written in elsewhere. Rust's MIR exists for the same reasons.
- **The thing early cutoff compares.** A definition whose LIR comes out the
  same compiles to the same C, so nothing after it runs again, and tests that
  reach it keep their cached results. The LIR does not depend on which C
  compiler is installed, so a new compiler version invalidates no test
  results.
- **A small emitter.** `Emit_c` prints one C construct per LIR construct, so
  it is easy to check and easy to port when the compiler is rewritten in
  Truss.

The LIR is not SSA. Locals are mutable slots, as in MIR, because the C
compiler builds SSA itself, and slots make drop elaboration and state
machines simpler.

### The C that is emitted

The generated C is C11 plus a few builtins that both clang and gcc provide.
Clang is the supported compiler; gcc should work too. It never includes a
header: the compiler declares the types, the functions it calls, and the
libc functions the standard library uses itself, for each target, so
compiling a file parses only what that file needs. Each file declares the
fixed-width integers from the compiler's own predefined macros, such as
`__INT64_TYPE__`, the target's `USize`, and the runtime's few functions,
and defines only the small helpers it uses, such as the one that gives a
float's bits with every NaN made canonical. Every local starts zeroed, which
the C compiler removes wherever it is overwritten.

The runtime (see [Program startup and failure](#program-startup-and-failure))
is the exception. It is one fixed file for each target, compiled once and
cached, and it includes the system's headers, since its declarations of
signals and alternate stacks differ between systems and parsing them costs
nothing on an edit.

Generated code has no undefined behavior, even if the prover were wrong
about an overflow or a shift:

| Rule | How |
|---|---|
| Integer arithmetic wraps if it ever overflows | `-fwrapv`. Truss proves overflow never happens, so this changes no result. It turns a prover bug into a wrong value rather than undefined behavior, at almost no cost, because indexes are `USize` and wrap anyway. |
| Shift amounts are masked | `x << (n & 63)`. The mask is free on x86-64 and ARM64, where the instruction masks anyway. |
| No type-based alias analysis | `-fno-strict-aliasing`. Truss's own guarantee, that nothing is aliased, is given to the compiler as `restrict` instead. |
| Loops are not assumed to end | `-fno-finite-loops`. A pure loop without a `time` clause may legitimately run until the test's time limit. |
| Floats are exact IEEE 754 | `-ffp-contract=off` and no fast-math. On x86-64, SSE2 is the baseline, never x87. |
| `unreachable` and impossible `match` arms | A call to a compiler-bug report in development builds, `__builtin_unreachable()` in release builds. |

Division by zero and `Int64.minimum / -1` are proven impossible. Making them
defined would cost a test per division, so they are the one place where a
prover bug could still reach undefined behavior. `--check-proofs` catches it
(see [Testing](#testing)).

**Stage0 checks instead of proving.** Stage0 has no prover, so it cannot
refuse a program whose obligations are unproven, as DESIGN.md's builds do.
It builds every program with the checks `--check-proofs` describes
instead, which makes a broken contract a panic rather than a wrong answer
or a memory error:
- Each `requires` clause that can run is tested on entry to its function,
  and to each inlined lending or yielding body, with the parameters bound.
  It panics with "requirement not met: requires ...". That is how an index
  past a `List`'s end is caught. A clause runs unless it uses the
  mathematical `Integer`, a quantifier, a conversion to or from one, or a
  comparison of integers of two types.
- Integer `+`, `-`, and `*` panic with "arithmetic overflow", through
  `__builtin_*_overflow`. The `wrapping_` operations still wrap.
- Integer division panics on a zero divisor, and on the least value over
  -1.

An overflow or division check reports the operator's position in the
code that wrote it, since operators on built-in types are lowered where
they are written. A `requires` check of an inlined lending or
yielding method, such as the `List` index's, reports the call's position,
and one of a function called reports the clause's own. Reporting the
caller's position there too is left for later; Rust's `#[track_caller]`
does it by passing the caller's location. `Compile.create ~checks:false` builds
without the checks, for when the prover exists.

Other flags: `-std=c11 -fno-common -fvisibility=hidden -fno-exceptions
-fno-asynchronous-unwind-tables`, since nothing unwinds, and
`-fno-math-errno`, so `sqrt` is one instruction rather than a call that
might set `errno`; it changes no result. Programs link with `-lm`, since
`fma` is a call into libm on processors without the instruction, such as
baseline x86-64.

## Instances

### Roots

A build starts from roots and compiles only what they can reach:

- **A program:** its `main`.
- **A test run:** each test that must run, that is, each test without a
  cached result.
- **Code run while compiling:** each tagged-template check, each value of a
  template without interpolation, and each `Map` or `Set` constant to build
  (see [Code run while compiling](#code-run-while-compiling)).

### Instance keys

An instance is a definition together with everything that makes one copy of
its code different from another:

- the definition's path, the same `Path.t` every stage names definitions
  by. A method's path names its receiver mode, and an `impl`'s method is a
  method of the `impl`, whether written, derived, or provided by the trait.
  A type's generated functions (drop, copy, debug output) and a pulled
  method's state machine are keyed by their type instead.
- its type arguments, fully monomorphic, as ground types: types with no
  generic parameters, projections, or inference variables, which the type
  checker's substitution has fully decided. A method's are its type's and
  then its own, and an `impl` method's are the `impl`'s and then its own.
  Generic code is compiled once for
  each set of them, as DESIGN.md says, and the type checker has already
  rejected instantiation cycles.
- the capability sets bound to its capability parameters, such as
  `Granted = {FileRead, Clock}`, since the hidden evidence parameters differ
  for each set

Collecting instances walks the LIR of each instance from a root and adds every
instance it calls, takes as a function value, reads as a constant, puts in
an `any` vtable, or drops. The walk is breadth-first and takes references in
the order they appear in the LIR, so the result is the same on every run.

### Symbol names

Each instance gets a C symbol made from its key: a `t_` prefix, the module
path with `__` between its parts, a type's method after a single `_`, and
the type arguments between markers, such as
`t_standard__list__List_each_Of_standard__Int64_End_`. Names stay readable
in profilers and debuggers. A marker is `_`, an `UpperCamelCase` word, and
`_`, such as `_Of_`, `_Mut_`, or `_Drop_`, which no Truss name can contain,
since a name with `_` has no uppercase letter and an `UpperCamelCase` name
has no `_`. So every symbol reads back in exactly one way, and two keys
never share one. A name longer than 200 bytes keeps its first 180 bytes and
adds `_Hash_` and 32 hexadecimal digits of the BLAKE3 hash of the whole
name.

Renaming a definition changes its symbol, so its callers' C changes. Their
types are checked again after a rename anyway, which costs more than
compiling them. Test results do not change, because test keys never contain
names (see [Test results](#test-results)).

## The lowered IR

An instance's LIR is a main function and the nested functions it makes: its
lambdas and its loop bodies. Each function has:

- **Parameters and locals,** numbered, each with a type: a Truss value, a
  pointer to one, a raw scalar such as a drop flag, or a nested function's
  environment. A local has a name only for debug output.
- **Basic blocks,** each a list of statements and one terminator.
- **For a nested function, its environment's fields:** a pointer to each
  local of the function around it that it reads, and for a loop body the
  slots it reports through.

Every choice about how a value is passed is already made in the LIR (see
[Calling convention](#calling-convention)): a parameter that arrives as a
pointer has a pointer type, an argument passed by address is an address
operand, and a result too large to return is written through a pointer
parameter. The emitter only prints.

| Statement | Meaning |
|---|---|
| `place = rvalue` | Write a value to a place. A drop flag is a `Bool` local written this way. |
| `call(target, arguments, destination)` | A call. The target is an instance or nested function with its C signature, a function value, a capability's entry through its evidence, an entry of an `any` value's table, or an intrinsic. The destination is where the result goes: nowhere, returned into a place, or written by the callee into a place through a pointer, which the emitter passes before the arguments. A function value's environment, an evidence pointer, and an `any` value's pointer are part of the target, which the emitter passes first, before any result pointer |
| `drop(place)` | Run the type's drop code. Before drop elaboration: drop whatever the place still owns |
| `free_block(place, variant)` | Free the block of an `indirect` variant whose fields have all been moved out or dropped |
| `echo(text, length, site)` | Record a value's debug output, with its position |

| Rvalue | Meaning |
|---|---|
| an operand | `copy place`, only for types that copy implicitly; `move place`, which leaves the place without a value; a constant; the address of a place; or the moved address of a place, for a large `own` argument, which the callee takes, so the place holds nothing after the call |
| `unary`, `binary` | A primitive operation on built-in types (see [Primitive operations](#primitive-operations)) |
| `convert` | A conversion between built-in numbers that keeps the value |
| `build(type, variant, fields)` | Construct a record or variant. Building an `indirect` variant allocates its block. |
| `is_variant(place, variant)` | Whether a sum type's value holds the variant, however its layout tells them apart |
| `function(code, environment)` | A function value |

| Terminator | Meaning |
|---|---|
| `goto block` | Jump |
| `switch(operand, cases, default)` | Branch on an integer, a `Bool`, or a `Character` |
| `switch_variant(place, cases, default)` | Branch on a sum type's variant |
| `return operand` | Return a value, or nothing |
| `unreachable` | A proven-impossible point |
| `fail(reason, message, length, site)` | End the run with a message and a position: a panic, a failed `assert` in a test, or a `todo` that was reached |
| `yield(operand, resume, stop)` | Before yield lowering only: give a value to the caller's loop, then go on at `resume`, or at `stop` if the loop has ended. A lending method's `yield` has no `stop`, since it always continues. |

Places are a local or a constant's static data, followed by fields, the
fields of a variant, elements, and dereferences of pointers. A variant's
field reaches into the block of an `indirect` variant, and how it is laid
out is the emitter's business, as are tags and niches: the LIR names
variants, never tag values.

Code generation never asks the type checker what a value is: every local
has a ground type, and the layout of each is computed from it.

**The LIR is canonical.** Locals are numbered with the parameters first and
then by first use, blocks in reverse postorder from the entry, unused locals
and unreachable blocks are removed, and every list is in source order. Two
builds of the same definition give byte-identical LIR, as DESIGN.md requires
of every stored result. The LIR is stored and hashed in deterministic CBOR,
like the other stored forms, with the version of code generation. A
reference to another instance is encoded by its key, or by a number in a
test key (see [Test results](#test-results)).

## Data layout

The compiler chooses every layout, and no program can observe one: Truss has
no pointers, no `size_of`, and no foreign code.

### Built-in types

| Type | C | Notes |
|---|---|---|
| `Int8` … `Int64`, `UInt8` … `UInt64` | `int8_t` … `uint64_t` | Declared by the compiler, without `<stdint.h>` |
| `USize`, `ISize` | The target's pointer-sized integers | A `typedef`, so code built to run while compiling can use the target's width on any host |
| `Float32`, `Float64` | `float`, `double` | |
| `Bool` | `uint8_t`, 0 or 1 | Values 2 to 255 are a niche |
| `Character` | `uint32_t` | Values above `0x10FFFF` are a niche |
| `Unit` and records with no fields | Nothing | Erased from parameters, fields, and locals |
| `Never` | No values | A function returning `Never` is `_Noreturn` |

### Records

- **Fields are placed by alignment, largest first, then by name.** Reordering
  fields in the source never changes the layout, which is what DESIGN.md's
  promise that "reordering fields rebuilds nothing" needs. A derived
  `Ordered` compares in declaration order regardless of layout.
- **A record with one field is laid out as that field,** as DESIGN.md
  promises for `UserId(number: UInt64)`: it has the field's size, alignment,
  and spare values. In C it is a `struct` of that one field, which compilers
  pass and store exactly as the field.
- **Fields of zero size take no room.**
- A record is a C `struct` named after its instance, such as
  `t_geometry__Point`.

### Sum types

- **A sum type is a tag followed by the largest variant's fields,** as a C
  `struct` holding a tag and a `union`. The tag is the smallest unsigned
  integer that holds every variant, numbered in declaration order.
- **A sum type with no fields at all is just its tag,** as `Ordering` and
  `LogLevel` are. A variant whose fields all have zero size counts as having
  none, so `Option[Unit]` is one byte.
- **A sum type with one variant has no tag,** and one whose only variant
  has no fields, like `Never`, has zero size.
- **Niches remove the tag where a field has spare values,** as in Rust. When
  every variant but one has no fields, and the one with fields has a field
  with spare values, the other variants use those values instead of a tag.
  Stage0 uses these spare values: non-null pointers, `Bool`, `Character`, and
  the unused values of another sum type's tag. So `Option[List[Int64]]`,
  `Option[Bool]`, and `Option[Character]` are the size of what they hold.
  The field with the most spare values is used, the first in placement order
  on a tie, and the variants without fields take its first values, in
  declaration order. What is left is spare for the type around it, so
  `Option[Option[Bool]]` is still one byte.
  More can be added later without any change to the language, because no
  program can see a layout.
- **An `indirect` variant holds one pointer** to a heap block containing its
  fields. Building one allocates that block; changing it in place writes
  through the pointer; moving its fields out moves them from the block and
  frees it. The pointer is never null, so an `indirect` variant gives a
  niche, and `Option` of a type whose only variant with fields is `indirect`
  is one pointer.

### Arrays

`Array[Element, count]` is the elements in place, wrapped in a one-field C
`struct` so it can be passed and assigned by value.

### Collections and strings

These are standard-library types written in Truss on top of intrinsics (see
[The system interface](#the-system-interface)). Their layouts follow from
their fields like any other type. Truss types cannot define what dropping
them does, so the one type that owns a buffer of elements is built in:
`Storage[Element]` in `standard::intrinsic`, whose drop and copy the
compiler generates. What matters to code generation is:

| Type | Fields | Notes |
|---|---|---|
| `Storage[Element]` | buffer pointer, length, capacity | Elements `0` to `length` are live. Dropping one drops them and frees the buffer. It is `Copyable` exactly when `Element` is, and never `Plain`. An empty one has capacity 0 and a non-null pointer that points at nothing, so `Option[Storage[...]]` has a niche. |
| `List[Element]` | `storage: Storage[Element]` | A one-field record, laid out as its storage |
| `String` | `storage: Storage[UInt8]` | Capacity 0 with a non-empty length means static bytes: dropping frees nothing, and the first method that writes bytes copies them to the heap |
| `Slice[Element]`, `StringSlice` | pointer, length | A view. Turning a `List` into a `Slice` reads two of its three fields |
| `Map`, `Set` | Their fields, written in Truss | No special case |

`String` is the only type with a static form. A constant is a read-only
place, so a `List`, `Map`, or `Set` in static memory is only ever read, and
nothing that drops or changes a value needs to check for static memory.

### `any` values

`any Handler` is two pointers: the heap block holding the value, and a
vtable for that type and trait. A vtable holds:

- the value's size and alignment
- its drop function, and its copy function when the trait requires
  `Copyable`
- one entry for each method that can be called through `any`, after the
  receiver and its evidence

`any value` allocates the block and moves the value in, which is the one
allocation DESIGN.md says it costs.

### Function values

A function value is two pointers: the code and its environment. A lambda's
environment is a `struct`, on the caller's stack, holding a pointer to each
local the lambda reads, since lambdas capture by view. Making one never
allocates. A function that captures nothing has a null environment, and a
named function used as a value goes through a small adapter that ignores the
environment. The code takes the environment as its first parameter, then
the function type's parameters, then one evidence pointer for each
capability in its `uses`. An `own` function-typed parameter accepts only functions that
capture nothing, so storing one never stores a pointer into a stack.

### Cursors

A cursor is the state machine of one pulled yielding method (see
[Cursors](#cursors-1)). Its layout is a state number, the method's
parameters, and the locals that are live across a `yield`, with the states
of any cursors it pulls from inside it. An `own` argument is held as a
value the cursor owns and drops, whatever its size, since the cursor may
outlive the statement that made it. Other arguments are held as their
parameters take them, a view or a pointer to the caller's place. The type has no name in Truss, and
its layout depends on the method's body, so every instance that holds one
reads that body, as Rust's incremental compiler records for
`impl Iterator`.

## Calling convention

The C compiler implements the platform's calling convention. Code
generation only decides how each Truss parameter becomes C parameters.

| Parameter | 16 bytes or less | Larger |
|---|---|---|
| read-only, including `self` | by value | `const T *restrict` |
| `mut` | `T *restrict` | `T *restrict` |
| `own` | by value | `T *restrict` to the caller's memory, which the callee now owns and drops |
| result | returned | written through a `T *restrict` first parameter |

- **Every pointer is `restrict`.** Truss guarantees that a place passed `mut`
  is used by nothing else during the call, and that a viewed original does
  not change while the view is in use. That is exactly what `restrict`
  promises, and it lets the C compiler keep values in registers across
  stores, which it can rarely do for C programs. Rust gives LLVM the same
  facts through `noalias`.
- **Read-only parameters are never copied to be safe.** The original is
  frozen while a view is in use, so passing a pointer is always correct.
- **Hidden parameters follow the written ones,** in this order: the
  default-presence mask, if any parameter has a default; one evidence
  pointer for each capability in `uses`, ordered by the capability's path;
  and the loop body, for a yielding method.
- **Parameters of zero size disappear.**
- **What a call goes through comes first.** A function value's environment,
  a capability entry's evidence, and an `any` value's pointer come before
  the result's pointer and the written parameters.
- **A call names the place its result goes,** however the result travels,
  so that drop elaboration sees every call that gives a place a value,
  including one written through a pointer.

### Defaults

A function with defaults takes a mask with one bit for each parameter that
has a default, set when the caller passed it. The function's first block
fills in each missing argument from its constant. A caller that passes
everything passes 0. This keeps DESIGN.md's rule that defaults are applied by
the function, so changing one compiles only the function again. It avoids
Kotlin's separate `$default` method, which costs an extra call.

Where the default must be owned, for a record field or an `own` parameter,
filling it in copies the constant: free for numbers, strings, and empty
collections, one allocation for a non-empty one. That is how DESIGN.md counts
it.

## Ownership: moves, drops, and copies

### Moves

The type checker records which statements move which places, and rejects any
use of a moved place. The LIR states each move explicitly. A move is a
memory copy of the value's bytes, after which the source place holds nothing
to drop.

### Drop elaboration

Lowering writes `drop(place)` wherever an owned local goes out of scope, on
every path out of the scope, including `return`, `?`, `break`, and a loop's
`stop` at a `yield`, since lowering is where scopes are known. Such a drop
means "drop whatever this place still owns here", which lowering cannot
always tell. `Drops` works it out, as Rust's drop elaboration does over MIR:
a dataflow analysis over each function finds, at each point, which places,
and which fields of places, may own a value and which may not. Then each
`drop(place)` becomes:

- **nothing,** where the place was moved out on every path
- **a drop of the whole place,** where nothing in it was moved out
- **a drop of each remaining field,** where a field was moved out with
  `own config.name`, so the rest of `config` is dropped field by field. Once
  `config.name` is assigned again, `config` is whole again, as DESIGN.md
  describes, and is dropped whole. When the fields of an `indirect`
  variant are moved out, what is left of them is dropped and the variant's
  block is freed.
- **a drop behind a flag,** where the place owns a value on some paths and
  not others, as after `if ready { consume(own item) }`. A flag is a `Bool`
  local, set where the place is given a value and cleared where it is moved
  or dropped.

A place can also be given a value in parts. A record holds a value once
every field with something to drop does, as when a `List` literal fills
its storage in place. Writing an element gives the whole array a value,
because lowering writes every element of a new array before anything reads
it. A drop of an element reached through an index stays as it is, since
elements are never moved out, which is how a `Storage`'s drop drops each
element.

A function starts with every parameter holding a value, except what the
pointer for a large result points to: the LIR names that parameter, so the
first write of the result drops nothing, whatever the caller's memory held
before.

An assignment to a place that may still own a value drops that value first,
after the assignment's own moves, so `items = rebuild(own items)` drops
nothing and `name = other_name` drops the old `name`. The new value is
computed into a temporary first, so the old one is dropped only once
nothing can read it.

Drops of types with nothing to drop, such as plain data, are removed.
Values are dropped in reverse order of declaration. No program can observe
the order, because dropping never runs Truss code.

A panic drops nothing. The process ends, and the operating system reclaims
memory and handles.

### Generated functions for each type

`Glue` generates these for each monomorphic type, each as its own instance,
so they are compiled once and shared:

- **Drop:** frees what the value owns, field by field. A type is *trivial*
  when it holds no `Storage`, no `indirect` variant, and no handle
  anywhere; its drop is empty and every drop of it is removed. A sum type's
  drop switches on its variant and drops that variant's fields. An
  `indirect` variant drops its fields and frees its block. `Storage` drops
  each of its live elements, unless they are trivial, and frees its buffer
  unless its capacity is 0, which is how static bytes and empty storage go
  unfreed. A standard-library handle frees its operating-system resource
  (see [Handles](#handles)). A drop function takes a writable pointer to
  the value.
- **Copy:** `copy()` follows the structure of the value, for each type that
  is `Copyable`; handles and the types that hold one have none. A trivial
  type is a memory copy. A copy function takes the value as a read-only
  parameter and returns the copy, by the
  [calling convention](#calling-convention). `Storage` with capacity 0, as
  static bytes have, or with no elements, is shared, not copied, so a
  static `String` is shared. Otherwise its copy is one allocation of
  exactly its length, and for trivial elements one memory copy, the fast
  path DESIGN.md mentions; other elements are copied one by one.
- **Debug output:** the built-in debug output every type has, used by
  `echo`, failed `assert`s, and the test runner, and to write out values
  computed while compiling. A debug function takes a read-only pointer to
  the value and appends its text to the runtime's debug buffer, one for
  each thread, so it needs nothing from the standard library. The text is
  Truss as it would build the value: `Point(x: 1.0, y: 2.0)`, `Some(3)`,
  with a single field written bare, `None`, `[1, 2, 3]` for storage, views,
  and the standard library's lists and slices, and quoted text with escapes
  for its strings. Integers are decimal, and floats the shortest decimal
  that reads back as the same value, always with a point or an exponent.
- **Derived implementations:** `Equal`, `Hash`, `Ordered`, and `Default`, from
  the type's shape and the version of the rule that derives them.

### Updates in place

- **`with` on an owned base** writes the new fields into the base's memory,
  so `own config with (port: 443)` costs one write per field, as DESIGN.md
  says.
- **Compound assignment** moves the old value into the operator. When the
  operator's trait has an `own self` version, it reuses the old value's
  memory and the result is written back into the same place.

## Lowering expressions

### Primitive operations

These are never calls, at any optimization level. The standard library
declares them through traits so that typing and proofs see ordinary
`impl`s, and the compiler emits their bodies directly:

- arithmetic, comparison, and bitwise operators on built-in integers, floats,
  `Bool`, and `Character`
- `for` over a range of built-in integers, which becomes a counted loop
- indexing and slicing `List`, `Slice`, `Array`, `String` bytes, and
  `StringSlice` bytes, which become address arithmetic with no bounds check
- `?`, `is`, `match`, `with`, building values, reading fields, and turning a
  `List` into a `Slice`

Float comparisons follow DESIGN.md's lawful rules:

| Truss | C |
|---|---|
| `a == b` | `a == b \|\| (a != a && b != b)` |
| `a < b` | `a < b \|\| (a == a && b != b)` |
| `a.ieee_equal(b)`, `a.ieee_less(b)` | `a == b`, `a < b` |
| `x.to_bits()` | the bits, with every NaN replaced by one canonical NaN |

Checked, wrapping, and saturating arithmetic use `__builtin_add_overflow`
and its siblings. Full-width multiplication, used by hashing and
`checked_mul`, uses `unsigned __int128` on 64-bit targets.

### Control flow and patterns

- **`match`** compiles to a decision tree that tests each part of the value
  once, in the order the patterns need, and switches on tags and integers.
  Maranget's "Compiling Pattern Matching to Good Decision Trees" (2008) is
  the method. The tree is built deterministically from the arms in order.
- **`?`** is a tag test and an early return, with the drops elaboration
  inserted.
- **Conditions are lowered as jumps.** `if`, `while`, a guard, and a
  boolean built with `&&`, `||`, `!`, and `is` all go through one lowering
  that branches to a true block and a false one. `&&` and `||` short-circuit
  by branching, and `!` swaps the two.
- **`is`** is the same test as a `match` arm. The names it binds are bound
  on the way to the true block, in a scope that covers the rest of the `&&`
  chain and the `if`'s or `while`'s block and is closed, with its drops, on
  every way out, the false one included. A `while`'s condition temporaries
  end before its body and before its exit.
- **A value is evaluated once for a pattern.** A pattern looks into the
  place an expression names, or into a temporary holding its value, whose
  parts its names then own.
- **A guard sees views** of what its arm binds, so a guard that fails leaves
  the value whole for the next arm. The body then binds the parts again,
  owning them.
- **`while` and `for`** become blocks and gotos. A `for` over anything but a
  range of built-in integers calls `each` (see
  [Lending and yielding methods](#lending-and-yielding-methods)).

### Strings and templates

- **String interpolation builds into one buffer.** `"${count} items in
  ${name}"` adds up the literal lengths, calls each part's `display` into a
  `TextBuilder` with that much room reserved, and returns the `String`. It
  never builds a `Template` or its lists. A `TextBuilder` grows only if a
  part writes more than its first estimate.
- **Numbers display as their debug output does.** Integers are written in
  decimal by the standard library. A float is written by the
  `write_float` intrinsic, the shortest decimal that reads back as the same
  value, which is the runtime's function behind debug output too, so
  `"${x}"` and `echo x` agree.
- **Other tags build a `Template`** with the literal text as constant data,
  which costs nothing, and the parts in a list that the tag usually keeps,
  as `SqlQuery` does. Each part becomes the tag's `Part` through the `From`
  the type checker chose. Stage0 allocates the list of `Literal`s too,
  each a view of static bytes; making that list static data is left for
  later.
- **A template without interpolation is a constant.** Its value is computed
  while compiling and placed in static memory. `Character"a"` and
  `UInt8"\n"` are plain numbers. A `Regex"[a-z]+"` that is only read is used
  in place. Where an owned value is needed, the static value is copied with
  its copy function. This is never more expensive than building it: every
  heap block the copy makes was allocated by `from_template` too, and the
  copy writes no byte that `from_template` did not write.

### Literals and constants

- **A constant** is emitted once as static data, with a symbol, and
  referenced by that symbol. A constant is a read-only place, so its data
  can go in a read-only section. What an instance compiles to is either
  code, its LIR, or data: a ground type and a static value, which the
  emitter writes as C initializers, with the elements of storage and the
  blocks of `indirect` variants as static objects of their own. Lowering
  works a constant's value out exactly from its constant expression:
  integers with Zarith, floats with IEEE arithmetic rounded once to their
  type, and records, variants, strings, lists, and arrays from their parts.
  Another constant's value is written in place, since C cannot initialize
  static data from another object.
- **A list or map literal in a function body** allocates its buffer and
  fills it, which is the one allocation DESIGN.md counts. A literal whose
  parts are all constant, and which is only read, can be static data
  instead.
- **A `Set` or `Map` literal** makes the collection empty and inserts each
  element or entry with the type's own `insert`, so a literal keeps the
  collection's order and, of equal keys, the last, exactly as inserting by
  hand would.

### Code that does not ship

- **`echo`** calls the runtime's echo function with the value's debug output
  and its position. It writes to the test's report in a test, and to stderr
  elsewhere. Builds refuse programs that can reach it, so it only exists in
  test and development runs.
- **`todo`** reached in a test calls a function that tells the runner the
  test is incomplete and ends the worker. Builds refuse programs that can
  reach a `todo`.

## Generics and traits

- **Every call to a trait method is resolved before code generation.** The
  type checker records which `impl` each call means. After
  monomorphization, every such call is a direct call to an instance.
- **A trait's provided methods,** such as `max`, are compiled for each type
  that uses them, unless the `impl` replaces them.
- **Derived implementations may be inlined into callers even in
  development builds.** Their code comes from the type's shape, which every
  caller already depends on through the layout, so inlining them adds
  no dependency.
- **`any` calls** load the method from the vtable and call it with the
  value's pointer.

## Lending and yielding methods

### Loops and lending calls

A lending or yielding method takes the caller's code as a function: the rest
of the caller's statement for a lending method, or the loop body for a
yielding one. That function returns whether to go on. Pulling is a separate compilation of the same method (see
[Cursors](#cursors-1)), made only when some code pulls it.

The standard library's `List.each` is ordinary Truss:

```truss
fn List[Element].each(self) yields Element {
  for index in 0..self.length() {
    yield self[index]
  }
}
```

Its instance for `Int64` becomes:

```c
typedef struct {
  t_step (*call)(void *environment, int64_t item);
  void *environment;
} t_body__Int64;

static void t_standard_list__List_each__Int64(const t_List__Int64 *restrict self, t_body__Int64 body) {
  for (t_usize index = 0; index < self->length; index += 1) {
    if (body.call(body.environment, self->buffer[index]) == t_stop) {
      return;
    }
  }
}
```

In the loop form, `Yields` adds the body as the method's last parameter, and
turns each `yield` into a call to it followed by a switch on its result: on
to the block after the `yield`, or to the `yield`'s `stop` path, whose drops
drop elaboration has already placed. A lending method's `yield` has no
`stop`, so it calls the body and always goes on.

A caller's loop body becomes a function too. Its environment holds pointers
to the caller's locals it reads and changes, and a slot that records why the
loop ended:

- **`continue`** returns `t_continue` early.
- **`break`** records "break" and returns `t_stop`. The method returns at
  that `yield` without running any more of its code, except the drops for
  its own locals.
- **`return value` and `?`** record "return", store the value in the caller's
  frame, and return `t_stop`. After the method returns, the caller checks
  the slot and returns too.

A lending method always continues after its `yield`, as DESIGN.md promises,
even if the caller's statement leaves early. So for a lending call, the
statement's early exits are recorded the same way, but the method runs to its
end before the caller acts on them.

In release builds, and in development builds when the method is in the
standard library or a dependency, `List.each` and the body are in the same C
file. The C compiler inlines both, and the loop becomes a plain loop over the
buffer. In a development build of a package's own yielding method, the body
is called once per element. That is the cost DESIGN.md accepts for keeping
rebuilds narrow.

**Stage0 inlines instead.** Its lowering writes a lending or yielding
method's body into the caller, with each `yield` handing its place to the
caller's statement or running the caller's loop body there: `continue` goes
on after the `yield`, and `break` takes the `yield`'s `stop` path, so the
method's locals are dropped as the loop leaves them. This gives the plain
loop the C compiler would make of the loop form, and needs no rewriting of
the caller into continuation-passing style. The caller then reads the
method's body, and depends on it. A lending method's `yield` must be
its last statement, which needs the loop form above to lift.

A loop over a yielding method that is already inlined around it, as a
tree's `each` loops over its subtrees, would be inlined forever. Stage0
pulls a cursor over the inner call instead, in a heap block the loop frees
on every way out, so a cursor over the method can hold another: the cursor
type holds a pointer to its own type, never itself. This is the room for
every level of recursion that DESIGN.md says other languages allocate
behind the scenes. The language still refuses `next()` on such a cursor,
so it only drives `for` loops.

### Cursors

When some code pulls a yielding method with `next()`, it is lowered a second
time, for pulling. `next` gives its caller a value of its own: what the
method makes is moved out, and a part of a place it yields a view of, such
as a `List` element from `each`, is copied, so that the element stays
where it is. `Yields` makes that version a state machine, as C# and Kotlin
compile iterators:

1. Number each `yield` as a state, from 1 in the order of the blocks. State
   0 is the start, and the state after the last is the end.
2. Find the locals live where a `yield` resumes or stops, by liveness over
   the LIR. They and the parameters become the cursor's fields, beside the
   state number; everything else stays in C locals. A kept local reads and
   writes its field through the cursor, so a `yield` stores nothing.
3. `next()` switches on the state and jumps to the block after that
   `yield`. Each `yield` sets the state and returns `Some` of the value.
   Reaching the end sets the end state and returns `None`, as `next()` does
   ever after.
4. In the version lowered for pulling, a `for` loop or a pulled cursor
   inside the method is an explicit cursor and calls to its `next()`, rather
   than a loop body, since a loop body cannot stop partway. The inner cursor
   is live across the outer `yield`s, so it becomes a field of the outer
   cursor.

A cursor's drop function runs the `stop` path of the `yield` it is stopped
at, which drop elaboration has already filled with the drops of what the
method owns there. That is what DESIGN.md means by a dropped cursor ending
the method at its last `yield`. Before the method starts, it drops the
owned parameters, such as the receiver of an `own self` method, and after
the end it drops nothing. A method whose yields go through a recursive call has
no fixed-size state, so the type checker reports any pull of it, as
DESIGN.md says.

Every cursor implements the prelude's `Cursor` trait, whose `next` is the
state machine's entry, so `any Cursor[Element = Int64]` gets an ordinary
vtable.

## Capabilities

### Evidence

A function that `uses` capabilities takes a hidden pointer to *evidence* for
each one. Evidence is a small `struct` that `provide` builds on the stack:

- a pointer to the implementation value. For `provide mut files`, this is
  the address of the caller's variable, so changes stay in it afterward.
- a pointer to the vtable for that implementation type and capability
- the evidence for the capabilities the implementation itself `uses`, taken
  from the code around the `provide`

A call such as `Clock.now()` loads `now` from the evidence's vtable and calls
it with the implementation pointer and the implementation's own evidence.
Koka calls this evidence passing. It needs no global state, and it is safe
for `parallel` code.

- **How `provide` is lowered.** Each implementation is evaluated once: a
  place by its address, so `provide mut files` changes `files`, and any
  other value into a temporary that lives to the end of the statement. For
  each capability it provides, a local of LIR type `evidence(n)`, a
  `struct t_evidence` followed by room for the `n` evidence pointers its
  `impl` captures, is filled with the implementation's address, the table
  for that `impl`, and the captured evidence, taken from the code around
  the `provide`. The body is lowered with that evidence for those
  capabilities. An `impl`'s `uses` are part of each of its methods'
  signatures, so its methods take that evidence as other functions do.
- **Narrowing needs nothing special.** Inside an implementation of
  `FileRead`, a call to `FileRead.read` uses the evidence captured from
  outside the `provide`, so it reaches the next provider out.
- **Providing a type provides every capability it implements.** `provide`
  builds one evidence `struct` for each, all pointing at the same value.
- **Capability parameters are part of the instance.** `for_each[Item,
  capability Granted]` is compiled once for each set `Granted` stands for,
  and passes on that set's evidence.
- **Function types with `uses`** take evidence when called, like functions,
  after their parameters. A lambda's code reaches only that evidence. A
  callback stored in an `own` parameter gets its evidence from whoever
  calls it.
- **Inside an `impl` of a capability,** a function value that uses the
  capability means the implementation itself, as the type checker rules,
  so its evidence is the implementation's own, made on the stack like a
  `provide`'s. This is how `FileWrite.write_with` hands its callback the
  file system it writes to.
- **`Panic` has no evidence.** It cannot be provided, so `Panic.crash` is a
  direct call into the runtime.

A capability call costs one indirect call, which is small next to the I/O
behind most capabilities. Release builds could call `main`'s real
implementations directly, since `main` gets exactly the ones it declares.
Stage0 does not.

### `main` and the real implementations

The standard library implements each standard capability for real with an
ordinary type, such as a system clock and the real file system. The
generated startup code builds the evidence for exactly the capabilities in
`main`'s `uses` clause and passes it in. An external test gets its declared
capabilities the same way.

### Tasks

Stage0 runs each task on an operating-system thread. DESIGN.md requires that
calls into one implementation never overlap. When a task is spawned, each
piece of evidence it receives is wrapped in evidence whose vtable takes that
implementation's lock around every call. Code in the task cannot tell the
difference, and a fake implementation in a test needs no locking of its own.
Tests provide a seeded `Tasks` implementation that runs tasks one at a time,
which needs no threads or locks at all.

## Parallelism

Stage0 runs `parallel` blocks and `parallel for` loops one branch after
another, which DESIGN.md allows. The type checker and the prover have
already shown the branches disjoint. A later compiler can hand branches to a thread pool with
no change to the LIR above the statement that starts them.

## The system interface

Only the standard library reaches the operating system. The compiler
provides a module, `standard::intrinsic`, that exists in no source file,
like Go's `unsafe` package. Only the `standard` package can import it. It
declares the built-in types, including `Storage[Element]` and its read-only
view `View[Element]`, and the operations the standard library is written
on. The type checker and code generation both match exhaustively on the one
list of operations in the `intrinsic` library, so a new one cannot compile
until both handle it.

| Group | Examples |
|---|---|
| Numbers | arithmetic, wrapping arithmetic, overflow tests, lawful and IEEE comparisons, bit operations, conversions and whether a value fits a type |
| Exact float operations | `sqrt`, `fma`, `floor`, `ceil`, `trunc`, round to nearest even, `to_bits`, `from_bits` |
| Storage | empty, with a capacity, length, capacity, reserve, push, pop, insert, remove, swap, lend an element, view |
| Views | length, lend an element, slice |
| Operating system | write and read bytes, the clock, random bytes, crash; more come with the standard library's real implementations |

`Intrinsics` writes every operation into the caller's LIR, never as a call:
numbers as primitive operations, and storage and views as a few statements
over their fields, so the C compiler sees each whole. The operations that
lend an element, such as `storage_at`, lend the place `buffer[index]`
itself. The one exception is growing storage, which calls the runtime's
grow function, since growing depends on the element type only through its
size: it at least doubles the capacity, so pushing is amortized O(1).

Storage with capacity 0 and a nonzero length is static, as a string
literal's is: it owns no buffer, so dropping it frees nothing and copying
it shares it. Every operation that writes the buffer in place gives such
storage a buffer of its own first, by growing it, which copies the static
elements and never frees them. A `String` constant is static in the same
way. A `List`, `Map`, or `Set` constant has its elements in static memory
too, but records its capacity as its length, so `copy()` of one really
copies; a constant is a read-only place, so nothing writes or drops it. The
standard library never moves a `String`'s storage into another type without
copying it.

The libc functions used are declared by the compiler for each target, so the
generated C still includes no headers. Allocation failure ends the process
with a message, as DESIGN.md allows for running out of memory.

### Handles

The intrinsic module also provides a few handle types, such as a file
descriptor, a process, and a thread. Their drop functions call the
operating system to release them, such as `close`. Stage0 has the first:
`Handle`, a file descriptor in an `Int32`, which is neither `Copyable` nor
`Plain`, with `open_file`, `handle_read`, and `handle_write`. The standard
library's `SystemFileRead` and `SystemFileWrite`, and its `FileReader` and
`FileWriter`, are written on them, as `SystemEnvironment` is on
`environment_variable`, `SystemProcesses` on `run_process`, which spawns
a program found on the `PATH` and waits for it, `SystemClock` on
`clock_now`, and `SystemRandom` on `random_fill`. `SystemTasks.yield_now`
does nothing, since stage0 runs tasks one after another. `NetworkClient` and
`NetworkServer` have no real implementation yet, and a `main` that uses one
is refused with a message saying so. They are the only drops
that do more than free memory, and they run no Truss code, as DESIGN.md
requires. Standard-library types such as `File` hold one in a field, so
their drop functions release the resource by dropping that field.

## Program startup and failure

The C `main` of a program is generated:

1. Install a handler for stack overflow on an alternate signal stack. Truss
   code has no unsafe operations, so a segmentation fault means the stack
   ran out.
2. Turn `argc` and `argv` into `List[String]`, the program's path first, as
   in C. Each `String`'s storage points at the argument itself, with
   capacity 0, so it is never copied, unless it holds bad UTF-8, which a
   copy replaces with U+FFFD.
3. Build the evidence for `main`'s `uses` clause: static evidence for the
   standard library's real implementation of each capability, its
   `System` type, such as `SystemConsole`, whose table of entries is static
   data too.
4. Call Truss's `main` and return its `ExitCode` as the process's status.

Failures end the process without running anything else:

| Failure | What happens |
|---|---|
| `Panic.crash` | Writes the message and position to stderr with `write`, then exits with status 101, as Rust does |
| Running out of memory | Writes a message to stderr and calls `abort` |
| Stack overflow | The signal handler writes a message to stderr and exits with status 101 |

In a test worker, each of these, and a failed `assert` or a `todo`, is
reported to the runner instead (see [The test program](#the-test-program)).
The text of a report is built in a fixed buffer, so failing never
allocates, even when memory ran out.

None of these use stdio, so there are no buffers to flush and no `atexit`
handlers to run.

## Positions

DESIGN.md keeps positions relative to their definition, so adding a line at
the top of a file changes no generated code below it:

- **Each site that can report a position,** such as a panic, an `echo`, or a
  failed `assert`, passes three things: the address of its definition's
  *anchor*, and its line and column within the definition. The line
  counts from 0 at the definition's first line, and the column from 1.
- **An anchor** is an external constant, one per definition, holding the
  file's path and the definition's first line. The generated code only
  refers to it, so its own C never changes when the definition moves.
- **The anchors are defined in one C file generated at link time** from the
  position table. Moving a definition changes only that file.

Release builds can also emit `#line` directives, so debuggers and profilers
see real files and lines. Those builds already compile every definition
again, so absolute lines cost nothing there.

## Code run while compiling

DESIGN.md runs pure, terminating Truss code while compiling: tagged-template
checks, the values of templates without interpolation, and the tables of
`Map` and `Set` constants. That code goes through this same generator, and
runs in the test runner's workers.

- **It is built for the host, with the target's `USize`.** `USize` is a
  `typedef` in the generated C, so code built to run while compiling for a
  32-bit target uses 32 bits on a 64-bit host and computes what the target
  would compute.
- **Results are written out by their debug-output functions** in a binary
  form, and the compiler turns them into static data in C. Values are never
  shared, so every value is a tree, and writing it out is a simple walk.
- **The standard library's checkers ship already compiled** with the
  toolchain, for each host and both widths of `USize`. A dependency's are
  compiled once per version. A package's own are compiled when they change,
  like any other instance.
- **Results are cached** by the hash of the code that ran and its input, so
  a check runs again only when its literal or its code changes.

**What stage0 does.** A constant whose value cannot be folded from its
expression, such as one that calls a function or is a `Map` or a `Set`, has
an `Evaluator` instance: it works the value out, writes its binary form with
the generated `Encode` functions into the debug buffer, and writes that to
standard output. The compiler builds it, with everything it reaches, into a
program for the host, runs it, and reads the bytes back into static data by
the type's shape. The binary form is:
- a scalar's bytes
- a record's fields in order
- a sum's variant index as a `UInt32`, then its fields
- an array's elements
- storage's length as a `USize`, then its elements
- a value of zero size writes nothing

The value is worked out once in a compiler's run, and its program's objects
are cached as any others are. Stage0 has no result cache yet, and does not
run template checks.

## Tests

### The test program

A test run builds one program containing every test that must run, their
instances, and a generated `main` that hands a table of the tests to the
runner in the runtime. The runner starts one worker process per core by
forking itself after startup, so workers share its loaded code. It sends
each worker a test to run, over a pipe, and gets back, on another pipe,
records of the test's end and of its `echo` output. A test that returns has
passed.

A worker whose test fails an `assert`, panics, overflows its stack, runs out
of memory, or reaches a `todo` reports why and ends; one that dies without
a report is recorded from its exit status. The runner then starts a new
worker and carries on, so a new process starts only after a failure. Ending
the worker is also what lets an `assert` inside a lambda end its test, which
an early return could not. The runner kills a worker whose test exceeds the
project's time limit.

A test must free every block it allocates. The runtime counts the blocks
that are allocated and not yet freed, and a test that ends with more than it
started with panics with a compiler-bug message saying how many it left.
Truss has no garbage collector and no way to leak a value on purpose, so a
leak is a bug in code generation, most likely in drop elaboration. Every
test that compiles Truss is therefore also a check of its drops.

Results are printed in the order of the tests, however the tests were spread
over workers, each as `test N outcome`, where the outcome is `passed`,
`failed`, `panicked`, `incomplete`, `timed_out`, or `crashed`, followed by
an optional `message` block and an optional `echo` block, each giving its
length in bytes and then its bytes.

### Test results

A test's result is cached under a key built from all the code it can reach.
DESIGN.md requires that renaming a definition or moving it to another module
finds test results already done, so the key contains no names:

- Walk the instances reachable from the test, in the deterministic order of
  their calls, and number them in the order they are first reached.
- Hash each instance's LIR with every reference to another instance replaced
  by that instance's number, and every path, in a type or a position,
  replaced by a number given in the order paths are first met, since a
  type's path is a name too.
- The test's key is the hash of that numbered list, plus the version of code
  generation and the target. `USize` is a `typedef` in the generated C, so
  the LIR is the same for 32-bit and 64-bit targets, but results such as
  `USize.maximum` are not.

Two programs that differ only in names give the same key, and any change to
what the test can run changes it. A layout change appears in the LIR of
every instance that uses the layout, so it changes the key too.

`truss test` keeps results in the code database's store, as
[DATABASE.md](DATABASE.md#exact-keys) describes, and builds and runs only
the tests without one. Stage0 keeps only a pass
with nothing to show. A failure's message and an `echo` give positions,
which the key leaves out so that moving code keeps its results, so those
tests run again, as do tests that ran out of time or crashed, which the
machine may have caused. A sanitized run keeps nothing.

## Building

### Caching

Lowering is a query, kept current by the code database as DATABASE.md's
"Lowering" describes, and so is each test's key. The steps after it are kept
under exact keys, the hash of exactly the input each consumed:

| Output | Kept by |
|---|---|
| An instance's LIR | A query on the instance, which reads the checked forms it lowers, the signatures it calls, the layouts it uses, and the bodies it inlines |
| An instance's C | The LIR's hash and the emitter's version |
| An object file | The C's text, the C compiler's identity (its `--version` output and path), and the flags, which name the target |
| A program | The objects, the anchors file, and the linker's identity |

Early cutoff happens at the LIR: if an instance's LIR comes out the same, no
C is written, nothing is compiled, and no test that reaches it runs again.
The C compiler's identity is only in the object key, so upgrading clang
recompiles objects but invalidates no test result.

### C files and optimization

- **Object files are cached by their key,** each written under a temporary
  name and renamed into place, so a build that stops partway leaves no
  broken object. Files that need compiling are compiled in parallel, across
  the machine's cores.
- **Development builds compile one C file per instance.** The C compiler
  runs once for each instance whose LIR changed, in parallel across cores.
  Small standard-library and dependency instances that the instance calls
  are emitted into the same file as `static` functions, so the C compiler
  can inline them, as DESIGN.md allows for development builds. They are
  chosen by size, and every yielding method is chosen. Each one is recorded
  as a body the instance reads.
- **A package's own code compiles at `-O1`** in development builds, which is
  fast to compile and avoids the stack traffic of `-O0`.
- **The standard library and dependencies compile at `-O2`** and are cached,
  so development builds of a project run them at full speed.
- **Release builds** put each module's instances in one C file at `-O2` and
  link with ThinLTO, so the C compiler can inline across every definition.

One C file per instance means many small compiler runs on a cold build. If
that is slow, instances can be grouped by definition later. The change
affects only build speed.

### The command

`truss test DIRECTORY` checks a package, reporting every diagnostic, then
builds its tests into one test program and runs it. `truss run DIRECTORY
ARGUMENTS` builds the package's program from its `main` and runs it with
the arguments, on the terminal's own input and output, so it can prompt and
read, and exits with its status. A package is a directory with a `truss.toml` naming it, and
each `.truss` file under it is one of its modules. Object files are kept in
the code database's store.

### Linking

Stage0 links in full every time, as IMPLEMENTATION.md records: with lld or
mold on Linux and the system linker on macOS, against the platform's libc.
The standard library is linked from its cached objects. Making linking
incremental is deferred.

## Testing

The tests follow IMPLEMENTATION.md's rules for testing: each states one
fact about a small input, and there are no golden files.

- **Focused tests.** A test gives a small definition and asserts exact facts
  about what code generation makes of it, rather than comparing a dump of
  its whole LIR. For example: a `for` over a range of `Int64` lowers to a
  loop with no call; a field moved out with `own` is dropped exactly once,
  on every path; `Option[List[Int64]]` has no tag; a `mut` parameter becomes
  a `restrict` pointer. A test that runs a small program asserts its output
  and exit status.
- **The generated C is checked strictly.** Every focused test that emits C
  compiles it with `-Wall -Wextra -Werror` and a list of warnings known not
  to apply to generated code, which catches emitter bugs that a C compiler
  would otherwise accept quietly. The list is `-Wno-unused-parameter`, since
  an adapter ignores its environment and a trait's implementation may not
  read every parameter, and `-Wno-unused-but-set-variable`, since
  `let _ = ...` computes a value that nothing reads.
- **Output is deterministic.** A test lowers and emits the same definition
  twice and checks that the LIR and C are byte-identical.
- **The documents' complete programs build and run,** each as a test of its
  own.
- **Tools, run by hand, in `stage0/tools/`:**
  - **Sanitizers.** Build programs with AddressSanitizer and
    UndefinedBehaviorSanitizer. A memory error in Truss code can only come
    from a bug in the compiler or the prover, so any report is one. Being
    able to do this is one benefit of emitting C. `truss test --sanitize` and
    `truss run --sanitize` build this way, and `TRUSS_SANITIZE=1 dune test`
    builds every codegen test this way.
  - **`--check-proofs`.** A compiler flag, for testing the compiler only,
    that emits a run-time check for every proven obligation: indexes,
    overflow, division, shifts, and `unreachable`. A failed check reports a
    prover bug with the obligation's position, which checks the prover
    against real executions.
  - **Development and release agree.** Run programs built both ways and
    compare their outputs. Later, the compiler written in Truss is checked
    against stage0 the same way.

  Each problem a tool finds becomes a focused test of its own.

## Open questions

- **Program arguments that are not UTF-8.** `main` takes `List[String]`, and
  a `String` is always UTF-8, but a Unix argument can be any bytes. Rust's
  `std::env::args` panics on such an argument, Python substitutes escapes,
  and some programs replace bad sequences with U+FFFD. The language should
  decide. Until then, stage0 replaces bad sequences with U+FFFD.
- **Static or dynamic libc on Linux.** Stage0 links dynamically on both
  platforms. A static program with musl would match IMPLEMENTATION.md's
  "single binary" more closely.
- **Release-only optimizations:** calling `main`'s real capability
  implementations directly, and giving proven `requires` clauses to the C
  compiler as assumptions. Both are deferred.
