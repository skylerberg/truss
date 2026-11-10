# Truss Code Generator

This document describes stage0's code generation, in
[`stage0/codegen/`](stage0/codegen): everything between the type checker's
output and a program that runs. It follows the decisions in
[DESIGN.md](DESIGN.md) and [SYNTAX.md](SYNTAX.md), reads the checked form
that [TYPECHECKER.md](TYPECHECKER.md) describes, and relies on the proofs
that [PROVER.md](PROVER.md) describes.

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

- check anything about the program. Every error in a program is reported
  by an earlier stage. A failure here is a bug in the compiler, or a valid
  program that stage0 cannot build yet (see [Failures](#failures)).
- insert run-time checks into a program. Indexes, overflow, division,
  shifts, and `unreachable` have all been proven before a program is built.
  The only checks in a program are the ones it asks for, such as
  `checked_add` or `items.get(i)`. Test builds, and code run while
  compiling, are different: they check every operation that could fail, so
  that they can run before the prover has finished, as DESIGN.md's "Tests
  do not wait for proofs" describes.
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

### Why C

Truss has no foreign code, so the standard library's hashing, crypto, and
text handling run on Truss's own generated code, and nothing can drop to C
for speed. The backend must therefore optimize well. QBE, the obvious small
backend, has no inliner, no 128-bit multiply, no bit-counting, rotate, or
byte-swap instructions, no `sqrt`, no SIMD, no atomics, and no way to say
that pointers do not alias. C compilers have all of these, and Truss proves
no aliasing, which C expresses with `restrict`. Linking libc already needs
the platform's C toolchain, so emitting C adds almost no dependency.

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

The compiler lays every type out itself (see [Data layout](#data-layout)),
and the C compiler lays each one out again from the `struct` it is given.
Code generation relies on the two agreeing: the size it allocates for a
value, and whether a value is passed by address, come from its own layout.
So each type a file defines is followed by a static assertion of its size
and alignment, and a layout the C compiler would not make is a C file that
does not compile, on whatever target that is.

The runtime (see [Program startup and failure](#program-startup-and-failure))
is the exception. It is one fixed file for each target, compiled once and
cached, and it includes the system's headers, since its declarations of
signals and alternate stacks differ between systems and parsing them costs
nothing on an edit. A test program's runtime is a second such file: it adds
the test runner and the count of blocks a test must free, which a program
that ships has no use for.

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
prover bug could still reach undefined behavior.

**Test builds check instead of waiting for proofs.** A test build, and code
run while compiling, is built with the checks below whether or not the
prover has finished, so tests run alongside the prover, and a broken
contract is a failed test rather than a wrong answer or a memory error.
The checks do not depend on which proofs passed, so neither do the test
build's LIR and the test results cached under it. A program is built
without them, once its proofs are done. Stage0 builds programs with the
checks too, whether or not their proofs are done:
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
and one of a function called reports the clause's own.

Other flags: `-std=c11 -fno-common -fvisibility=hidden -fno-exceptions
-fno-asynchronous-unwind-tables`, since nothing unwinds, and
`-fno-math-errno`, so `sqrt` is one instruction rather than a call that
might set `errno`; it changes no result. Programs link with `-lm`, since
`fma` is a call into libm on processors without the instruction, such as
baseline x86-64.

The emitted C compiles without warnings under `-Wall -Wextra -Werror`,
which every test that emits C enforces. Two warnings are turned off:
`-Wno-unused-parameter`, since an adapter ignores its environment and a
trait's implementation may not read every parameter, and
`-Wno-unused-but-set-variable`, since `let _ = ...` computes a value that
nothing reads.

## Instances

### Roots

A build starts from roots and compiles only what they can reach:

- **A program:** its `main`.
- **A test run:** each test that must run, that is, each test without a
  cached result.
- **Code run while compiling:** each constant whose value cannot be folded
  from its expression, such as a `Map` or a `Set`, and each tagged
  template's check (see
  [Code run while compiling](#code-run-while-compiling)).

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
builds of the same definition give byte-identical LIR, as DATABASE.md
requires of every result. The LIR is hashed in deterministic CBOR (RFC 8949,
section 4.2), with the version of code generation. The encoder is small
enough to write directly, which keeps the exact byte format under the
project's control, and the same one must later be written in Truss and
produce the same bytes. A
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
of any cursors it pulls from inside it. A parameter's field is named by its
place among the parameters that have a size, in `Convention`, which is how
the code that makes a cursor and the method's state machine agree on it. An `own` argument is held as a
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

### Who owns a value

Every value lowering makes has an owner from its first moment, so that no
way out of the code can forget it:

- **A scope owns what is dropped as it ends.** A block's scope owns the
  names bound in it. Each statement has a scope of its own, which owns the
  statement's temporaries: an argument evaluated before the call, a value a
  pattern looks into, the text an interpolation builds. Scopes are one
  stack, so `return`, `?`, `break`, `continue`, and a loop's `stop` at a
  `yield` each leave exactly the scopes inside where they go, the
  statements' among them.
- **A local for a value is made with its owner.** Lowering has no way to
  make one without: a temporary belongs to the statement being lowered, and
  a binding to the names around it. The one exception is the slot for the
  function's result, which is the caller's once the function returns.
- **A parameter says whose it is.** The function owns an `own` parameter,
  and drops it unless it gives it away. Any other is the caller's, and one
  passed by value is marked *borrowed* in the LIR: it holds the bits of a
  value something else owns, and nothing drops it. An `own` parameter with a
  default may arrive holding nothing, so its name is bound to a local the
  function owns, which takes the argument or the default.

### Drop elaboration

Lowering writes `drop(place)` wherever a scope ends, on every path out of
it, for each thing the scope owns. Such a drop means "drop whatever this
place still owns here", which lowering cannot always tell. `Drops` works it
out, as Rust's drop elaboration does over MIR: a dataflow analysis over
each function finds, at each point, which places, and which fields of
places, may own a value and which may not. Then each `drop(place)` becomes:

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

A function starts with every parameter it owns holding a value, except
what the pointer for a large result points to: the LIR names that
parameter, so the first write of the result drops nothing, whatever the
caller's memory held before.

**A write gives a place a value and drops nothing.** Whatever replaces a
value drops it first, with a `drop` of its own. So an assignment works its
new value out into a temporary, drops what the place still owns, and moves
the temporary in: `items = rebuild(own items)` drops nothing, since the
place was moved from, `name = other_name` drops the old `name`, and
`names[0] = other_name` drops the old element. A compound assignment and a
field written by `with` do the same, and each evaluates the place it
names once. The temporary is also what keeps a call's result apart from
its arguments: a callee writes a large result through a `restrict` pointer,
which must not be to a place the callee was also given, as in
`point = moved(point)`.

`Drops` checks what it is given, so that a mistake in lowering is a
compiler bug in whatever code has it, not a leak in the runs that reach
it:
- no write is to a place that may still own a value
- where a function returns, none of its locals owns a value still. What a
  pointer points at is not looked at, since it may be the caller's or a
  block's.

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
  [calling convention](#calling-convention). A `Storage` is in one of
  three states, which its capacity and length say, and its copy follows
  the state:
  - *empty*, with capacity 0 and no elements, and *static*, with capacity
    0 and elements it does not own, as a string literal has: it owns no
    buffer, so it is shared, not copied
  - *owning*, with a capacity that is not 0: it owns a buffer on the heap,
    which is never shared, since both would free it. With no elements its
    copy is empty. Otherwise its copy is one allocation of exactly its
    length, and for trivial elements one memory copy, the fast path
    DESIGN.md mentions; other elements are copied one by one.

  One module defines the two built-in types that hold a buffer, `Storage`
  and `View`: their fields, these states, and how each is built. Nothing
  else in code generation names their fields.
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
  the type checker chose. The list of `Literal`s is allocated too, each a
  view of static bytes.
- **`Character"a"` and `UInt8"\n"` are plain numbers.** Every other tagged
  template calls its tag's `from_template` when it runs.

### Literals and constants

- **A constant** is emitted once as static data, with a symbol, and
  referenced by that symbol. A constant is a read-only place, so its data
  can go in a read-only section. What an instance compiles to is either
  code, its LIR, or data: a ground type and a static value, which the
  emitter writes as C initializers, with the elements of storage and the
  blocks of `indirect` variants as static objects of their own.
- **A constant's value is what running its expression gives.** Lowering
  folds what it can to exactly that, to save the run: literals, operators
  on integers, with Zarith, on floats, with IEEE arithmetic rounded once to
  their type, and on `Bool`, and records, variants, strings, lists, and
  arrays of parts that fold. Another constant's value, where it folds, is
  written in place, since C cannot initialize static data from another
  object. Whatever the folder does not know, or cannot give exactly, such
  as a sum that does not fit its type, is not folded: the constant's
  evaluator is run (see [Code run while compiling](#code-run-while-compiling)),
  so folding can be incomplete and never wrong. A constant made of one that
  is run is run too, and its evaluator copies that one's static data,
  since nothing is moved out of a constant.
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
method's body, and depends on it.

A lending method goes on after the caller's statement, as DESIGN.md has
it, and its own values live until then, so it may lend one it made. The
LIR is a graph of blocks, so this needs no function for the rest of the
statement:

- The method's body is written into the caller up to its `yield`, which
  jumps to the rest of the caller's statement with the place it lends.
- What is left of the method, its code after the `yield` and the drops of
  what it owns, is written once, in blocks nothing reaches yet.
- The scope the lending call is in owns the lend, as it owns a temporary.
  As that scope ends, on each way out of it, the code sets a selector to
  the way it was going and jumps to what is left of the method, which ends
  by going on that way. So a `return` or a `?` in the statement finishes
  the method first, as an ordinary end does, and lends in one statement
  finish in reverse order.

Where nothing is left, as for an index into a `List`, whose method ends at
its `yield` owning nothing, the method simply ends there and the lend costs
nothing.

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
behind most capabilities.

### `main` and the real implementations

The standard library implements each standard capability for real with an
ordinary type, such as a system clock and the real file system. The
generated startup code builds the evidence for exactly the capabilities in
`main`'s `uses` clause and passes it in. An external test gets its declared
capabilities the same way.

### Tasks

Stage0 runs tasks one after another. The standard library's `Tasks` has
only `yield_now`, which does nothing, and nothing runs on a second thread.

## Parallelism

Stage0 runs `parallel` blocks and `parallel for` loops one branch after
another, which DESIGN.md allows.

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

The intrinsic module also provides one handle type: `Handle`, a file
descriptor in an `Int32`, which is neither `Copyable` nor `Plain`, with
`open_file`, `handle_read`, and `handle_write`. Its drop function calls the
operating system to release it, with `close`. The standard
library's `SystemFileRead` and `SystemFileWrite`, and its `FileReader` and
`FileWriter`, are written on them, as `SystemEnvironment` is on
`environment_variable`, `SystemProcesses` on `run_process`, which spawns
a program found on the `PATH` and waits for it, `SystemClock` on
`clock_now`, and `SystemRandom` on `random_fill`. `SystemTasks.yield_now`
does nothing, since tasks run one after another. `NetworkClient` and
`NetworkServer` have no real implementation, and a `main` that uses one is
refused with a message saying so. A handle's is the only drop that does more
than free memory, and it runs no Truss code, as DESIGN.md requires.
Standard-library types such as `File` hold one in a field, so their drop
functions release the resource by dropping that field.

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
  refers to it, so its own C never changes when the definition moves. The
  driver names the file: a development build as the current directory
  reaches it, as diagnostics name it, and a release build from the
  package's root, so the program is the same wherever it was built.
- **The anchors are defined in one C file generated at link time** from the
  position table. Moving a definition changes only that file.

Release builds can also emit `#line` directives, so debuggers and profilers
see real files and lines. Those builds already compile every definition
again, so absolute lines cost nothing there.

## Code run while compiling

DESIGN.md runs pure, terminating Truss code while compiling. That code goes
through this same generator. Stage0 runs it for two things: a constant whose
value cannot be folded from its expression, and a tagged template's check.

- **It is built for the host, with the target's `USize`.** `USize` is a
  `typedef` in the generated C, so code built to run while compiling for a
  32-bit target uses 32 bits on a 64-bit host and computes what the target
  would compute.
- **Results are written out in a binary form,** and the compiler turns them
  into static data in C. Values are never shared, so every value is a tree,
  and writing it out is a simple walk.
- **A constant's evaluator runs with no time limit,** since DESIGN.md
  requires its code to be pure and to terminate. A run that fails, as on a
  stack overflow, is reported as an error.

A constant whose value cannot be folded from its expression, such as one
that calls a function or is a `Map` or a `Set`, has an `Evaluator`
instance: it works the value out, writes its binary form with
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
are cached as any others are.

A tagged template's check has a `Template_check` instance, of the tag's
`from_template` and the template's literal texts: it builds a template of
those texts and no parts, works out each of `from_template`'s `requires`
clauses that can run, and writes each out as a `Bool`. The prover asks it
only of a clause that reads the template's literals alone, which its parts
cannot change (see PROVER.md, "Running code while proving"). It runs with
the test time limit, and its results are kept under the key of the code
that ran, as test results are, so a check runs again only when its texts
or its code change.

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

A test must free every block it allocates. A test program's runtime counts
the blocks that are allocated and not yet freed, and a test that ends with
more than it started with panics with a compiler-bug message saying how
many it left.
Truss has no garbage collector and no way to leak a value on purpose, so a
leak is a bug in code generation, most likely in drop elaboration. Every
test that compiles Truss is therefore also a check of its drops.

The runner writes a line as it hands each test to a worker, `start N`, and
each test's result as soon as the test ends, so that `truss test` can show
progress. A result is an optional `message` block and an optional `echo`
block, each giving its length in bytes and then its bytes, then the line
`test N outcome microseconds`, which ends the record, so a reader knows a
record is whole when that line arrives. `N` is the test's number in the
table, the outcome is `passed`, `failed`, `panicked`, `incomplete`,
`timed_out`, or `crashed`, and the duration is the time from handing the
test to a worker to its end. Results therefore come in the order tests end,
which depends on the workers, and `Compile.run_tests` puts them back in the
order of the tests.

### Test results

A test's result is cached under a key built from all the code it can reach.
DESIGN.md requires that renaming a definition or moving it to another module
finds test results already done, so the key contains no names. It is
composed from the instances' own keys, so that an edit changes the keys of
the tests that can reach the edited code, and costs what can reach it:

- **An instance's own hash** is the hash of its LIR with each instance it
  refers to written as that instance's place in the list of what it refers
  to, and each path as a number given in the order paths are first met. It
  holds no name, so renaming or moving a definition changes no hash. A
  constant worked out by running code refers to its evaluator, whose code is
  what decides its value.
- **The key of everything an instance can reach** is its own hash and the
  key of each instance it refers to, in order.
- **Instances that reach each other are keyed as a group.** A key cannot be
  made of keys that are made of it. So the groups of instances that reach
  each other are found, by Tarjan's algorithm, among everything the wanted
  tests and programs reach, and an instance of a group is keyed by the group
  as a walk from the instance reaches it: each of the group's instances, in
  the order the walk first reaches them, as its own hash and what it refers
  to, a number for an instance of the group and a key for any other. An
  instance that refers only to itself is no group, since its own hash marks
  that.
- **The wanted tests and programs are an input.** Finding groups needs
  somewhere to start, and starting from every test would lower every test's
  code when one test is asked about. So a driver says which tests' keys it
  wants before it asks for them, and the database adds them to this input.
  A key asked for without that is an error wherever the code reaches itself.
- **The groups come out the same unless one forms or changes.** Finding them
  reads what every reached instance refers to, which changes when a call is
  added or removed, and its result changes only when a group does. It is of
  an earlier phase than the keys, so an edit that changes no group costs the
  keys nothing but the keys of what can reach the edit.
- **The test's key** is the key of everything the test's own instance can
  reach, with the version of code generation and the target. `USize` is a
  `typedef` in the generated C, so the LIR is the same for 32-bit and 64-bit
  targets, but results such as `USize.maximum` are not.

Two programs that differ only in names give the same key, and any change to
what the test can run changes it. A layout change appears in the LIR of
every instance that uses the layout, so it changes the key too. A function
that a thousand tests reach is hashed once, and an edit to it makes its own
hash again, and the keys of what reaches it.

Finding the groups walks every instance the wanted tests reach, when what
any of them refers to changes. That is the one step here whose cost follows
the tests asked about and not the change, and it reads only lists of what
instances refer to.

`truss test` keeps results in the code database's store, as
[DATABASE.md](DATABASE.md#exact-keys) describes, and builds and runs only
the tests without one. Stage0 keeps only a pass with nothing to show, and
never an external test's, whose result depends on the world, and the
result holds `passed` and the duration of the run that kept it, which
`truss test --timings` shows for a cached test. A result in any other form
counts as none. A failure's message and an `echo` give positions,
which the key leaves out so that moving code keeps its results, so those
tests run again, as do tests that ran out of time or crashed, which the
machine may have caused. A sanitized run keeps nothing.

## Failures

Code generation fails in three ways, and tells them apart, since each is
for someone else to act on:

| Failure | What it is | How it is reported |
|---|---|---|
| A compiler bug | An invariant of code generation does not hold: a pass met LIR it cannot have been given, or the verifier refused what a pass made | An exception that carries the stage that found it, what it found, and what the compiler was doing, such as the instance being lowered. Nothing in code generation catches it: the command line reports it once and exits with status 2. |
| A program stage0 cannot build yet | The program is valid, and lowering has no code for something in it, which [Not built](#not-built) lists | An exception that carries what it is and its position. The driver gives it as the build's error, with the file and line. |
| A build that cannot be done | The C compiler or the linker refused, or a program run while compiling ended badly | The build's error, with what they wrote |

The two exceptions are every stage's to use. A broken invariant that the
OCaml standard library finds first, such as a missing list element, is
turned into a bug where an instance is lowered, so no failure of the
compiler reads as a failure of the program.

### The verifier

`Verify` checks the LIR, so that a mistake in lowering or in a pass is a
compiler bug that names its instance, instead of C that is wrong in a way
the C compiler cannot see. Each instance is a C file of its own, which
declares what it calls from its own side, so a caller and a callee that
disagree compile and link without complaint.

Each instance is checked as it is lowered, once its passes have run:
- every block a terminator goes to and every local a place names exists,
  and every place fits the type it projects from
- no `yield` is left
- a function with a result returns one on every `return`, and one without
  returns none
- a call gives its target as many arguments as the target's signature
  takes, and writes a large result to a place it does not also pass by
  address
- a value that has a size is built as a record or a variant its type has,
  with fields the type has, since the emitter leaves out a field it does
  not find in the layout, as it must for a field of no size
- a call of a nested function names it with the signature it has

Everything a build links is checked together before any C is emitted:
- each call names its callee with the signature the callee has, as does
  each entry of a table and each named function used as a value
- a drop reaches a drop function
- each address of static evidence, of a table, or of a constant reaches one
- what an instance compiles to is the instance that was asked for

## Building

### Lowering

Code generation's lowering is a query, so a test run after an edit lowers
only the instances the edit reached:

- **An instance's LIR** is a query keyed by the instance and by how it is
  lowered: the target's widths, and whether the program checks what the
  prover would prove. A pulled method's version, whose locals make its
  cursor's fields, is a query of its own.
- **Each computation lowers in a context of its own,** made from the
  query's reads. A layout or a piece of generated code worked out on the way
  is read through that query, never cached where another query could use it
  without reading what it came from.
- **A constant that is worked out by running code** is the one result a
  query cannot make, since running code is not a function of reads. Its
  query says so instead, and the build runs the constant's evaluator, whose
  code is lowered by the same query, and puts the value in the program. Only
  that constant's data depends on running code; every instance that uses it
  refers to it by name.

### Caching

Lowering is a query of the code database, and so are each instance's own
hash, what it refers to, and its key (see [Lowering](#lowering) and
[Test results](#test-results)). [DATABASE.md](DATABASE.md) describes how
such results are kept current, and found by any worktree that reads the
same. The steps after lowering are kept under exact keys, the hash of
exactly the input each consumed:

| Output | Kept by |
|---|---|
| An instance's LIR | A query on the instance, which reads the checked forms it lowers, the signatures it calls, the layouts it uses, and the bodies it inlines |
| An object file | The C's text, the C compiler's identity (its `--version` output and path), and the flags, which name the target |

Early cutoff happens at the LIR: if an instance's LIR comes out the same, so
does its C, so its object is found, nothing is compiled, and no test that
reaches it runs again. The C compiler's identity is only in the object key,
so upgrading clang recompiles objects but invalidates no test result.

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
- **Release builds** compile at `-O2` and optimize across every file as
  they are linked, with ThinLTO where the C compiler is clang and LTO
  otherwise, so the C compiler can inline across every definition. They
  keep one C file per instance, so each object is still cached on its own
  and compiled in parallel.

One C file per instance means many small compiler runs on a cold build. If
that is slow, instances can be grouped by definition later. The change
affects only build speed.

### The command

`truss test`, `truss run`, and `truss build` drive code generation, as
[CLI.md](CLI.md) describes: a test run builds the tests into one test
program, `run` builds the package's program from its `main` for
development, which the command line runs on its own terminal, and `build`
builds it for release. Both refuse a program whose `main` can reach a
`todo`, which `Compile.unshippable` finds by walking the instances `main`
reaches, as a build does, without compiling them, and `build` refuses an
`echo` too. Object files are kept in the code database's store.

### Linking

Stage0 links in full every time: with lld or mold on Linux and the system
linker on macOS, against the platform's libc. It is the one step of an
everyday edit whose cost grows with the whole program. The standard library
is linked from its cached objects. The linker is given the objects' names in
a file, since a program of a few thousand instances names more objects than
a command line can hold.

## Not built

- **Programs built without checks.** A program is to be built without the
  checks a test build has, once its proofs are done. Stage0 builds programs
  with the checks too. A flag for testing the compiler, `--check-proofs`, is
  then to build a program with the checks: a failed check in code whose
  obligations were all proven reports a prover bug with the obligation's
  position, which checks the prover against real executions.
- **A `requires` check that reports its caller's position.** One of a
  function called reports the clause's own. Rust's `#[track_caller]` does
  this by passing the caller's location.
- **A constant's value kept between runs.** It is worked out again in each
  run of the compiler.
- **Checkers shipped compiled.** The standard library's are to ship already
  compiled with the toolchain, for each host and both widths of `USize`, and
  a dependency's to be compiled once per version.
- **A quantifier in code.** It is to be a loop over its range or collection,
  through the same `each` a `for` loop calls, that stops at the first
  element that decides the answer: `forall` at the first false body,
  `exists` at the first true one.
- **A lending method with more than one `yield`,** one on each of several
  paths, and one that lends through a call to itself.
- **A lambda in a yielding method that is pulled,** and in a pulled method
  a default for a parameter that is passed by address or is a view.
- **A range without both of its ends, as a value.**
- **A template without interpolation as a constant.** Its value is to be
  computed while compiling and placed in static memory. A `Regex"[a-z]+"`
  that is only read is then used in place, and where an owned value is
  needed, the static value is copied with its copy function. This is never
  more expensive than building it: every heap block the copy makes was
  allocated by `from_template` too, and the copy writes no byte that
  `from_template` did not write.
- **A template's list of literals as static data.** It is allocated.
- **Tasks on threads.** Each task is to run on an operating-system thread.
  DESIGN.md requires that calls into one implementation never overlap, so
  when a task is spawned, each piece of evidence it receives is wrapped in
  evidence whose vtable takes that implementation's lock around every call.
  Code in the task cannot tell the difference, and a fake implementation in
  a test needs no locking of its own. A seeded `Tasks` implementation for
  tests runs tasks one at a time, and needs no threads or locks at all.
- **`parallel` branches at once.** Branches can go to a thread pool with no
  change to the LIR above the statement that starts them.
- **Handles for processes and threads, and real implementations of
  `NetworkClient` and `NetworkServer`.**
- **Keeping an instance's C and a linked program.** The C is emitted again
  for each build, and found as an object by its text. It could be kept by
  the LIR's hash and the emitter's version, and a program by its objects,
  the anchors file, and the linker's identity.
- **Incremental linking.** The likely way is a long-running test runner that
  keeps the program loaded, loads only the definitions that changed as a
  small shared library, and forks test workers from itself. Truss has no
  mutable global state, so swapping code in a running process needs no state
  to be carried over.
- **Release-only optimizations:** calling `main`'s real capability
  implementations directly, since `main` gets exactly the ones it declares,
  and giving proven `requires` clauses to the C compiler as assumptions.
- **Comparing development and release builds.** A tool would run programs
  built both ways and compare their outputs, and later check the compiler
  written in Truss against stage0 the same way.
- **Program arguments that are not UTF-8** are not decided. `main` takes
  `List[String]`, and a `String` is always UTF-8, but a Unix argument can be
  any bytes. Rust's `std::env::args` panics on such an argument, Python
  substitutes escapes, and some programs replace bad sequences with U+FFFD.
  Stage0 replaces bad sequences with U+FFFD.
- **Static or dynamic libc on Linux** is not decided. Stage0 links
  dynamically on both platforms. A static program with musl would match
  IMPLEMENTATION.md's "single binary" more closely.
