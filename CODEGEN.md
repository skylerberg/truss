# Truss Code Generator

This document describes stage0's code generation, in
[`stage0/codegen/`](stage0/codegen): everything between the type checker's
output and a program that runs. It follows the decisions in
[DESIGN.md](DESIGN.md) and [SYNTAX.md](SYNTAX.md), reads the core form
that [TYPECHECKER.md](TYPECHECKER.md) describes, and relies on the proofs
that [PROVER.md](PROVER.md) describes.

## What code generation does

Code generation takes the core form of each definition the program can
reach and produces C, which a C compiler turns into object files, which a
linker turns into a program. In the core form every call has a resolved
callee and one argument per parameter, each argument is marked as a place
or a value, every operator is resolved to an intrinsic operation or a call,
and every type is fully inferred. A slice of a range, `items[1..3]`, is a
call of the base type's `slice_range` with both bounds worked out, so
lowering it is lowering that call. Lowering from the core form needs no
name resolution and no type inference. Every proof obligation has been
discharged by then.

Lowering reads nothing else of a definition's body. A function's
parameters, parameter defaults, `requires` checks, and body all come from
its core form, and so do the lending and yielding methods inlined into it,
the pulled version of a yielding method, a constant's value, and the check
of a tagged template. The syntax tree gives only the source text and the
positions that failure messages quote.

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
- makes each branch of a `parallel` statement a function of its own, which
  the runtime's threads run
- makes each branch of a `concurrent` statement a function too, and spawns
  it as a task through the `Tasks` capability
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

Lowering straight from the core form to C text would put drops, yield
lowering, state machines, and hashing all inside a string printer. A small IR
between them gives:

- **One place for every transformation.** Drop elaboration, the cursor
  state machine, and the outlining of `parallel` branches are passes over a
  control-flow graph, which is the form they are written in elsewhere.
  Rust's MIR exists for the same reasons.
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
nothing on an edit. It holds what must not be Truss: the handler for a
stack that ran out, failing, which builds its text in a fixed buffer so
that it never allocates, and allocation. A test program's runtime is a
second such file: it adds the count of blocks a test must free and the
table of the program's tests, which a program that ships has no use for.

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
build's LIR and the test results cached under it. `truss build` builds a
program without them, since it builds only once every proof the program
reaches, the standard library's included, is done; `truss run` keeps them,
since it does not wait for proofs:
- No `requires` clause is evaluated. The prover shows each one, and a
  clause can cost more than the function it guards. Each check below is
  of one primitive operation and takes constant time. A call that breaks
  a `requires` is caught at the primitive it reaches.
- An index into a storage, a view, or an array panics with "index out of
  bounds" where it is not below the length, and so do a removal, a swap,
  and an insertion past the end. A slice panics with "slice out of
  bounds". That is how an index past a `List`'s end is caught: the
  `List`'s `at` is inlined, and its `storage_at` checks.
- A storage operation checks its own precondition. A push and an
  insertion need room, a pop needs an element, a new length is within the
  capacity, and a new capacity is at least the length.
- A call of the C library checks what the table says of each argument: a
  view has the elements that the function reads, a storage has the room
  that the function writes into or the elements that it changes, and
  elements that the function reads up to a zero end with one.
- Integer `+`, `-`, and `*` panic with "arithmetic overflow", through
  `__builtin_*_overflow`, and so does negating the least value of a signed
  type. The `wrapping_` operations still wrap.
- Integer division panics on a zero divisor, and on the least value over
  -1.
- A shift panics with "shift amount out of range" where the amount is
  negative or is not below the type's width.
- A float converted to an integer panics with "conversion out of range"
  where it is not in the integer type's range, which C leaves undefined.
  A conversion between integer types keeps the low bits and is not
  checked: the standard library uses it that way, as where it hashes a
  negative number.

A check reports the position of the operation in the code that wrote it.
For the standard library's code that is inlined into a program's, it
reports the program's call, since the program's author can change the
call and not the library: an index past the end of a `List` fails in the
`List`'s `at` and is reported at the program's index. A check that fails
in a function of the library that is called, such as a slice past the
end, reports the library's position.

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
`t_standard__list__List_each_Of_standard__Int64_End_`. A package with an
owner in its name gives two parts, as in `t_acme__geometry__vector__length`. Names stay readable
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
| `call(target, arguments, destination)` | A call. The target is an instance or nested function with its C signature, a function value, a capability's entry through its evidence, an entry of an `any` value's table, an intrinsic, or a function of the C library with the declaration its system gives it. The destination is where the result goes: nowhere, returned into a place, or written by the callee into a place through a pointer, which the emitter passes before the arguments. A function value's environment, an evidence pointer, and an `any` value's pointer are part of the target, which the emitter passes first, before any result pointer |
| `drop(place)` | Run the type's drop code. Before drop elaboration: drop whatever the place still owns |
| `free_block(place, variant)` | Free the block of an `indirect` variant whose fields have all been moved out or dropped |
| `echo(text, length, site)` | Record a value's debug output, with its position |
| `region(fork, kind)`, `regions_end(fork)` | Before outlining only. The start of a region of a `parallel` or `concurrent` statement, and the end of the fork's last region (see [Parallelism](#parallelism) and [Concurrency](#concurrency)) |
| `fork(branches)` | Run each nested function, given the address of its environment, and go on when all have returned. They may run at the same time. |
| `fork_range(body, environment, first, last)` | Run the nested function for parts that together hold each index from `first` to `last` once, and go on when all have returned |

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

The methods with an entry are the ones the type checker lets a call
through `any` reach: a method with no generic parameters of its own, whose
parameters and result do not name `Self` other than as the type an
associated type is of. An entry's C signature is the trait's method read
with `Self` as the `any` type, which fixes each associated type, so the
code that fills a table for an `impl` and the code that calls through the
`any` type agree on it.

`any value` allocates the block and moves the value in, which is the one
allocation DESIGN.md says it costs.

### Shared values

`intrinsic::Shared[Value]` is one pointer, to a value in a heap block. The
block starts with a header that the runtime owns: the block's address, an
atomic reference count, and a mutex. The value follows the header, and the
pointer is the value's address, so the header ends where the value starts.

| Operation | Lowering |
|---|---|
| `shared_new(value)` | Allocates the block with a count of one and moves the value in |
| `copy()` | Increments the count and copies the pointer |
| drop | Decrements the count. The reference that brings it to zero calls the value's drop function and frees the block |
| `shared_update(shared, input, change)` | Locks the mutex, calls `change` with the value's address as its `mut` argument and with `input`, and unlocks |
| `shared_key(shared)` | The pointer as a `UInt64` |

- **The count is atomic** because a reference can be copied and dropped
  on any thread, in a `parallel` branch for one.
- **`change` cannot block or deadlock.** Its type has no `uses`, so it
  cannot wait, and it cannot call `shared_update`, which requires `Tasks`.
- **Drop elaboration does not track the block's contents.** The code that
  writes the value into the block or lends it to `change` reaches it
  through a pointer local marked `borrowed`. The value is dropped by a
  direct call of its type's drop function.
- **The runtime's functions are declared only in the C files that call
  them,** so adding them changed the C of no other instance.

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
parameters but its evidence, and the locals that are live across a
`yield`, with the states of any cursors it pulls from inside it. A
parameter's field is named by its
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
| read-only, including `self` | by value, or `const T *restrict` if it holds an array's elements | `const T *restrict` |
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
- **A read-only value that holds an array's elements is passed by
  address, whatever its size.** A view of an array's elements is a view
  into the array's own bytes, and a function may return a view of what a
  read-only parameter views. Passed by value, the parameter would be a
  copy in the callee's frame, and the view would outlive it. A small array
  and a small record with an array in it are the values this changes; one
  whose elements are in a block of their own, as a `List`'s are, is still
  passed by value.
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
fills in each missing argument from its constant. A call that has an
argument for every parameter sets every bit: a call through a function
value, an entry of a table, a call the compiler writes itself, and a call
that is run while compiling are all such calls. Only a call written in
source can leave an argument out. This keeps DESIGN.md's rule that defaults
are applied by the function, so changing one compiles only the function
again. It avoids Kotlin's separate `$default` method, which costs an extra
call.

Where the default must be owned, for a record field or an `own` parameter,
filling it in copies the constant: free for numbers, strings, and empty
collections, one allocation for a non-empty one. That is how DESIGN.md counts
it.

A capability method is the exception: its caller evaluates the defaults of
the arguments it omits and passes every argument. An entry of a capability's
table takes no mask, and no one implementation is there to fill a default
in, since the default is written in the capability and not in each `impl`.

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
  block is freed. A sum type's value is asked which variant it holds
  first: a `match` that owns its value moves a payload out in one arm, and
  where the arms meet the value may hold another variant, which is dropped
  whole.
- **a drop behind a flag,** where the place owns a value on some paths and
  not others, as after `if ready { consume(own item) }`. A flag is a `Bool`
  local, set where the place is given a value and cleared where it is moved
  or dropped. It starts false, as every local starts zeroed, and is written
  at the function's entry only for a parameter, which holds a value there.
  So the flag of a local is named only where the local is, which matters
  where a part of the function becomes a function of its own (see
  [Outlining](#outlining)).

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
  the value and the storage of bytes to append its text to, which its
  caller owns, so there is no buffer of the program's. It writes a number
  and quoted text by calling the standard library's functions that do. The
  text is
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

A float is written as a hexadecimal literal, which is exact. One that is
infinite or not a number has no literal, and is written with the C
compiler's `__builtin_inf` and `__builtin_nan`, which are constants, since
a constant's static value is initialized with one. Every float that is not
a number is the same one in Truss, so which one is written does not show.

Whether a float fits an integer type is whether it is a number and the
whole number it is cut down to is in the type's range: it is above the
least value less one and below the greatest plus one, with IEEE
comparisons, which a float that is not a number fails. The upper bound is
a power of two, which every float type holds exactly. Where the lower one
is not held exactly, as the least `Int64` less one is not, no float lies
between it and the least value, and the test is against that. A
conversion of a float that fits cuts it down toward zero.

Checked, wrapping, and saturating arithmetic use `__builtin_add_overflow`
and its siblings. Full-width multiplication, used by hashing and
`checked_mul`, uses `unsigned __int128` on 64-bit targets.

### Control flow and patterns

- **`match`** tests its arms in order: each arm tests its patterns against
  the values, part by part, and jumps to the next arm at the first part
  that does not match. The value is evaluated once, and the first arm that
  matches runs.
- **`?`** is a tag test and an early return, with the drops elaboration
  inserted.
- **A `for` over a range** counts in the range's own type, and an
  inclusive range stops after its last value without adding one to it,
  which could overflow. A range of characters goes from U+D7FF to U+E000,
  since the surrogates between them are not characters.
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
- **Alternatives that bind a name are tested as separate patterns.**
  `Circle(radius: n) | Square(side: n)` is two patterns, and `n` is bound
  from the part that the matching one found. The code after the pattern is
  emitted once, so each name is kept in a slot that every alternative
  fills: a local of the name's type where the name owns the part or copies
  it, and a pointer to the part otherwise. Alternatives that bind nothing
  stay one pattern.
- **`while` and `for`** become blocks and gotos. A `for` over anything but a
  range of built-in integers calls `each` (see
  [Lending and yielding methods](#lending-and-yielding-methods)).

### Strings and templates

- **String interpolation builds into one buffer.** `"${count} items in
  ${name}"` writes each piece of literal text and each part's `display`
  into one `TextBuilder`, and returns the `String`. It never builds a
  `Template` or its lists.
- **Numbers display as their debug output does.** Integers are written in
  decimal by the standard library. A float is the shortest decimal that
  reads back as the same value: the standard library asks the C library's
  `snprintf` for one more digit until `strtod` gives the float back. Debug
  output calls the same functions, so `"${x}"` and `echo x` agree.
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
  arrays of parts that fold. The core form desugars a list literal into a
  block that makes a storage, pushes each element, and calls
  `List.from_storage`, so the folder follows a block's `let`s and pushes,
  and a call of a function whose body is one expression. Another constant's
  value, where it folds, is
  written in place, since C cannot initialize static data from another
  object. Whatever the folder does not know, such as a `Map` literal, or
  cannot give exactly, such as a shift whose result does not fit its type,
  is not folded: the constant's evaluator is run (see
  [Code run while compiling](#code-run-while-compiling)), so folding can be
  incomplete and never wrong. A constant made of one that is run is run
  too, and its evaluator copies that one's static data, since nothing is
  moved out of a constant.
- **A list or map literal in a function body** allocates its buffer and
  fills it, which is the one allocation DESIGN.md counts. A literal whose
  parts are all constant, and which is only read, can be static data
  instead.
- **A `Set` or `Map` literal** makes the collection empty and inserts each
  element or entry with the type's own `insert`, so a literal keeps the
  collection's order and, of equal keys, the last, exactly as inserting by
  hand would.

### Code that does not ship

- **`echo`** appends the value's debug output to storage of its own, and
  calls the runtime's echo function with that and its position. It writes to the test's report in a test, and to stderr
  elsewhere. Builds refuse programs that can reach it, so it only exists in
  test and development runs.
- **`todo`** reached in a test calls a function that tells the runner the
  test is incomplete and ends the worker. Builds refuse programs that can
  reach a `todo`.

What a program can reach is what its `main` calls, takes as a value, reads,
or drops, and so on from each of those, with one difference from what a
build compiles. A capability's implementation is compiled whole, since its
table has an entry for every method, but a method of it is reached only
where code that is reached calls that method of the capability. So a
`todo` in a method of an implementation stops a program that can call the
method, and no other: an implementation can be written a method at a time
while programs that use the rest of it build. A call of a capability's
method names the capability for this, and a table says which capability's
methods it holds.

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
standard library or a registry package, `List.each` and the body are in the
same C file. The C compiler inlines both, and the loop becomes a plain loop over the
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

A lending method may have a `yield` on each of several paths, as
`Slice.get` yields `Some(self[index])` or `None`. Each `yield` then stores
the address of what it lends and its own number, and the caller reads
through the address. As the caller's scope ends, the code goes on from the
`yield` that was reached, by its number. A value the method makes to lend,
such as that `None`, is built in one place that the caller's statement
owns, so that it is dropped once whichever `yield` made it.

A method may yield a value built around places it lends:
`yield Some(self[index])`, or `yield Indexed(index: index, value: mut
self[index])`. The core form marks each such field as a place.

- **Lent to be read,** the value holds a copy of each place's bytes and
  owns nothing. No Truss value depends on its own address, and the places
  cannot change while they are lent, so the copy is as good as the place.
  Nothing drops it.
- **Lent to be changed,** each place's value is moved into the built
  value, and the scope around the `yield` moves each back as it ends, on
  every way out of it: the end of the caller's statement or loop body, a
  `break`, a `return`, a `?`. While the caller has the value it owns what
  it holds, so a field the caller replaces is dropped first, as in any
  value, and what goes back is what the caller left.

Where such a method is pulled, which only a loop over a method that is
already inlined around it does, `next` gives a value that owns a copy of
each place.

A lending method with no `yield`, such as one whose body is `todo`, never
returns. Its body is inlined as usual, and the caller's code after the call
is unreachable.

A quantifier in code that runs, such as
`forall i in 0..items.length() => items[i] > 0` or
`exists item in items => item < 0`, is the same loop with another body:
over a range it is the counted loop, and over a collection it is the call
of `each` that a `for` loop makes, which the core form gives it. The
answer starts as true for `forall` and false for `exists`, each value's
body is evaluated, and the first one that decides the answer sets it and
leaves the loop as `break` does, so an `each` that is inlined drops what
it owns. It costs what the loop costs up to that value, and a quantifier
inside a loop or another quantifier needs nothing more.

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
   the LIR. They and the parameters, but the evidence, become the cursor's
   fields, beside the state number; everything else stays in C locals. A
   kept local reads and writes its field through the cursor, so a `yield`
   stores nothing.
3. `next()` switches on the state and jumps to the block after that
   `yield`. Each `yield` sets the state and returns `Some` of the value.
   Reaching the end sets the end state and returns `None`, as `next()` does
   ever after. `next()` takes the method's evidence as parameters after
   the cursor, and each call passes the evidence that its own code has,
   as a call of a function value whose type has `uses` does.
4. In the version lowered for pulling, a `for` loop or a pulled cursor
   inside the method is an explicit cursor and calls to its `next()`, rather
   than a loop body, since a loop body cannot stop partway. The inner cursor
   is live across the outer `yield`s, so it becomes a field of the outer
   cursor.

A cursor holds no evidence. The evidence that a method is given where it
is pulled is in the frame of a `provide`, and a cursor is a value that can
outlive that frame. A cursor that held the evidence would then call an
implementation that had been dropped, which is a use after free. So the
type checker requires the method's capabilities at each `next`, and each
`next` uses the implementation that is provided where it is called. The
drop function is given no evidence and has none to read: code generation
reports a compiler bug if a `stop` path reads any.

A `for` over a value of a type that implements `Cursor` is the same loop
with the type's own `next`: it is called until it gives `None`, and the
loop owns each value it gives.

A cursor's drop function runs the `stop` path of the `yield` it is stopped
at, which drop elaboration has already filled with the drops of what the
method owns there. That is what DESIGN.md means by a dropped cursor ending
the method at its last `yield`. Before the method starts, it drops the
owned parameters, such as the receiver of an `own self` method, and after
the end it drops nothing. A method whose yields go through a recursive call has
no fixed-size state, so the type checker reports any pull of it, as
DESIGN.md says.

A cursor of a yielding method implements the prelude's `Cursor` trait, by
an `impl` that the compiler derives for the yielding function. A call of
that `impl`'s `next`, which generic code reaches through a bound, is a
call of the state machine. The `impl`'s associated capability set `Uses`
is the method's `uses` clause, so the call passes the method's evidence
after the cursor, as a `next` written on the cursor's own type does.
The methods that the trait gives a body, such as `count` and `skip`, are
instances of the trait's code for the cursor's type, as for any `impl`. So
`any Cursor[Element = Int64]` gets an ordinary vtable.

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
- **An associated capability set is decided by the instance.** A function
  that uses `Source.Uses` is compiled once for each type that `Source`
  stands for. Each instance takes evidence for the capabilities that the
  type's `impl` defines as `Uses`: none for a `List`'s cursor, and
  `FileRead` for the cursor of a method that uses `FileRead`. A method that
  a trait gives a body and that uses `Self.Uses` takes the evidence of its
  `impl`'s set in the same way. A set that an `impl` defines from another,
  as `capability Uses = Source.Uses`, is replaced until only capabilities
  are left, so the signature of an instance names no set.
- **A call through `any` passes no evidence for an associated capability
  set.** The type checker converts a value to `any` only where each set of
  its type is empty, since the caller cannot name the capabilities of the
  type that the value hides. So the set of an `any` type is empty, and an
  entry of an `any` table takes the same evidence as the method it calls.
- **Function types with `uses`** take evidence when called, like functions,
  after their parameters. A lambda's code reaches only that evidence. A
  callback stored in an `own` parameter gets its evidence from whoever
  calls it.
- **Inside an `impl` of a capability,** a function value that uses the
  capability means the implementation itself, as the type checker rules,
  so its evidence is the implementation's own, made on the stack like a
  `provide`'s.
- **`Panic` has no evidence.** It cannot be provided, so `Panic.crash` is a
  direct call into the runtime.

A capability call costs one indirect call, which is small next to the I/O
behind most capabilities.

### `main` and the real implementations

The standard library implements each standard capability for real with an
ordinary type, such as a system clock and the real file system: the
capability's `System` type, as `SystemConsole` is `Console`'s. The
generated startup code makes a value of the type for exactly the
capabilities in `main`'s `uses` clause, with evidence on the stack
pointing at each, as a `provide mut` would. A type that holds something is
made by its `new`: `SystemConsole` holds the input it has read and not yet
given out. The values are `main`'s caller's, and are dropped when `main`
returns. An external test gets its declared capabilities the same way, as
values of its own.

### Tasks

`Tasks` is a capability like any other. `concurrent` code calls its methods
through evidence, so a test can provide a scheduler of its own. The real
implementation, `SystemTasks`, calls the runtime's task functions.

| Method | Meaning |
|---|---|
| `open() -> UInt64` | Creates a task group and returns its handle |
| `spawn(task_group, work, item) -> Bool` | Spawns a task that calls `work(item)` and returns true. If the group is cancelled, spawns nothing and returns false |
| `join(task_group)` | Blocks until every task of the group has ended, then frees the group |
| `cancel(task_group) -> Bool` | Cancels the group's tasks. Returns true to the first caller and false to every later caller |
| `cancelled() -> Bool` | Whether the calling task is cancelled |
| `watch(key) -> UInt64`, `wait(key, ticket, reason)`, `wake(key)` | Blocking on a key. `watch` returns a ticket, and `wait` blocks until `wake` has been called for the key after that ticket was issued |
| `lock(mutex)`, `unlock(mutex)` | Mutual exclusion between the calls of a `mut` implementation |
| `yield_now()` | Yields the thread to another task |

The runtime runs each task on a stack of its own, as it runs a coroutine,
and the pool's threads run the tasks that are ready:

- **The ready queue** holds the tasks that can run. A thread of the pool
  takes one, switches to its stack, and runs it until it parks, yields,
  or ends.
- **A task that waits parks.** Waiting for a key, for a mutex, or for the
  tasks of a group switches from the task's stack back to the thread,
  which takes the next ready task. A parked task holds no thread. What it
  waits for makes it ready again, and it then runs on whichever thread
  takes it.
- **A thread that is not a task blocks while it waits.** The thread that
  runs `main` is one. It runs no task meanwhile. A task that ran on top
  of the thread's own computation could block for long, and would hold
  that computation up after its wait had ended.
- **A call that blocks holds its thread.** The C library's rows that can
  block, such as `read` of a file or a pipe and `waitpid`, are named in
  the table, and lowering brackets each call with `blocking_begin` and
  `blocking_end`. Most such calls return at once, so the bracket only
  records the tick at which the call began. The monitor, a thread of the
  runtime that ticks every millisecond while tasks are ready, counts a
  thread as blocked once its call has lasted a whole tick, as Go's
  `sysmon` does. A thread that counted as blocked from the start of each
  call would call a spare thread for every short read.
- **A sleep and a wait for a socket park the task.** A sleep puts a timer
  in a heap that is ordered by deadline. A thread of the runtime sleeps
  until the earliest deadline, then wakes that timer's key. The standard
  library's sockets do not block: a call that would block fails with
  `EAGAIN`. The library takes a ticket for the descriptor and direction
  before the call (`descriptor_watch`) and waits on it after `EAGAIN`
  (`descriptor_wait`), so it does not miss the descriptor becoming ready
  between the two. The runtime registers the descriptor at its first
  wait with the system's poller, `epoll` on Linux and `kqueue` on macOS,
  edge-triggered and for both directions. A thread of the runtime takes
  the poller's reports and wakes the key of the descriptor and
  direction. The time limit that a program sets on a socket
  (`SO_RCVTIMEO`, `SO_SNDTIMEO`) applies only to a blocking call, so the
  wait reads it and starts a timer for it. `close` goes through the
  runtime, which forgets the registration, because the system gives a
  closed descriptor's number to the next one that is opened.
- **Spare threads run tasks in place of blocked threads.** A thread is
  blocked once the monitor has counted its call, while it waits and is
  not a task, and while it sleeps until a `parallel` branch that another
  thread took is done. For each blocked thread, one spare thread may run tasks,
  so a program runs tasks on as many threads as the pool has. A spare
  thread is called or started when a task is ready, no thread of the pool
  is idle, and fewer spare threads run tasks than threads are blocked. It
  sleeps when that no longer holds, and it never exits. On a machine
  with one core the pool has no thread but the first, so a spare thread
  runs the tasks while `main` waits for them.
- **A task changes threads.** A task that parks resumes on whichever
  thread takes it. What the runtime keeps for each thread follows the
  task: the coroutine that the task is in, and for the sanitizers the
  stack that it left. Generated code reads `errno` through the runtime's
  `t_runtime_errno`. glibc declares its own function for the address of
  `errno` as returning the same address on every call, so a C compiler
  could reuse one thread's address after the task has moved to another.
  A release build optimizes across the runtime and the generated code,
  so a function of the runtime that generated code calls reads every
  thread-local variable, and `errno`, through a function that is not
  inlined.
- **A `parallel` block in a task** forks on the queue of the thread that
  runs the task, and a spare thread has such a queue too. A branch may
  use no capability but `Panic`, so a task neither parks nor yields
  inside the block, and it leaves the block on the thread it entered it
  on.
- **A group** counts its tasks that have not ended. `join` waits until the
  count is zero and then frees the group.
- **Cancellation** is a flag on the group. A task is cancelled when its
  group, or a group that encloses it, is. `cancel` sets the flag once,
  and makes ready each task of the group, and of the groups that its
  tasks opened, that is parked in a cancellable wait. A task records
  where it parks before it reads the flag, and `cancel` sets the flag
  before it looks, so one of the two sees the other. No other task is
  woken.
- **A cancelled task that is blocked in a system call is interrupted.**
  `cancel` hands the group to a thread of the runtime. Every few
  milliseconds, until the group is joined, that thread sends `SIGURG` to
  each thread that runs a blocked task of the group, or of a group that
  its tasks opened. The handler does nothing and is installed without
  `SA_RESTART`, so a blocked read or `waitpid` fails with `EINTR`.
  The standard library's retry loops stop retrying in a cancelled task,
  and the error becomes `SystemError.Cancelled`. The interrupt is
  repeated because a task can start a blocking call just after one. The
  runtime reserves `SIGURG`, as Go's runtime does. A host lookup cannot
  be interrupted, so it runs to its end.
- **Waiting on a key** uses a fixed table of slots. A key hashes to a
  slot, which counts the wakes of its keys and holds their waiters.
  `watch` returns the count, `wait` parks the caller if the count is
  unchanged, and `wake` increments it and makes the waiters of that key
  ready. Two keys can share a slot, so a wake of one key can make a
  `wait` on the other return at once, and its caller tests its condition
  again.
- **A mutex** is a `UInt64` that its owner initialized to zero: 0 is
  unlocked, 1 is locked, and 2 is locked while a caller may wait, as in
  Drepper's "Futexes Are Tricky". `lock` changes it from 0 to 1 with a
  compare-and-swap. A caller that finds it locked sets it to 2 and waits
  on its address as a key, and `unlock` wakes one waiter if it finds 2:
  a thread that is not a task if one waits, and otherwise the task that
  has waited longest. A lock and an unlock that no other caller contends
  are one atomic operation each. The wait is not cancellable.
- **A test program, and code run while compiling, start no thread.**
  `spawn` calls the task's function and returns when it returns, so tasks
  run sequentially, in the order they are spawned. A task that calls
  `wait` would deadlock, because the task that would wake it cannot run,
  so `wait` panics there. A sleep and a wait for a socket block the one
  thread, in `nanosleep` and `poll`.

### Mutual exclusion for a `mut` implementation

Several tasks can call one implementation at the same time. If the
implementation is provided `mut`, that would be a data race on its state.
So at a `provide mut` whose body can use `Tasks`, lowering replaces the
evidence of each capability of the implementation:

- The replacement's table is the capability's *locking table*, an
  instance generated once for the capability. Its entry for a method
  calls `Tasks.lock`, calls the same method through the implementation's
  own evidence, and calls `Tasks.unlock`.
- The replacement holds the address of the mutex, the implementation's
  own evidence, and the evidence for `Tasks`. The mutex is a word in the
  frame of the `provide`, shared by all capabilities of the
  implementation.
- The locks go through `Tasks`, not straight to the runtime, so that a
  scheduler provided as `Tasks` sees every lock. They use the `Tasks`
  implementation that the same `provide` lists, or else the enclosing
  one.
- An implementation of `Tasks` is never locked. It guards its own state.
- A `provide` whose body cannot use `Tasks`, and one without `mut`, are
  lowered as before, so their calls cost nothing more.

The intrinsic module also has coroutines, for a scheduler written in Truss
that runs one task at a time. `coroutine_start(work, item)` creates a
suspended coroutine, `coroutine_resume` runs it until it suspends or its
function returns, and `coroutine_suspend` switches back to the resumer.
A coroutine has a stack of its own, and a resume or a suspend is a switch
between two stacks on one thread:

- **The stack** is memory from `mmap`, as large as the main thread's
  stack, with a guard page below it. An overflow faults on the guard page
  and is reported as any stack overflow is. The pages take memory only
  once they are touched, and a few unused stacks are kept for reuse.
- **The switch** is a function in assembly, for x86-64 and for ARM64. It
  pushes the callee-saved registers, stores the stack pointer of the code
  that calls it, loads the stack pointer of the code it switches to, and
  pops that code's registers. No system call is made and no thread is
  created.
- **The sanitizers are told of each switch,** through the fiber functions
  of AddressSanitizer and ThreadSanitizer, so generated code that runs in
  a coroutine is checked like any other.

## Parallelism

A branch of a `parallel` block, and the body of a `parallel for`, becomes a
function of its own, which the runtime's threads run. It happens in two
steps, with drop elaboration between them.

### Regions

Lowering writes a `parallel` statement's code where the statement is, in
order, and marks where each part starts:

- **A block's branches** are each a region. A branch cannot leave the block
  early, so a region has one way in and one way out.
- **A `parallel for` over a range** is one region that holds the loop. The
  loop covers a part of the range's indexes, counted from 0 as `UInt64`,
  so that a range of any integer type has as many indexes as fit. Two
  locals hold the first and last index of the part, and where the region
  is reached they hold the whole range's.
- **A `parallel for` over a method that yields by position** is that
  method's own loop, marked the same way, with the `parallel for`'s body
  at its `yield`. A method yields by position when its body is one `for`
  over a range that does nothing but `yield`: its iterations share
  nothing, so they can run in any order and at the same time.
- **Any other `parallel for`** runs in order. A method that keeps
  something from one `yield` to the next, such as a count in a `while`
  loop, has iterations that depend on each other.
- **A method's pulled version** has no regions, since its code is a state
  machine, and neither has a `parallel` block in a lending or yielding
  method that is inlined, where a `yield` in a branch would run the
  caller's code.

Run in place, the regions mean what the statement means. So drop
elaboration reads them as ordinary code: which branch gives a `let` its
value, which takes a value out of a place, and which drops what, is worked
out as for any other code.

### Outlining

After drops are elaborated, `Outline` makes each region a nested function
and the statement a fork:

- **A local that only the region names** becomes a local of the function.
- **A local that the region shares** with the code around it or with
  another region is reached through the function's environment, which
  holds the address of each. The type checker has shown that the branches
  change no place that another uses, so the addresses are never written
  through at the same time. Unreachable code around the region does not
  count: after a loop whose body always fails, the blocks that step the
  loop cannot run, and the loop's index is still the region's alone.
- **The locals of a loop's part** are the function's parameters.
- **No two regions share a local that one of them gives a whole new
  value.** No program can do that, so it would be a temporary of the
  compiler's used twice, and `Outline` stops at it.
- **The parts of a loop share no local that the loop's body gives a whole
  new value.** The parts run at the same time, each on its own thread, so
  such a local would be a data race. A drop flag is the case that
  matters: the flag of a value that the body owns is the body's own, so
  each part has its own. A flag that the parts shared would let one part
  drop a value that another had moved, which is a double free. `Outline`
  stops at any such local.

The fork is `fork(branches)` for a block and `fork_range(body, environment,
first, last)` for a loop. A fork inside a region is outlined after the
region around it, from the function that region became.

### The runtime's threads

A fork gives a thread several branches. It runs the first itself and
offers the rest on its own queue, where a thread with nothing to do takes
one from the far end. When its first branch returns, the thread takes back
each branch that is still there and runs it, and for one that was taken it
waits, running other threads' branches meanwhile.

- **The queue** is Chase and Lev's work-stealing deque, with the memory
  orderings of Lê, Pop, Cohen, and Zappa Nardelli, and a fixed size: a
  thread whose queue is full runs the branch itself.
- **A branch's record** lives in the frame of the fork that offered it,
  which does not return until every one of its branches is done. Nothing
  is allocated.
- **There is a thread for each core,** counting the thread that forks
  first. They start at the first fork a program reaches, each with a stack
  as large as the first thread's, and with every signal held back, so that
  a signal sent to the process goes to the first thread as it does in a
  program that has one. `TRUSS_WORKERS` gives another number of threads,
  which changes how long a program takes and nothing it does.
- **A thread with nothing to do sleeps** after looking a while, and a fork
  wakes one. A thread waiting for a branch that was taken sleeps too, and
  the thread that finishes the branch wakes it.
- **A loop's range is run by halves,** down to parts whose size depends
  only on the range, never on the number of threads.
- **A test program, and code run while compiling, run a fork's branches in
  order** on the one thread they have. The code is the same as a
  program's; the runtime they are linked with has no threads.
- **The text of a failure or an `echo` is built by one thread at a time,**
  and a thread that is ending the run never gives the buffer up, so one
  failure is reported.

## Concurrency

A branch of a `concurrent` block, and each iteration of a `concurrent for`,
runs as a task. Lowering marks the task's code as a region, as it does for
`parallel`, and outlining turns the region into a nested function. Two
things differ from `parallel`: the function is spawned through `Tasks`, and
a task can exit its statement early.

### Task regions

A task region has the kind `task(function_value, item)`. Outlining assigns
the nested function to the local `function_value`, and the code after the
region passes it to `Tasks.spawn`. `item` is a `UInt64` local that becomes
the nested function's parameter.

- **A block** opens a group, marks one region for each branch in a single
  fork, spawns each branch, and joins the group.
- **A `concurrent for` over a range** runs the loop sequentially in the
  enclosing function. Each iteration converts the index to `UInt64`,
  assigns it to `item`, and spawns the body, which is a fork with one
  region. If `spawn` returns false, the loop stops.
- **A `concurrent for` over a method that yields by position** inlines the
  method, and the method's range loop spawns the tasks. The `yield` and
  the loop body both run in the task, so the task borrows its own element.
  This is the only case where a task uses a place that the method lends.
- **A `concurrent for` over any other yielding method, or over a cursor,**
  runs the method sequentially in the enclosing function and spawns a task
  at each `yield`. The value's bytes go to the task in a heap block whose
  address is `item`, and the task takes them out and frees the block. What
  the task then holds depends on the `yield`:

  | Yielded | The task |
  |---|---|
  | An `own` value, a value the method computed for the `yield`, or a value from a cursor | Owns the value and drops it |
  | A read-only place, or a constructor of read-only places | Holds a bitwise copy that it never drops. The place still owns what the bytes point at |

  The task outlives the `yield`. The ownership check has verified that a
  borrowed place is inside a parameter the method takes read-only, or is
  `Plain`, so the place stays valid and unchanged until the group is
  joined. If `spawn` returns false, the enclosing code takes the value
  back out of the block, drops it if it is owned, and stops the method as
  a `break` does.
- **The join is a scope cleanup.** The group has a scope of its own, and
  every exit from that scope joins the group, so no path skips the join.
  The scope's temporaries, such as the arguments of the yielding method,
  are dropped after the join, because a task may read them until then.
- **A pulled method has no task regions.** Its instance holds no nested
  function, so `concurrent` code in it is reported as not built, as a
  lambda is.

### Early exits

An early exit is a `return`, a `break`, a `continue`, or a `?` that leaves
a task before the task's end. The core form wraps it in `Task_exit`, with the
tasks that it ends, innermost first. Lowering handles one task at a time:

1. The task evaluates the return value, if there is one, into a temporary
   of its own.
2. The task calls `Tasks.cancel` on its group. If the call returns true, the task
   assigns the exit's number to the local `winner` and moves the return
   value into the local `return_value`. If it returns false, another exit
   won, and the temporary is dropped.
3. The task ends: it drops what its scopes own and jumps to the end of its
   region.
4. After `Tasks.join`, the enclosing code switches on `winner`. If no
   enclosing task remains, it performs the winning exit. Otherwise it
   repeats these steps in the next enclosing task, with `return_value` as
   the value.

- **Each branch of a block has its own `winner` and `return_value`.** The
  branches are regions of one fork, and outlining rejects a local that one
  region assigns and another uses. The iterations of a loop are one
  region, so they share one pair.
- **`return_value` belongs to the scope that encloses the statement.** Drop
  elaboration gives it a drop flag, as for any local that is assigned on
  some paths only.
- **A `break` of the `concurrent for` itself** needs no code after the
  join. A `continue` of the `concurrent for` itself is not an early exit
  of the group: it jumps to the end of the task.

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
| Storage | empty, with a capacity, from an array, length, capacity, set the capacity, lengthen, shorten, push, pop, insert, remove, swap, lend an element, view, view to change the elements through, take a view back |
| Views | length, lend an element, lend an element to change, swap, slice, take a view back |
| Arrays | from a storage, a view of the elements, lend an element to change, take a view back |
| Operating system | the C library's functions and numbers, which system the program is built for, an entry of the environment, a handle from a descriptor and its descriptor, the address of a view, crash |
| A test program | run a test by its number, have failures reported to a descriptor, how many blocks are allocated and not freed |

`Intrinsics` writes every operation into the caller's LIR, never as a call:
numbers as primitive operations, and storage and views as a few statements
over their fields, so the C compiler sees each whole. The operations that
lend an element, such as `storage_at`, lend the place `buffer[index]`
itself.

`array_view` gives a view of an array's elements, whose address is the
array's own, so indexing and slicing an array read it in place.
`array_at_mut` lends the element at an index to change, which is the
place `array[index]` itself.

`view_at_mut` lends an element of a view to change, and `view_swap`
exchanges two, which is how a `Slice`'s methods change elements in place.
A view is an address and a length, and does not record whether its
elements may be written. So a view to change comes from
`storage_view_mut`, which gives static storage a buffer of its own first,
as every operation that writes a buffer does, or from `array_view` of an
array that is held `mut`. The ownership check keeps a view of a read-only
place from being passed where its elements are changed.

A view is a value to the prover, though in memory it is its owner's
elements. So after elements are changed through a view, the standard
library says that the owner's elements from some index are the view's:
`storage_take_view(mut storage, view, start)`, and `view_take_view` and
`array_take_view` for a view of a view and of an array. The prover gives
the owner's model the view's elements. In memory there is nothing to do,
so the operation is no code, except that a build with checks stops if the
view is not of exactly those elements of the owner.

`storage_from_array` moves an `own` array into new storage whose length
and capacity are the array's length. An array's bytes are its elements in
order, so the whole array is written into the new buffer at once and is
moved-from afterwards. That is the only way to take an array's elements
out one at a time: the elements are then popped from the storage, which
stays valid after each pop, so a loop that ends early drops only the
elements it has not taken.

`array_from_storage` is the other way: it moves the elements of an `own`
storage into a new array whose length is the storage's, and frees the
storage's buffer. That is how an array whose length is a type parameter is
made, since an array literal writes each element out: the elements are
pushed onto a storage, which may stop partway and still be dropped, and
become the array together. A build with checks stops if the storage's
length is not the array's, which the prover is to show never happens.

Storage never grows by itself. `storage_set_capacity` gives it a buffer of
its own with room for exactly as many elements as it is told, and
`storage_push` and `storage_insert` write into room it has. How much room
to make is the standard library's to say, in Truss: where a push finds no
room, it at least doubles the capacity, so pushing is amortized O(1), and
the prover reads that as it reads any code.

`storage_shorten` forgets every element after the first `length`, in one
step, and keeps the capacity. Its element type is `Plain`, which the type
checker holds a call to, since forgetting an element that owns something
would leak it; a `List` of any elements is cut short by popping. That is
what makes `String.truncate` constant time.

Storage with capacity 0 and a nonzero length is static, as a string
literal's is: it owns no buffer, so dropping it frees nothing and copying
it shares it. Every operation that writes the buffer in place gives such
storage a buffer of its own first, with room for the elements it has, which
copies the static elements and never frees them. A `String` constant is static in the same
way. A `List`, `Map`, or `Set` constant has its elements in static memory
too, but records its capacity as its length, so `copy()` of one really
copies; a constant is a read-only place, so nothing writes or drops it. The
standard library never moves a `String`'s storage into another type without
copying it.

The libc functions used are declared by the compiler for each target, so the
generated C still includes no headers. Allocation failure ends the process
with a message, as DESIGN.md allows for running out of memory.

### The C library

The intrinsic module also holds functions of the system's C library for
the standard library to call, one operation each, named `libc_` and the
function's name: `libc_write(descriptor, bytes: view, count: length)` is
`write`. They come from one table in the compiler. A row gives the
function's symbol and C types on each system, and how each argument
reaches it:

| An argument | Is passed as |
|---|---|
| A number | Its value, converted to the parameter's C type |
| A `View` | The address of its elements, which the function only reads |
| A `mut Storage` | The address after its last element, for a function that fills room the storage has beyond its length; or, where the row says so, the address of its first element, for a function that reads the elements the storage has and changes some |
| Several `mut` numbers of one type | The address of a structure of them, which holds the arguments' values and which the function writes; each number then goes to its argument. A function that reads a number there before it writes it, as `accept` reads how much room an address has, finds the argument's value |

Truss has no pointer type, so memory crosses to C only as a view, as
storage, or as numbers to write. A small structure a function fills is the
numbers it is made of: `libc_clock_gettime(clock, seconds: mut seconds,
nanoseconds: mut nanoseconds)` gives a `timespec`'s two, with nothing on
the heap. `storage_lengthen` then makes what a function wrote into
storage's room the storage's own. A row can also fix an argument, which
the Truss call then does not have: `libc_getentropy(mut value)` always
asks for the eight bytes of the `UInt64` it fills. A function that reads
its arguments by a
request, as `fcntl` and `ioctl` do, has a row for each request the
standard library makes, and the row fixes the request:
`libc_fcntl_dupfd_cloexec(descriptor, least: 3)`. Another request would
read the next argument as an address, so the request is not Truss's to
choose. A list of addresses, such as the arguments
of a program to run or the variables it is given, is a `View[USize]` that
Truss fills with
`view_address`, which gives the address of a view's elements as a number;
nothing turns a number back into an address.

A row also says how much the function reads or writes through each
address: as many elements as a count that the call passes, a fixed number,
a number of the system such as `PATH_MAX` or the size of a `struct stat`,
or up to the first zero element, as C reads a path. And it says which
count bounds the result, as `read` returns no more than the count it was
given. Code generation does not use these. They are what the prover holds
a call to: a view has the elements that are read, and storage has the room
that is filled. So the proof that a call stays inside the memory it is
given is one rule over the table, and a new row needs no rule of its own.

A function's result is a number; the number at the address it returns,
which is how `errno` is reached; text, the bytes at the address it
returns up to a zero byte, as a view, with a `mut Bool` that says whether
it returned an address at all, which is how `getenv` says a variable is
unset; or nothing ever, for `_exit`, which Truss calls
`libc_exit_at_once`, since a name does not start with an underscore.

A structure whose numbers are not of one type is storage of a number that
several of them make. `poll` takes `pollfd`s, each a descriptor and two
numbers of half its size, as a `Storage[Int32]` with two elements for
each: the descriptor, and what to wait for in the low half of the next
with what was found in the high half. The table's check holds the
structure to that, byte order included.

A larger structure whose layout differs between systems is filled as
bytes. `fstat`, `stat`, and `lstat` write a `struct stat` into the room of
a `Storage[UInt8]`, and the table has numbers for the structure's size and
for the offset of each field the standard library reads:
`libc_stat_size()`, `libc_stat_mode_offset()`, and so on. The standard
library reads each number out of the bytes at its offset. The check
compares each of those numbers with `sizeof` or `offsetof` on the real
structure. A field that a system's structure does not have, as Linux's has
no time of creation, has offset 0.

A call is written into the caller's LIR as a call of the C function
itself, given each argument converted to its parameter's C type, and the C
declares the function with the prototype the system's headers give it. A
function with arguments C passes through `...`, such as `open`, is
declared so, since some systems pass those differently from named ones.

The numbers the headers define, such as `O_CREAT` and `EINTR`, are in the
same table with their value on each system, and are operations that take
nothing: `libc_o_creat()`. Lowering writes the value. So the type checker
and the prover see the same signatures on every system, and only code
generation's results depend on the system, which is part of the target.
A system is an operating system and an architecture: Linux or macOS, on
x86-64 or ARM64. The architecture matters where a structure's layout or a
function's symbol depends on it, as `struct stat` does on Linux and the
symbol of `stat` does on macOS. Stage0 builds for the system it runs on.

A function that only some systems have says so in its row, as
`proc_pidpath` is macOS's. The standard library asks which system the
program is built for with `system_is_linux()`, `system_is_macos()`,
`system_is_x86_64()`, and `system_is_arm64()`, which lowering writes as
constants, and calls such a function only where it exists. A call of it
on a system that lacks it is lowered to a failure, so the program never
names a symbol its C library does not have.

A test compiles the table against the system's own headers: every number
must have the value the table gives, every prototype must be the one the
headers declare, and every structure must be laid out as the storage
passed for it. A row that is wrong for the system the tests run on is
therefore a failing test, not a program that misbehaves.

### Handles

The intrinsic module also provides one handle type: `Handle`, a file
descriptor in an `Int32`, which is neither `Copyable` nor `Plain`.
`handle_from` makes one of a descriptor that is open, and
`handle_descriptor` reads it. Its drop function calls the operating system
to release it, with `close`. `handle_release` gives up a handle without
closing it and returns its descriptor, so that `Handles.close` can call
`close` itself and report an error from it.

The standard library's real implementations are Truss on the C library's
functions: opening a file, with its path given a zero byte at its end and
refused if it holds one; reading into storage; writing every byte; going
on after a signal interrupts a call; and turning an error number into a
`SystemError`. `SystemFileRead`, `SystemFileWrite`, `FileReader`, and
`FileWriter` are written on those, `SystemConsole` writes with them,
`SystemClock` reads `clock_gettime`, and `SystemRandom` reads
`getentropy`. `SystemConsole` and `FileReader` each hold a reader of
lines, which reads a block at a time and keeps what it has not given out.
The console's input and its two outputs as streams are each a new
descriptor for the same open file, made with `fcntl`, so that a stream
owns the descriptor it closes and the process keeps its first three. The
console's terminal is `/dev/tty`, the terminal the process is controlled
from, whatever its input and output were redirected to. Its size is
`ioctl`'s `TIOCGWINSZ`, and a handle that is no terminal has none, which
is how a program learns that it has no terminal. Raw mode reads the
terminal's settings with `tcgetattr` as the bytes of a `struct termios`,
changes the flags at the offsets the table's numbers give, and writes them
with `tcsetattr`: on, the terminal gives each byte as it is typed, with no
echo, no signals from keys, and no changes to what is written; off, those
are set again. `SystemLog`
writes each record to standard error as one line and with one `write`,
`level=warning message="..."` and then each field as `name=value`, with
text in quotes.
`SystemHandles` reads onto the end of a list and writes a slice with
`read` and `write`, does the same at an offset with `pread` and `pwrite`,
and moves, shortens, flushes, and closes a file with `lseek`, `ftruncate`,
`fsync`, and `close`. A file's metadata comes from `fstat` for an open file
and from `stat` or `lstat` for a path: its kind, length, permissions, and
times are read out of the structure's bytes. `SystemFileWrite.open` opens a file in each write
mode: to replace it, to append to it, to create it only if it is missing,
or to update it in place. `SystemFileWrite` makes a directory with
`mkdir`, removes a file or an empty directory with `remove`, renames with
`rename`, links with `symlink` and `link`, and sets permissions and the
time of last change with `chmod` and `utimensat`. `SystemFileRead` reads
where a symbolic link points with `readlink` and resolves a path with
`realpath`, each into room for the longest path the system allows.
`SystemClock.sleep` calls the runtime's `sleep`, which parks the calling
task until a timer fires; the monotonic clock is `clock_gettime` with
`CLOCK_MONOTONIC`. `SystemFileRead.list` opens the directory and reads
its entries a block at a time through the descriptor, with the call each
system has for that: `getdents64` on Linux and `getattrlistbulk` on
macOS. Each fills bytes with entries of the system's own layout, which
the standard library reads at the offsets the table's numbers give, and
it holds every length an entry states to the bytes that were filled. The
C library's `opendir` and `readdir` are not used, since they keep the
directory in a structure of the C library's that Truss would have to hold
an address of. Where Linux does not say what kind an entry is, the kind
comes from `lstat`.
`SystemEnvironment` reads one variable with `getenv` and all of them with
`environment_entry`, an intrinsic that gives the entry at an index of the
environment the process was started with and counts from the first entry
each time, so that it never reads past the last. The current directory is
`getcwd`'s, and the platform is the system the program was built for with
`sysconf`'s count of processors, `gethostname`, and `getpid`. The
program's own path is the link `/proc/self/exe` on Linux and
`proc_pidpath` on macOS. The other locations come from `HOME`, `TMPDIR`,
and on Linux the `XDG` variables. The local time zone is `TZ`, or where
`/etc/localtime` links to, and a zone's rules are its file under
`/usr/share/zoneinfo`, for a name that stays inside that directory.
`SystemProcesses` starts a program found on the `PATH` with
`posix_spawnp`. It lays the program's name and its arguments end to end,
each with its zero byte, refusing one that holds a zero byte, and does the
same for the variables: those this process was started with, unless the
command leaves them out, and then the command's own, a later one of a
name replacing an earlier. What the program does to its first three
descriptors before it runs is a `posix_spawn_file_actions_t`, which is
storage of as many bytes as the structure takes: a stream that is
discarded is opened on `/dev/null`, a stream that is piped or captured is
one end of a `pipe` whose other end this process keeps, and the directory
the program starts in is `posix_spawn_file_actions_addchdir_np`'s. Both
ends of each pipe are closed in programs that are run, so a child never
holds the end that its parent writes to it with. `run` reads what it
captures from both pipes as `poll` finds it, so that neither fills while
the other is read, and then waits with `waitpid`. A spawned child is a
handle whose number is the process's and whose descriptor is none;
`Handles.wait` reads the exit status, or the signal that ended the
program, out of `waitpid`'s status, and `Handles.signal` is `kill`, which
is refused for a handle that is not one process. `SystemSignals.wait`
calls the runtime, which installs a handler for each signal it is asked
for, so that a task on any thread can wait for it. The handler records
the signal and writes a byte to a pipe, and a thread of the runtime reads
the pipe and wakes the waiters. A signal stays recorded until a wait
takes it, so one that arrives between two waits is there for the second.
A signal that the program was started with blocked, and that arrived
before the first wait for it, has run no handler and is pending. The
thread that waits takes it if it can. On Linux any thread can. On macOS
only the thread that the signal is pending for can, which is the
program's first thread, so a task on another thread does not get such a
signal there.
The wait returns `None` in a cancelled task. A test program, which has
one thread, blocks the signals and takes the next with `sigwait`. The
real `NetworkServer`
and `NetworkClient` are sockets. An address is a `sockaddr_in` or a
`sockaddr_in6` as bytes, which the standard library writes and reads: the
family is where the system keeps it, and the port and the address are high
byte first. Listening is `socket`, `bind`, and `listen`, and the address
the listener reports is the one `getsockname` gives, so a port asked for
as 0 comes back as the port the system chose. Every socket is in the mode
where a call does not wait, so that a task parks for it. `connect`
returns at once, and the standard library waits until the socket can be
written, with the connect's time limit set as the socket's limit for
sending, and reads how the connection went with `getsockopt`. The limit
is set before `connect` is called. A refusal can arrive before the next
system call, and on macOS `setsockopt` fails on a socket whose connection
was refused, so a limit set afterwards would report that failure in place
of the refusal. A read or a
write that waits past a time limit set with `setsockopt` is `TimedOut`:
the runtime's wait applies the limit. A datagram socket
that is not bound to an address is an IPv6 socket that also carries IPv4,
where the system has IPv6: an IPv4 address is sent to as the IPv6 address
that stands for it, and a sender's is given back as IPv4. Every socket is
closed in programs that are run. `NetworkClient.resolve` asks the system
for a host's addresses, so that it answers as every other program on the
machine is answered. The C library gives them as a chain of structures
that hold addresses of one another, which the table cannot describe, so
this one call goes through a function of the runtime's, written in C: it
calls `getaddrinfo`, follows the chain, and writes each address into room
the standard library gives it, which Truss then reads. Its row is in the
table with the C library's, so the prover holds the call to its room in
the same way, and the standard library calls it `runtime_` and its name.
A handle's is the only drop that does more
than free memory, and it runs no Truss code, as DESIGN.md requires.
Standard-library types such as `File` hold one in a field, so their drop
functions release the resource by dropping that field.

## Program startup and failure

The C `main` of a program is generated:

1. Install a handler for stack overflow on an alternate signal stack. Truss
   code has no unsafe operations, so a segmentation fault means the stack
   ran out.
2. Turn `argc` and `argv` into `List[String]`, the program's path first, as
   in C. Each `String` is made of an argument's bytes by the standard
   library, which replaces bad UTF-8 with U+FFFD.
3. Make the standard library's real implementation of each capability in
   `main`'s `uses` clause, and evidence for each on the stack.
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
instance: it works the value out, appends its binary form with
the generated `Encode` functions to storage of its own, and writes that to
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
clauses that can run, and writes each out as a `Bool`. A clause can run
unless it uses the mathematical `Integer`, a quantifier, a conversion to
or from one, or a comparison of integers of two types. In one that runs,
`a ==> b` holds where `a` does not, and `b` is evaluated only where `a`
holds, since `b` may be defined only there. This is the one place where
a clause is evaluated, and it is while compiling. The prover asks it
only of a clause that reads the template's literals alone, which its parts
cannot change (see PROVER.md, "Running code while proving"). It runs with
the test time limit, and its results are kept under the key of the code
that ran, as test results are, so a check runs again only when its texts
or its code change.

A call the prover knows the arguments of has a `Call_evaluation` instance,
of the function and its arguments, each an integer or a `Bool` as 0 or 1: it
calls the function with them as constants and writes its result out, which
is read back as a constant's value is. Its results are kept the same way.

## Tests

### The test program

A test run builds one program containing every test that must run, their
instances, the standard library's test runner, and a generated `main` that
gives the runtime a table of the tests and calls the runner with how many
there are. The runner is Truss, written on the C library's `fork`, `pipe`,
`poll`, `kill`, and `waitpid`. It starts one worker process per core by
forking itself after startup, so workers share its loaded code. It sends
each worker the number of a test to run, over a pipe, and gets back, on
another pipe, records of the test's end and of its `echo` output: a
record is its kind, the length of its text, and the text. A worker runs a
test by its number through the runtime's table. A test that returns has
passed, and its worker writes the record that says so.

The runtime writes the other records. A worker tells it which descriptor
is its pipe, and from then on failing writes a record there where another
program writes to standard error.

A worker whose test fails an `assert`, panics, overflows its stack, runs out
of memory, or reaches a `todo` reports why and ends; one that dies without
a report is recorded from its exit status. The runner then starts a new
worker and carries on, so a new process starts only after a failure. Ending
the worker is also what lets an `assert` inside a lambda end its test, which
an early return could not. The runner kills a worker whose test exceeds the
project's time limit.

A test must free every block it allocates. A test program's runtime counts
the blocks that are allocated and not yet freed, a worker reads the count
before and after each test, and a test that ends with more than it started
with is reported as a panic with a compiler-bug message saying how many it
left.
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
  reach, with the version of code generation and the target: its widths
  and its system. `USize` is a
  `typedef` in the generated C, so code that differs between 32-bit and
  64-bit targets only in a `USize` has the same LIR for both, while results
  such as `USize.maximum` are not the same. An instance is lowered for one
  target all the same, since whether a value is passed by address depends
  on its size.

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
  takes, and writes a large result to a place that shares no memory with a
  place it also passes by address. Two places under one local share memory
  unless their paths part at different fields, or one path continues
  through a pointer. The pulled version of a yielding method keeps its
  locals in one cursor, so the check compares paths and not only locals.
- a value that has a size is built as a record or a variant its type has,
  with fields the type has, since the emitter leaves out a field it does
  not find in the layout, as it must for a field of no size
- a call of a nested function names it with the signature it has

Everything a build links is checked together before any C is emitted:
- each call names its callee with the signature the callee has, as does
  each entry of a table and each named function used as a value
- a drop reaches a drop function
- each address of a table or of a constant reaches one
- what an instance compiles to is the instance that was asked for

## Building

### Lowering

Code generation's lowering is a query, so a test run after an edit lowers
only the instances the edit reached:

- **An instance's LIR** is a query keyed by the instance and by how it is
  lowered: the target's widths and its system, and whether the program
  checks what the prover would prove. A pulled method's version, whose locals make its
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
| An instance's LIR | A query on the instance, which reads the core forms it lowers, the signatures it calls, the layouts it uses, and the bodies it inlines |
| An object file | The C's text, the C compiler's identity (its `--version` output and path), and the flags, which name the target |

Early cutoff happens at the LIR: if an instance's LIR comes out the same, so
does its C, so its object is found, nothing is compiled, and no test that
reaches it runs again. The C compiler's identity is only in the object key,
so upgrading clang recompiles objects but invalidates no test result.

### C files and optimization

- **Object files are cached by their key,** each written under a temporary
  name and renamed into place, so a build that stops partway leaves no
  broken object. Files that need compiling are compiled in parallel, across
  the machine's cores. An object that a build finds is given the present
  time, so a cache that drops objects by age drops those no build has used
  for that long, and never one that is still in use.
- **Every build compiles one C file per instance.** The C compiler runs
  once for each instance whose C changed, in parallel across cores, and
  each instance is an external function of its own file.
- **A development build puts small callees in the caller's file.** A
  function an instance calls, from the standard library or a registry
  package, with little code and no lambdas, is emitted into the instance's
  file too, as a `static inline` copy, so the C compiler can inline it, as
  DESIGN.md allows for development builds. Those change only with the
  toolchain or a version in the lock file. The small functions of the
  project's own packages stay calls, whichever of its packages calls them,
  so that an edit to one compiles only it again. An object
  file is found by its C's text, which the copies are part of, so a change
  to a callee compiles its callers' files again. Lowering writes lending
  and yielding methods and primitive operations into their callers
  itself, whatever the build.
- **Development builds compile at `-O1`,** which is fast to compile and
  avoids the stack traffic of `-O0`.
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

- **A check that reports its caller's position.** A check that fails in a
  function that is called, not inlined, reports the function's own
  position. Rust's `#[track_caller]` reports the caller's by passing its
  location.
- **A constant's value kept between runs.** It is worked out again in each
  run of the compiler.
- **Checkers shipped compiled.** The standard library's are to ship already
  compiled with the toolchain, for each host and both widths of `USize`, and
  a dependency's to be compiled once per version.
- **A float's text without the C library.** DESIGN.md has it written in
  Truss so that it is the same on every system. The loop is Truss; the
  digits are `snprintf`'s and the check `strtod`'s.
- **`match` as a decision tree.** A tree would test each part of the value
  once, in the order the patterns need, and switch on tags and integers,
  where arms tested in order may test one part again for each arm.
  Maranget's "Compiling Pattern Matching to Good Decision Trees" (2008) is
  the method.
- **Room reserved for an interpolation.** The literal lengths are known, so
  the `TextBuilder` can start with that much room and grow only if a part
  writes more than its estimate.
- **Small callees of small callees, and generated functions, in the
  caller's C file.** Only the functions an instance calls itself are
  copied in, and a type's drop and copy functions are not.
- **The standard library and registry packages at `-O2` in development
  builds,** cached, so a project's development builds run them at full
  speed.
- **A lending method that lends through a call to itself.**
- **Waiting, in a test program, for a signal that the system ignores
  unless it is asked for,** such as a terminal's change of size. macOS
  throws such a signal away while it is blocked, and a test program
  blocks the signals it waits for. A program installs a handler instead,
  and sees the signal.
- **A cursor over a method that lends places to be changed.** `next` would
  have to hand out a value it takes back.
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
- **A `parallel for` over the read-only `each` of a `List`, a `Slice`, or
  an `Array` in chunks.** These methods are `while` loops that keep an
  index between `yield`s, so the loop runs sequentially. They cannot be
  written as one `for` over a range yet: inside a `for`, `yielded` names
  the loop's own cursor, so the method's `ensures` about `yielded` cannot
  be proven.
- **A `parallel for` over any other method at once.** A collection that
  cannot give its parts by position needs a way to split itself in two,
  as Rust's rayon and Java's `Spliterator` have.
- **A wait for a pipe, a terminal, or a file that parks the task.** Only
  the standard library's sockets do not block. A read of a pipe or of
  standard input, and a wait for a child process, hold a thread. A read
  of a file cannot be waited for with `epoll` or `kqueue` at all.
- **More tasks at once than the operating system allows mappings.** Each
  task's stack is a mapping with a guard page. Linux allows a process
  about sixty-five thousand mappings by default, which is about thirty
  thousand tasks.
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
