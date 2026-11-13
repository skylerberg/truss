# Truss Code Generator

Stage0's code generation covers everything between the MIR of
[MIR.md](MIR.md) and a program that runs. It takes the MIR of each
definition the program can reach and produces C, which a C compiler and a
linker turn into a program. A default, a constant's value, and a template's
`requires` check are core expressions, each lowered through the MIR of that
one expression. Every proof obligation has been
discharged by then, and nothing used only by proofs is compiled.

It checks nothing about the program: a failure here is a compiler bug, or a
valid program stage0 cannot build yet (see [Failures](#failures)).

## Structure

```text
checked definitions
      │
      ▼
 Instances ──▶ Layout ──▶ Lower ──▶ Drops ──▶ Yields ──▶ Emit C ──▶ cc ──▶ link
                            │                                              ▲
                            └──────────── LIR, cached per instance ────────┘
```

Code generation reads MIR and core forms through queries of the code database. It
does not depend on the prover, and neither the prover nor the database
depends on it; only drivers do.

### Why C

Truss has no foreign code, so the standard library's hashing, cryptography,
and text handling run on Truss's own generated code, and the backend must
optimize well. QBE, the obvious small backend, has no inliner, no 128-bit
multiply, no bit-counting or byte-swap instructions, no SIMD, no atomics, and
no way to say that pointers do not alias. C compilers have all of these, and
Truss's guarantee of no aliasing is exactly C's `restrict`. Linking libc
already needs the platform's C toolchain.

### Why one IR before C

A small IR, the LIR, between the MIR and C text gives one place for
every transformation, since the cursor state machine and outlining
`parallel` branches are passes over a control-flow graph. The LIR
is not SSA: locals are mutable slots, since the C compiler builds SSA
itself, and slots make drops and state machines simpler.

Each instance is kept as its C, a fragment that also lists the types,
prototypes, and instances it names. The fragment is what early cutoff
compares: an instance whose C is unchanged needs nothing after it run
again. Its hash reads the C with each name written as a number, so renaming
or moving a definition changes no hash, and the C does not depend on the
installed C compiler, so a new one invalidates no test result. A build
assembles the fragments into files, each declaring and defining what its
fragments name.

### Generated code has no undefined behavior

Generated code has no undefined behavior even if the prover were wrong:

| Rule | How |
|---|---|
| Integer arithmetic wraps if it ever overflows | `-fwrapv`, which turns a prover bug into a wrong value at almost no cost |
| Shift amounts are masked | `x << (n & 63)`, free where the instruction masks anyway |
| No type-based alias analysis | `-fno-strict-aliasing`; Truss's guarantee is given as `restrict` instead |
| Loops are not assumed to end | `-fno-finite-loops`, since a loop without a `time` clause may run until the time limit |
| Floats are exact IEEE 754 | `-ffp-contract=off`, no fast-math, and SSE2 on x86-64 |

Division by zero and `Int64.minimum / -1` are proven impossible, and making
them defined would cost a test per division, so they are the one place a
prover bug could still reach undefined behavior.

**Test builds check instead of waiting for proofs.** A test build, a
development build, and code run while compiling check every primitive
operation that could fail, in constant time each, whether or not the prover
has finished. The checks do not depend on which proofs passed, so neither do
the test build's results. A release build builds only once every proof is
done, so it omits them.

## Instances

A build compiles only the instances its roots reach: a program's `main`,
each test without a cached result, and each constant or template check that
must run while compiling. An instance is a definition with ground type
arguments and the capability sets bound to its capability parameters.
Symbol names are made from the instance's key so that they stay readable in
profilers.

## Data layout

The compiler chooses every layout, and no program can observe one: Truss has
no pointers, no `size_of`, and no foreign code. So layout optimizations can
be added with no change to the language.

- **Record fields are placed by alignment, then by name,** so reordering
  fields never changes the layout.
- **A sum type is a tag followed by the largest variant's fields,** and
  niches remove the tag where a field has spare values, so
  `Option[List[Int64]]` is the size of a `List`.
- **The one type that owns a buffer is built in:** `Storage[Element]`, a
  pointer, a length, and a capacity, whose drop and copy the compiler
  generates. `List` and `String` are records of it, and `Slice` and
  `StringSlice` are a pointer and a length.
- **A function value is two pointers,** the code and an environment on the
  caller's stack, so making one never allocates. An `own` function-typed
  parameter accepts only functions that capture nothing, so storing one never
  stores a pointer into a stack.
- **`any Trait` is two pointers:** its heap block and a vtable.

## Calling convention

The C compiler implements the platform's convention; code generation decides
how each Truss parameter becomes C parameters:

| Parameter | 16 bytes or less | Larger |
|---|---|---|
| read-only, including `self` | by value, or `const T *restrict` if it holds an array's elements | `const T *restrict` |
| `mut` | `T *restrict` | `T *restrict` |
| `own` | by value | `T *restrict` to the caller's memory, which the callee now owns and drops |
| result | returned | written through a `T *restrict` first parameter |

- **Every pointer is `restrict`.** A place passed `mut` is used by nothing
  else during the call, and a viewed original does not change while the view
  is in use, which is exactly `restrict`'s guarantee.
- **Read-only parameters are never copied to be safe,** since the original
  is frozen.
- **A function with defaults takes a mask** of the parameters the caller
  passed, and fills in the rest itself. So changing a default compiles only
  the function, as Kotlin's `$default` does.

## Moves, drops, and copies

A move is a copy of the value's bytes, after which the source place holds
nothing to drop.

- **Every value has an owner from its first moment.** A local of the MIR
  that owns its value is dropped where the MIR ends it, and the MIR ends
  every local on every way out but the parameters, which the function drops
  where it returns. A scope owns the values that lowering itself makes, and
  drops each one that lowering did not move.
- **One move analysis decides each drop.** `Moves`, a forward analysis of
  the MIR, says which places and fields may hold a value at each point.
  Where a local ends, lowering drops all of it, the parts that were not
  moved out, or, where only some paths give it a value, what a flag says.
  The ownership check's rule of what moves is the same: a call moves each
  argument passed to an `own` parameter, and an assignment moves what it
  reads by value.
- **Drop order is unobservable,** since dropping runs no Truss code.
- **A panic drops nothing;** the operating system reclaims everything.

Each type gets a generated drop, copy, and debug output, compiled once and
shared.

## Lending and yielding methods

**Stage0 inlines a lending or yielding method into its caller.** Each
`yield` hands its place to the caller's statement or runs the loop body
there: `continue` goes on after the `yield`, and `break` takes its stop path,
so the method's locals are dropped as the loop leaves them. That is a plain
loop, with no coroutine at run time. A lend with nothing left to do, as for
an index into a `List`, costs nothing. The design that replaces inlining is
to pass the caller's code to the method as a function, which inlining in the
C compiler makes as cheap.

**The rest of a lending method runs at its part's end,** which the MIR
marks. Where some path reaches that end without the call, a flag, one for
each region that tasks may run at once, says whether the call ran.

**A pulled yielding method is a state machine,** as C# and Kotlin compile
iterators. Each `yield` is a state, and the locals live across a `yield`
become the cursor's fields.

**A cursor holds no evidence.** The evidence it was made with is in a
`provide`'s frame, which the cursor can outlive, so holding it could call a
dropped implementation, a use after free. Each `next` takes the evidence its
caller has.

## Capabilities

A function that `uses` capabilities takes a hidden pointer to *evidence* for
each: a `struct` that `provide` builds on the stack, with a pointer to the
implementation, its vtable, and the evidence for the capabilities the
implementation itself uses. This is Koka's evidence passing: no global state,
and safe for `parallel` code. A capability call costs one indirect call,
small next to the I/O behind it.

**`main` gets the real implementations.** The startup code makes one for
exactly the capabilities in `main`'s `uses`, as a `provide mut` would.

### Tasks

`Tasks` is a capability like any other, so a test can provide a scheduler of
its own; the real `SystemTasks` calls the runtime. The runtime runs each task
on a stack of its own, on a pool of threads:

- **A task that waits parks,** so a parked task holds no thread. Sockets and
  pipes are non-blocking, and the runtime waits for them with `epoll` or
  `kqueue`.
- **A call that blocks holds its thread,** and a spare thread runs tasks in
  its place, so a program keeps as many threads running tasks as the pool
  has.
- **Cancellation is a flag on a group.** A cancelled task's waits return, and
  a blocked system call is interrupted with a signal, so the call fails and
  becomes `SystemError.Cancelled`.
- **A monitor's evidence is replaced by a locking table** whose entries lock,
  call the method, and unlock. The locks go through `Tasks`, so a scheduler
  provided as `Tasks` sees every lock, and a `provide` that needs no lock
  costs nothing more.
- **A test program starts no thread.** Its scheduler runs one task at a
  time.

## Parallelism

A `parallel` branch, and a `parallel for` body, becomes a function of its
own, in two steps. Lowering first writes the branches in place, in order,
as regions, with their drops decided. `Outline` then makes each region a
nested function. It stops at a drop flag shared between regions, which
would let one branch drop a value another had moved, a double free.

A fork runs its first branch and offers the rest to other threads through
Chase and Lev's work-stealing deque. A branch's record lives in the fork's
frame, which does not return until every branch is done, so nothing is
allocated. A range is split into parts whose size depends only on the range,
never on the number of threads, so the result does not depend on the
machine. A test program runs a fork's branches in order.

## Concurrency

A `concurrent` branch, and each `concurrent for` iteration, is a region
outlined as for `parallel`, then spawned through `Tasks`. The join is a scope
cleanup, on every exit, and the scope's temporaries are dropped after it,
since a task may read them until then. An early exit from a task cancels the
group and records its value, and the enclosing code performs the exit after
the join.

## The system interface

Only the standard library reaches the operating system, through
`standard::intrinsic`, a module that exists in no source file and only
`standard` can import. Its operations are one list that the type checker and
code generation both match exhaustively, so a new one compiles only once
both handle it. Each is written into the caller's LIR, never as a call.

**The C library functions are rows of one table** in the compiler, which
gives each function's symbol and C types on each system, how each argument
reaches it, and how much it reads or writes through each address. Truss has
no pointer type, so memory crosses to C only as a view or as storage. The
sizes in the table are the prover's preconditions, so the proof that a call
stays inside its memory is one rule over the table, and a new row needs no
rule of its own. A test compiles the table against the system's own headers,
so a wrong row is a failing test, not a program that misbehaves.

**A handle is a file descriptor** whose drop calls `close`. It is the only
drop that does more than free memory, and it runs no Truss code.

## Program startup and failure

The generated C `main` installs a handler for stack overflow, turns the
arguments into a `List[String]`, makes the real implementation of each
capability in `main`'s `uses`, and returns `main`'s `ExitCode`. A panic or a
stack overflow writes its message and position to standard error and exits
with status 101. A failure report is built in a fixed buffer, so failing
never allocates, even when memory ran out.

## Positions

Positions are relative to their definition, so adding a line at the top of a
file changes no generated code below it. A site that reports a position
names its definition's *anchor*, a constant that holds the file's path and
the definition's first line, defined in one C file generated at link time.
Moving a definition changes only that file.

## Code run while compiling

A constant folds where running its MIR on static data gives exactly its
value: literals, other constants, operations on numbers and `Bool`s that
stay in range, constructors, arrays, pushes onto a storage, and calls of
functions that fold the same way, to a fixed depth and number of steps. A
constant that cannot be folded, a tagged template's check, and a call
whose arguments the prover knows run through this same generator, as
compiled code, so there is one meaning of Truss code to keep correct. It is
built for the host with the target's `USize`, so a 32-bit target's results
are computed on a 64-bit host. A constant's value is written out in binary
and read back into static data. Each run's output is kept under a key of
the code that ran, as a test's result is, so a constant, a template check,
or a call is run again only when that code changes. A run is stopped after
10 seconds.

## Tests

**A test run builds one program** of every test that must run, the standard
library's runner, and a table of the tests. The runner forks one worker per
core, so workers share its loaded code, and sends each a test at a time. A
worker whose test fails ends, and the runner starts a new one.

**A test must free every block it allocates.** Truss has no way to leak a
value, so a test that ends with more live blocks than it started with is a
compiler bug, and every test that compiles Truss also checks its drops.

**A test's result is kept under a key of all the code it can reach,** with
no names, so renaming or moving a definition finds its results done.
Instances that reach each other are keyed as a group, since a key cannot be
made of keys made of it. The key adds code generation's version, the
target, and the flags in `TRUSS_CFLAGS`, since a sanitizer can fail a test
that passes without one. Only a pass with nothing to show is kept, since a failure's message
gives positions, which the key leaves out.

## Failures

| Failure | Reported as |
|---|---|
| A compiler bug: an invariant of code generation does not hold | An exception with its stage and context; the command line reports it once and exits with status 2 |
| A valid program stage0 cannot build yet | An exception with the construct and its position, which the driver gives as the build's error |
| A build that cannot be done | The C compiler's, linker's, or run's output |

**`Verify` checks the LIR** before any C is emitted. Each instance is a C
file of its own that declares its callees from its own side, so a caller and
a callee that disagree would otherwise compile and link without complaint.

## Building

- **An instance's LIR is a query,** so a test run after an edit lowers only
  the instances the edit reached.
- **Object files are kept by an exact key:** the C's text, the C compiler's
  identity, and the flags. The C compiler's identity is only in the object
  key, so upgrading clang invalidates no test result.
- **Every build compiles one C file per instance,** in parallel.
- **A development build inlines only from the standard library and registry
  packages,** so an edit to a project's own function compiles only it again.
  Release builds use ThinLTO, still one file per instance.
- **Stage0 links in full every time,** the one step of an everyday edit
  whose cost grows with the whole program.

## Not built

- A check that reports its caller's position, as Rust's `#[track_caller]`
  does.
- Checkers shipped compiled with the toolchain.
- Converting a float to text without the C library.
- `match` as a decision tree.
- Reserving room for an interpolation.
- Inlining small callees of small callees, and generated functions, in
  development builds.
- The standard library and registry packages at `-O2` in development builds.
- A lending method that lends through a call to itself.
- Waiting, in a test program, for a signal the system ignores unless asked
  for.
- A cursor over a method that lends places to be changed, a lambda in a
  pulled method, and a default passed by address in one.
- A range without both of its ends, as a value.
- A template without interpolation as a constant.
- A `parallel for` over a `List`'s read-only `each`, or over any other
  method, in chunks.
- Parking a task that waits for standard input, a terminal, a child's exit,
  or a file.
- More tasks than the system allows mappings.
- Keeping an instance's C and a linked program by their inputs.
- Incremental linking.
- Release-only optimizations, such as giving proven `requires` to the C
  compiler as assumptions.
- Comparing development and release builds by running both.
- A decision on program arguments that are not UTF-8; stage0 replaces bad
  sequences with U+FFFD.
- A decision on static or dynamic libc on Linux; stage0 links dynamically.
