# Truss Code Generator

This document describes stage0's code generation, in
[`stage0/codegen/`](stage0/codegen): everything between the core form of
[TYPECHECKER.md](TYPECHECKER.md) and a program that runs. It takes the core
form of each definition the program can reach and produces C, which a C
compiler and a linker turn into a program. Lowering needs no name resolution
and no type inference, and reads nothing of a body but its core form; the
syntax tree gives only the source text and positions that failure messages
quote. Every proof obligation has been discharged by then.

It checks nothing about the program: a failure here is a compiler bug, or a
valid program stage0 cannot build yet (see [Failures](#failures)). A program
has no run-time checks but the ones it asks for, such as `checked_add`; test
builds and code run while compiling check every operation that could fail,
so tests need not wait for proofs. Nothing used only by proofs is compiled,
since code generation starts from executable code and never reaches it.

## Structure

```text
checked definitions
      │
      ▼
 Instances ──▶ Layout ──▶ Lower ──▶ Drops ──▶ Yields ──▶ Emit C ──▶ cc ──▶ link
                            │                                              ▲
                            └──────────── LIR, cached per instance ────────┘
```

Code generation reads core forms through queries of the code database. It
does not depend on the prover, and neither the prover nor the database depends
on it; only drivers do: the command line, tests, tools, and
`stage0/evaluator`. The table of C library functions, `stage0/libc`, is
beside it, since the type checker and the prover read signatures from it. A
test fails if a library that is not a driver depends on code generation.

### Why C

Truss has no foreign code, so the standard library's hashing, cryptography,
and text handling run on Truss's own generated code, and the backend must
optimize well. QBE, the obvious small backend, has no inliner, no 128-bit
multiply, no bit-counting or byte-swap instructions, no SIMD, no atomics, and
no way to say that pointers do not alias. C compilers have all of these, and
Truss proves no aliasing, which C expresses with `restrict`. Linking libc
already needs the platform's C toolchain.

### Why one IR before C

A small IR, the LIR, between the core form and C text gives one place for
every transformation, since drop elaboration, the cursor state machine, and
outlining `parallel` branches are passes over a control-flow graph. It is
also what early cutoff compares: a definition whose LIR is unchanged compiles
to the same C, so nothing after it runs again, and the LIR does not depend on
the installed C compiler, so a new one invalidates no test results. The
emitter prints one C construct per LIR construct, which is easy to check and
to port to Truss. The LIR is not SSA: locals are mutable slots, since the C
compiler builds SSA itself, and slots make drops and state machines simpler.

### The C that is emitted

The C is C11 with a few builtins that clang and gcc both provide; clang is
the supported compiler. It includes no header: each file declares the
fixed-width integers from the compiler's predefined macros and only the
functions and helpers it uses, so compiling a file parses only what it needs.
Each type a file defines is followed by a static assertion of its size and
alignment, since the code relies on the C compiler laying it out as code
generation did. The runtime is the exception: one fixed file per target,
compiled once, which includes system headers for signals and alternate
stacks, and holds what must not be Truss, such as the handler for a stack
that ran out, which never allocates.

**Generated code has no undefined behavior,** even if the prover were wrong:

| Rule | How |
|---|---|
| Integer arithmetic wraps if it ever overflows | `-fwrapv`, which turns a prover bug into a wrong value at almost no cost |
| Shift amounts are masked | `x << (n & 63)`, free where the instruction masks anyway |
| No type-based alias analysis | `-fno-strict-aliasing`; Truss's guarantee is given as `restrict` instead |
| Loops are not assumed to end | `-fno-finite-loops`, since a loop without a `time` clause may run until the time limit |
| Floats are exact IEEE 754 | `-ffp-contract=off`, no fast-math, and SSE2 on x86-64 |
| `unreachable` | A compiler-bug report in development builds, `__builtin_unreachable()` in release builds |

Division by zero and `Int64.minimum / -1` are proven impossible, and making
them defined would cost a test per division, so they are the one place a
prover bug could still reach undefined behavior.

**Test builds check instead of waiting for proofs.** A test build, `truss
run`, and code run while compiling check every primitive operation that
could fail, whether or not the prover has finished, so a broken contract is a
failed test rather than a wrong answer or a memory error. The checks do not
depend on which proofs passed, so neither do the test build's LIR and cached
results. `truss build` builds only once every proof is done, so it omits
them. No `requires` is evaluated, since a clause can cost more than the
function it guards, and each check takes constant time: an index, slice,
removal, or insertion out of bounds; a storage operation's own precondition;
each C library call against its row of the table; integer overflow, through
`__builtin_*_overflow`; division by zero; an out-of-range shift; and a float
converted to an integer that does not fit, which C leaves undefined. A
conversion between integer types keeps the low bits unchecked, as the
standard library uses it.

**A check reports the position in the code that wrote the operation,** or, for
standard library code inlined into a program's, the program's call, since the
program's author can change the call and not the library.

The other flags turn off unwinding tables, since nothing unwinds, and
`errno` for math, so `sqrt` is one instruction. The emitted C compiles
without warnings under `-Wall -Wextra -Werror`, which every test that emits
C enforces, except unused parameters, since a trait's implementation may not
read every one, and unused set variables, since `let _ = ...` computes a
value nothing reads.

## Instances

A build compiles only the instances its roots reach: a program's `main`, each
test without a cached result, and each constant or template check that must
run while compiling.

An instance is a definition's path, its ground type arguments, and the
capability sets bound to its capability parameters, since its hidden evidence
parameters differ for each set. A type's generated functions and a pulled
method's state machine are keyed by their type. Collecting instances walks
each instance's LIR breadth-first from a root, in the order references
appear, so the result is the same on every run.

**Symbol names** are made from the key: `t_`, the module path joined with
`__`, a method after a single `_`, and type arguments between markers, as in
`t_standard__list__List_each_Of_standard__Int64_End_`. A marker is `_`, an
`UpperCamelCase` word, and `_`, which no Truss name can contain, so every
symbol reads back one way and two keys never share one. A name longer than 200
bytes is cut and gets a BLAKE3 hash of the whole. Names stay readable in
profilers. Renaming a definition changes its callers' C, but their types are
checked again anyway, and test keys never contain names.

## The lowered IR

An instance's LIR is a main function and its nested functions, its lambdas
and loop bodies, each with typed parameters and locals, basic blocks, and,
for a nested function, an environment of pointers to the enclosing locals it
reads. The types are in `stage0/codegen/lir/`.

- **Every choice about passing values is already made in the LIR** (see
  [Calling convention](#calling-convention)), so the emitter only prints.
- **A call names where its result goes,** whether it is returned or written
  through a pointer, so drop elaboration sees every call that gives a place a
  value.
- **The LIR names variants, never tag values;** tags and niches are the
  emitter's business.
- **Code generation never asks the type checker for a type:** every local has
  a ground type.
- **The LIR is canonical:** parameters first and then locals by first use,
  blocks in reverse postorder, unused locals and unreachable blocks removed,
  so two builds give byte-identical LIR. It is encoded in deterministic CBOR
  (RFC 8949, section 4.2) with code generation's version and hashed with
  BLAKE3. The encoder is small enough to write directly, which keeps the byte
  format under the project's control, since the Truss rewrite must produce the
  same bytes.

## Data layout

The compiler chooses every layout, and no program can observe one: Truss has
no pointers, no `size_of`, and no foreign code. So more layout optimizations
can be added with no change to the language.

- **Built-in types** are the C fixed-width integers, `float` and `double`.
  `Bool` is a byte, 0 or 1, and `Character` a `uint32_t`, and each has spare
  values. `Unit` and empty records are erased. `USize` is a `typedef`, so code
  built to run while compiling can use the target's width on any host.
- **Record fields are placed by alignment, largest first, then by name,** so
  reordering fields never changes the layout. A record with one field is laid
  out as that field, and fields of zero size take no room.
- **A sum type is a tag followed by the largest variant's fields,** with the
  smallest tag that holds every variant. A sum type with no fields is just its
  tag, and one with one variant has none.
- **Niches remove the tag where a field has spare values.** When every
  variant but one has no fields, the others use the spare values of a field
  of that one: non-null pointers, `Bool`, `Character`, and the unused values
  of another sum type's tag. So `Option[List[Int64]]` and
  `Option[Option[Bool]]` are the size of their payload.
- **An `indirect` variant holds one non-null pointer** to a heap block of its
  fields, so it gives a niche too.
- **An `Array` is its elements in place,** in a one-field `struct` so it can be
  passed by value.
- **The one type that owns a buffer is built in:** `Storage[Element]`, a
  pointer, a length, and a capacity, whose drop and copy the compiler
  generates, since Truss types cannot define a drop. An empty one has a
  non-null pointer, so `Option` of it has a niche. `List` and `String` are
  one-field records of it, and `Slice` and `StringSlice` are a pointer and a
  length. A `String` with capacity 0 and a length is static bytes, which
  dropping does not free. `String` is the only type with a static form,
  because a constant is only ever read, so nothing that drops or changes a
  value checks for static memory.
- **`any Trait` is two pointers:** its heap block and a vtable with the value's
  size, alignment, drop, copy when the trait requires `Copyable`, and one entry
  for each object-safe method. An entry's signature is the trait's method read
  with `Self` as the `any` type, so the code that fills a table and the code
  that calls through one agree.
- **`intrinsic::Shared[Value]` is one pointer** to the value, after a header
  the runtime owns with an atomic reference count and a mutex. The count is
  atomic because a reference can be copied and dropped on any thread.
  `shared_update` locks the mutex and calls `change`, which has no `uses`, so
  it cannot wait or deadlock. Drop elaboration does not track the block's
  contents, which the code reaches through a `borrowed` pointer local.
- **A function value is two pointers:** the code and its environment, a
  `struct` on the caller's stack of pointers to the locals the lambda reads,
  so making one never allocates. A function that captures nothing has a null
  environment, and a named function used as a value goes through a small
  adapter. An `own` function-typed parameter accepts only functions that
  capture nothing, so storing one never stores a pointer into a stack.
- **A cursor** is a state number, the method's parameters but its evidence,
  and the locals live across a `yield`. An `own` argument is held as a value
  the cursor owns and drops, since the cursor may outlive the statement that
  made it. Its layout depends on the method's body, so every instance that
  holds one reads that body.

## Calling convention

The C compiler implements the platform's convention; code generation decides
how each Truss parameter becomes C parameters:

| Parameter | 16 bytes or less | Larger |
|---|---|---|
| read-only, including `self` | by value, or `const T *restrict` if it holds an array's elements | `const T *restrict` |
| `mut` | `T *restrict` | `T *restrict` |
| `own` | by value | `T *restrict` to the caller's memory, which the callee now owns and drops |
| result | returned | written through a `T *restrict` first parameter |

- **Every pointer is `restrict`.** A place passed `mut` is used by nothing else
  during the call, and a viewed original does not change while the view is in
  use, which is exactly `restrict`'s guarantee, and lets the C compiler keep
  values in registers across stores.
- **Read-only parameters are never copied to be safe,** since the original is
  frozen.
- **A read-only value that holds an array's elements is passed by address,
  whatever its size,** since a function may return a view of the place a
  read-only parameter views, which a copy in the callee's frame would not
  outlive.
- **Hidden parameters follow the written ones:** the default-presence mask,
  one evidence pointer per capability in `uses`, ordered by path, and the loop
  body of a yielding method. A function value's environment, an evidence
  pointer, and an `any` value's pointer come first.
- **A function with defaults takes a mask** with a bit set for each defaulted
  parameter the caller passed, and its first block fills in the missing ones.
  Every call but one written in source passes every argument. So changing a
  default compiles only the function, with no separate method, as Kotlin's
  `$default` is. A capability method is the exception: its caller fills in its
  defaults, since they are written in the capability, not each `impl`.

## Ownership: moves, drops, and copies

A move is a copy of the value's bytes, after which the source place holds
nothing to drop. The type checker has already rejected every use of a moved
place.

### Who owns a value

Every value lowering makes has an owner from its first moment, so no way out
of the code can forget it:

- **A scope owns the values dropped as it ends.** A block owns its names, and
  each statement owns its temporaries. Scopes are one stack, so `return`, `?`,
  `break`, `continue`, and a loop's stop at a `yield` each leave exactly the
  scopes inside where they go.
- **A local for a value is made with its owner;** lowering has no way to make
  one without, except the result slot, which is the caller's once the function
  returns.
- **A parameter says whose it is.** The function owns an `own` parameter. Any
  other is the caller's, and one passed by value is marked *borrowed*, so
  nothing drops it.

### Drop elaboration

Lowering writes `drop(place)` wherever a scope ends, meaning "drop whatever
this place still owns here". `Drops` works out what that is, as Rust's drop
elaboration does: a dataflow analysis finds at each point which places and
fields may own a value. Each drop then becomes nothing, a drop of the whole
place, a drop of each remaining field after one was moved out, or a drop
behind a flag, where the place owns a value on some paths only. A flag is a
`Bool` local, written at entry only for a parameter, so a local's flag is
named only where the local is, which matters for outlining. A sum type's
value is asked its variant first, since where a `match`'s arms meet it may
hold another.

- **A place can be given a value in parts:** a record once every field with
  something to drop has one, and an array by writing every element before
  anything reads it.
- **A write gives a place a value and drops nothing;** whatever replaces a value
  drops it first. An assignment evaluates its new value into a temporary,
  drops the old value if the place still owns it, and moves the temporary in.
  The temporary also keeps a call's large result apart from its arguments,
  since the callee writes it through a `restrict` pointer, as in
  `point = moved(point)`.
- **`Drops` checks its input:** no write is to a place that may own a value,
  and no local owns one where a function returns. So a mistake in lowering is a
  compiler bug where it is made, not a leak in the runs that reach it.
- **Drops of trivial types are removed,** and the rest run in reverse order of
  declaration, which no program can observe, since dropping runs no Truss
  code.
- **A panic drops nothing;** the operating system reclaims everything.

### Generated functions for each type

`Glue` generates a drop, a copy, and debug output for each monomorphic type,
each an instance of its own, compiled once and shared.

- **Drop.** A type is *trivial* when it holds no `Storage`, no `indirect`
  variant, and no handle; its drop is empty and removed. `Storage` drops its
  live elements and frees its buffer unless its capacity is 0, which is how
  static bytes go unfreed.
- **Copy.** A trivial type is a memory copy. A `Storage` that owns no buffer,
  empty or static, is shared rather than copied, and one that owns a buffer is
  copied in one allocation of its length, by one memory copy for trivial
  elements. One module defines `Storage` and `View`, and nothing else in code
  generation names their fields.
- **Debug output** is Truss as it would build the value, such as
  `Point(x: 1.0, y: 2.0)` or `[1, 2, 3]`, with floats as the shortest decimal
  that reads back as the same value. It appends to storage its caller owns, so
  there is no buffer of the program's.

`with` on an owned base writes the new fields into its memory, and a compound
assignment moves the old value into an `own self` version of the operator,
which reuses its memory.

## Lowering expressions

- **Primitive operations are never calls,** at any optimization level: the
  standard library declares them through traits, so typing and proofs see
  ordinary `impl`s, and the compiler emits their bodies directly. Indexing
  and slicing the built-in collections become address arithmetic, checked
  only in a test build.
- **Float comparisons are lawful:** `a == b` is
  `a == b || (a != a && b != b)`, `a < b` is `a < b || (a == a && b != b)`,
  and the `ieee_` comparisons are the bare C operators. A float is written as a
  hexadecimal literal, which is exact. Whether a float fits an integer type is
  tested against powers of two, which every float type holds exactly.
- **A range loop counts in the range's own type,** and an inclusive range
  stops after its last value without adding one to it, which could overflow.
  A range of characters skips the surrogates.
- **Conditions are lowered as jumps** to a true block and a false one, through
  one lowering for `if`, `while`, guards, `&&`, `||`, `!`, and `is`. The names
  `is` binds are in a scope closed, with its drops, on every way out, the false
  one included.
- **A guard sees views** of its arm's bindings, so a failing guard leaves the
  value whole for the next arm.
- **Alternatives that bind a name are tested as separate patterns,** and the
  code after them is emitted once, with each name in a slot that every
  alternative fills.
- **String interpolation builds into one `TextBuilder`,** never a `Template`.
  Other tags build a `Template` with the literal text as constant data.
  `Character"a"` and `UInt8"\n"` are plain numbers.

### Literals and constants

- **A constant is static data,** emitted once with a symbol, in a read-only
  section. An instance compiles to code or to data, a ground type and a static
  value that the emitter writes as C initializers.
- **A constant's value is the result of running its expression,** and lowering
  folds what it can to exactly that, to save the run: literals, arithmetic
  with Zarith and IEEE floats, and values built of parts that fold, following
  the block a list literal desugars to. Whatever it cannot fold, or cannot
  fold exactly, is run (see [Code run while compiling](#code-run-while-compiling)),
  so folding can be incomplete and never wrong.
- **A list or map literal in a body** allocates its buffer and fills it. A
  `Set` or `Map` literal inserts each entry with the type's own `insert`, so it
  keeps the collection's order exactly as inserting by hand would.

### Code that does not ship

- **`echo`** passes the value's debug output and its position to the runtime,
  which writes to the test's report in a test and to standard error otherwise.
- **`todo`** reached in a test tells the runner the test is incomplete and ends
  the worker.
- **A method of a capability's implementation is reached only where reached
  code calls that method of the capability,** though the implementation is
  compiled whole for its table. So a `todo` in one method stops only programs
  that can call it, and an implementation can be written a method at a time.

## Generics and traits

Every trait method call is resolved before code generation, so after
monomorphization each is a direct call. A trait's provided methods are
compiled for each type that uses them. A derived method is lowered from the
core form the type checker generates for it, and may be inlined into callers
even in development builds, since its code comes from the type's shape, on
which every caller already depends. An `any` call loads the method from the
vtable.

## Lending and yielding methods

### Loops and lending calls

The design is that a lending or yielding method takes the caller's code as a
function, the rest of the statement or the loop body, which returns whether
to continue. Each `yield` becomes a call of it followed by a switch, to the
next block or to the `yield`'s stop path, whose drops are already placed. The
caller's loop body records in its environment why the loop ended, and the
caller acts on it after the method returns. A lending method always
continues after its `yield`, so it runs to its end before the caller acts on
an early exit. With the method and the body in one C file, the C compiler
inlines both, and the loop becomes a plain loop over the buffer.

**Stage0 inlines instead.** Its lowering writes the method's body into the
caller, with each `yield` handing its place to the caller's statement or
running the loop body there: `continue` goes on after the `yield`, and `break`
takes its stop path, so the method's locals are dropped as the loop leaves
them. That is the plain loop the C compiler would make, with no rewriting of
the caller into continuation-passing style. The caller then depends on the
method's body.

- **A lending method resumes after the caller's statement,** so it may lend a
  value it made. In an `if` or `while` condition it resumes after the
  condition, or after the then-block or the body when the core form's
  `binds_lent_part` is set. Its rest, the code after the `yield` and the drops of its
  owned values, is written once, and the scope that owns the lend sets a
  selector to the way it was going and jumps there as it ends, on every way
  out. A lend with nothing left to do, as for an index into a `List`, costs
  nothing.
- **A method with a `yield` on several paths** stores the address of its lent
  part and its number at each, and the caller resumes from the one reached.
- **A yielded constructor of places is a lent value** of a type of its own,
  `Ground.Lent`, laid out as the yielded type with an address in place of each
  lent field. So `Slice.get` lends an `Option[Element]` as one pointer, null
  for `None`, whatever the element's size. The caller reads a lent field
  through its address. Used whole, a lent value is copied: read-only, the copy
  holds the places' bytes and owns nothing; lent `mut`, each place's value is
  moved in and moved back as the scope ends, which is safe because a place
  lent `mut` is never inside a variant.
- **A quantifier in code is the same loop with another body,** which leaves as
  `break` does at the first value that decides the answer.
- **A loop over a yielding method already inlined around it,** as a tree's
  `each` over its subtrees, would be inlined forever, so stage0 pulls a cursor
  over the inner call in a heap block that the loop frees on every way out.
  This is the room for each level of recursion, which the language still does
  not let code pull.

### Cursors

A pulled yielding method is lowered a second time, as a state machine, as C#
and Kotlin compile iterators. `next` gives an owned value: a computed value is
moved out, and a yielded view of a place is copied.

1. Each `yield` is a state, numbered in block order, with 0 the start and one
   past the last the end.
2. The locals live where a `yield` resumes or stops, found by liveness, and
   the parameters but the evidence, become the cursor's fields; each kept
   local is read and written through the cursor.
3. `next()` switches on the state and jumps past that `yield`, and each `yield`
   sets the state and returns `Some`.
4. A `for` loop inside the method is an explicit inner cursor, a field of the
   outer one, since a loop body cannot stop partway.

**A cursor holds no evidence.** The evidence it was made with is in a
`provide`'s frame, which the cursor can outlive, so holding it could call a
dropped implementation, a use after free. Each `next` takes the evidence its
caller has. The drop function has none, and a stop path that reads evidence is
a compiler bug.

A cursor's drop runs the stop path of the `yield` it is at, which is the
method ending at its last `yield`. The compiler derives an `impl` of `Cursor`
for the yielding function, whose `Uses` is the method's `uses`, so generic code
calls the state machine through a bound, and `any Cursor[Element = Int64]` gets
an ordinary vtable.

## Capabilities

### Evidence

A function that `uses` capabilities takes a hidden pointer to *evidence* for
each, a small `struct` that `provide` builds on the stack: a pointer to the
implementation value, its vtable for the capability, and the evidence for the
capabilities the implementation itself `uses`, taken from around the
`provide`. A call such as `Clock.now()` loads `now` from the vtable and calls
it with the implementation and its own evidence. This is Koka's evidence
passing: no global state, and safe for `parallel` code. A capability call
costs one indirect call, small next to the I/O behind it.

- **A provided place is passed by address,** so `provide mut files` changes
  `files`; any other value is a temporary to the end of the statement.
- **Narrowing needs nothing special:** inside an implementation of `FileRead`,
  `FileRead.read` uses the evidence captured from outside the `provide`.
- **Providing a type builds one evidence `struct` per capability,** all
  pointing at the same value.
- **Capability parameters and associated capability sets are decided by the
  instance,** so an instance's signature names no set, and each instance takes
  evidence for exactly the capabilities its type arguments give.
- **A call through `any` passes no evidence for an associated set,** since the
  type checker makes an `any` only where each set is empty.
- **A function value with `uses` takes evidence when called,** so a callback
  stored in an `own` parameter gets its evidence from whoever calls it.
- **`Panic` has no evidence:** it cannot be provided, so `Panic.crash` is a
  direct call into the runtime.

**`main` gets the real implementations.** The standard library implements each
standard capability with an ordinary type, such as `SystemConsole`. The
startup code makes one for exactly the capabilities in `main`'s `uses`, with
evidence on the stack, as a `provide mut` would, and an external test gets its
declared capabilities the same way.

### Tasks

`Tasks` is a capability like any other, so a test can provide a scheduler of
its own; the real `SystemTasks` calls the runtime. Its methods open, spawn
into, join, and cancel task groups, wait on keys, lock mutexes, and yield.

The runtime runs each task on a stack of its own, and the pool's threads run
the tasks that are ready:

- **A task that waits parks.** Waiting for a key, a mutex, or a group switches
  back to the thread, which takes the next ready task, so a parked task holds
  no thread. A thread that is not a task, such as `main`'s, blocks instead,
  since a task run on top of its computation could hold that computation up.
- **A call that blocks holds its thread.** The C library's rows that can block
  are named in the table, and lowering brackets each call. A runtime thread
  that ticks every millisecond while tasks are ready counts a thread as
  blocked once its call has lasted a whole tick, as Go's `sysmon` does, since
  counting from the start would call a spare thread for every short read.
- **A sleep, and a wait for a socket or a child's pipe, park the task.** Sleeps
  are a heap of timers ordered by deadline. The standard library's sockets and
  pipes do not block: after `EAGAIN` the library waits on a ticket it took
  before the call, so it cannot miss the descriptor becoming ready between
  the two. The runtime registers the descriptor, edge-triggered, with `epoll`
  or `kqueue`, and forgets it at `close`, since the system reuses a closed
  descriptor's number. A socket's time limit applies only to a blocking call,
  so the wait reads it and starts a timer.
- **One wait covers several descriptors,** so `Processes.run` can read a
  child's output and error output as the child writes them, since a child that
  fills one pipe while the program waits on the other never ends.
- **Spare threads run tasks in place of blocked threads,** one per blocked
  thread, so a program runs tasks on as many threads as the pool has. A spare
  thread sleeps when it is not needed and never exits.
- **A task changes threads,** so the runtime's per-thread state follows it.
  Generated code reads `errno` through the runtime, since glibc declares
  `errno`'s address constant per call, and a C compiler could reuse one
  thread's address after the task moved.
- **A `parallel` block in a task** forks on its thread's own queue, and leaves
  on the thread it entered on, since a branch uses no capability and cannot
  park.
- **Cancellation is a flag on a group,** inherited by the groups its tasks
  open. `cancel` sets it once and readies each parked task in a cancellable
  wait; a task records where it parks before it reads the flag, so one of the
  two sees the other.
- **A cancelled task blocked in a system call is interrupted.** A runtime
  thread sends `SIGURG` every few milliseconds, until the group is joined, to
  each thread running a blocked task of it, and the handler is installed
  without `SA_RESTART`, so the call fails with `EINTR` and becomes
  `SystemError.Cancelled`. It is repeated because a task can start a blocking
  call just after one. A host lookup cannot be interrupted.
- **Waiting on a key** uses a fixed table of slots that count wakes, so two
  keys can share a slot, and a waiter tests its condition again.
- **A mutex** is a word: 0 unlocked, 1 locked, 2 locked with waiters, as in
  Drepper's "Futexes Are Tricky", so an uncontended lock or unlock is one
  atomic operation.
- **A test program and code run while compiling start no thread.** `spawn` runs
  the task to its end, in spawn order, and a `wait`, which would deadlock,
  panics.

**A `mut` implementation provided where its body can use `Tasks`** gets its
evidence replaced by the capability's *locking table*, generated once per
capability, whose entries lock, call the method through the implementation's
own evidence, and unlock. The locks go through `Tasks`, not straight to the
runtime, so a scheduler provided as `Tasks` sees every lock. An implementation
of `Tasks` is never locked, and a `provide` that needs no lock costs nothing
more.

**Coroutines,** in the intrinsic module, serve a scheduler written in Truss
that runs one task at a time. Each has an `mmap` stack as large as the main
thread's, with a guard page, and a switch is a function in assembly for x86-64
and ARM64 that swaps callee-saved registers and stack pointers, with no system
call. The sanitizers are told of each switch, so code in a coroutine is checked
like any other.

## Parallelism

A `parallel` branch, and a `parallel for` body, becomes a function of its own,
in two steps with drop elaboration between them.

**Regions.** Lowering writes the statement's code in place, in order, and marks
where each part starts. Run in place, the regions have the statement's
semantics, so drop elaboration analyzes them as ordinary code.

- **A block's branches** are each a region, with one way in and one way out.
- **A `parallel for` over a range** is one region holding the loop over a part
  of the indexes, counted as `UInt64`.
- **A `parallel for` over a method that yields by position** is that method's
  own loop, since its iterations share nothing. Any other `parallel for` runs
  in order, since its iterations may depend on each other.

**Outlining.** `Outline` then makes each region a nested function. A local
only the region names becomes the function's; a shared local is reached
through the environment, safe because the type checker showed that branches
change no place another uses. `Outline` stops at a local that two regions
share and one gives a whole new value, which no program can make, and at one
that the parts of a loop share and the body gives a whole new value. The case
that matters is a drop flag: a shared one would let one part drop a value
another had moved, a double free.

**The runtime's threads.** A fork runs its first branch and offers the rest on
its own queue, Chase and Lev's work-stealing deque, from which an idle thread
takes from the far end. A branch's record lives in the fork's frame, which does
not return until every branch is done, so nothing is allocated. There is a
thread per core, started at the first fork, each with every signal held back
so signals go to the first thread. `TRUSS_WORKERS` changes the number of
threads and nothing a program does. A range is run by halves, down to parts
whose size depends only on the range, never on the number of threads. A test
program runs a fork's branches in order. The text of a failure is built by one
thread at a time, so one failure is reported.

## Concurrency

A `concurrent` branch, and each `concurrent for` iteration, is a task region
outlined as for `parallel`, then spawned through `Tasks`.

- **A block** opens a group, spawns each branch, and joins.
- **A `concurrent for` over a range** runs the loop in the enclosing function
  and spawns an iteration at each index, stopping if `spawn` returns false.
- **Over a method that yields by position,** the method is inlined and its
  range loop spawns the tasks, so a task borrows its own element.
- **Over any other method or a cursor,** the method runs in the enclosing
  function and spawns a task at each `yield`, with the value's bytes in a heap
  block the task frees. The task owns an owned value and drops it, and holds a
  bitwise copy it never drops of a read-only place, which the ownership check
  has shown stays valid until the join.
- **The join is a scope cleanup,** on every exit, and the scope's temporaries
  are dropped after it, since a task may read them until then.
- **A pulled method has no task regions,** so `concurrent` code in one is not
  built.

**An early exit** from a task evaluates its value, calls `Tasks.cancel`, and, if
it was first, records its number in `winner` and its value in
`return_value`; otherwise drops it. After the join, the enclosing code
switches on `winner`, and performs the exit or repeats in the next enclosing
task. Each branch of a block has its own `winner` and `return_value`, since
outlining rejects a local one region assigns and another uses.

## The system interface

Only the standard library reaches the operating system, through
`standard::intrinsic`, a module that exists in no source file and only
`standard` can import. Its operations are one list that the type checker and
code generation both match exhaustively, so a new one compiles only once both
handle it. `Intrinsics` writes each into the caller's LIR, never as a call, so
the C compiler sees it whole.

- **A view does not record whether its elements may be written,** so a view to
  change comes from `storage_view_mut`, which gives static storage a buffer of
  its own first, or from an array held `mut`.
- **A view is a value to the prover,** so after its elements are changed the
  standard library says the owner's elements are the view's with
  `storage_take_view` and its kin, which are no code, except a check in a
  build with checks.
- **`storage_from_array` and `array_from_storage`** move elements between an
  array and storage, which is the only way to take an array's elements one at
  a time, and to make an array whose length is a type parameter.
- **Storage never grows by itself.** How much room to make is the standard
  library's to say, in Truss, so the prover reads it as any code: a push that
  finds no room at least doubles the capacity.
- **`storage_shorten` forgets elements in one step,** only for `Plain`
  elements, since forgetting one that owns something would leak it.
- **Static storage** owns no buffer, so dropping frees nothing and copying
  shares it, and every operation that writes gives it a buffer first. A
  `List`, `Map`, or `Set` constant records its capacity as its length, so a
  `copy()` of it copies.
- **Allocation failure ends the process** with a message.

### The C library

The intrinsic module holds the C library functions the standard library calls,
each from one row of a table in the compiler, which gives the symbol and C
types on each system and how each argument reaches it. Truss has no pointer
type, so memory crosses to C only as a view, which the function reads; as
storage, through the address after its last element for a function that fills
room or of its first for one that changes elements; or as `mut` numbers, which
make a small structure the function fills, as a `timespec`'s two numbers. A
row can fix an argument, such as the request of `fcntl`, since another request
would read the next argument as an address. A list of addresses is a
`View[USize]` filled with `view_address`, and nothing turns a number back into
an address.

- **A row also says how much the function reads or writes through each
  address,** and which count bounds its result. Code generation does not use
  these: they are the prover's preconditions, so the proof that a call stays
  inside its memory is one rule over the table, and a new row needs no rule of
  its own.
- **A structure whose fields differ in type** is storage of a number several
  of them make, as `pollfd`s are, and **a larger structure whose layout differs
  between systems** is filled as bytes, with the table giving its size and the
  offset of each field the standard library reads, as for `struct stat`.
- **The numbers the headers define,** such as `EINTR`, are operations that take
  nothing, and lowering writes their values. So the type checker and the
  prover see the same signatures on every system, and only code generation's
  results depend on the system, which is part of the target: Linux or macOS,
  on x86-64 or ARM64. Stage0 builds for the system it runs on.
- **A function only some systems have** is called only where
  `system_is_macos()` and its kin, which lowering writes as constants, say it
  exists, and a call of it elsewhere is lowered to a failure, so a program
  never names a symbol its C library lacks.
- **A test compiles the table against the system's own headers,** checking
  every number, prototype, and structure layout, so a wrong row is a failing
  test, not a program that misbehaves.
- **A host lookup goes through a function of the runtime's,** written in C,
  since `getaddrinfo` gives a chain of structures that hold each other's
  addresses, which the table cannot describe. Its row is in the table, so the
  prover holds the call to its room in the same way.

### Handles

`Handle` is a file descriptor in an `Int32`, neither `Copyable` nor `Plain`,
whose drop calls `close`. `handle_release` consumes one without closing it,
so `Handles.close` can report an error from `close`. A handle's is the only
drop that does more than free memory, and it runs no Truss code.

The standard library's real implementations are Truss on the C library:

- **The console's streams are new descriptors** for the same files, made with
  `fcntl`, so a stream owns the descriptor it closes and the process keeps its
  first three. Its terminal is `/dev/tty`, whatever the streams were
  redirected to.
- **A directory is read a block at a time** with `getdents64` on Linux and
  `getattrlistbulk` on macOS, read at the offsets the table gives, with every
  stated length held to the bytes filled. `opendir` is not used, since it
  keeps a structure Truss would have to hold an address of.
- **The environment is read by index from the first entry each time,** so it
  never reads past the last.
- **Processes start with `posix_spawnp`,** with both ends of each pipe closed
  in the child, so a child never holds the end its parent writes it with.
- **A signal is recorded by a handler that writes to a pipe,** which a runtime
  thread reads, so a task on any thread can wait for it, and a signal that
  arrives between two waits is there for the second. On macOS a signal that
  was pending before the first wait can be taken only by the first thread.
- **Every socket is non-blocking,** so a task parks for it. A connection's
  time limit is set before `connect`, since on macOS `setsockopt` fails on a
  socket whose connection was refused, which would hide the refusal. A
  datagram socket that is not bound is IPv6 carrying IPv4 where the system
  has IPv6.

## Program startup and failure

The generated C `main` installs a handler for stack overflow on an alternate
stack, since Truss code has no unsafe operations, so a segmentation fault
means the stack ran out; turns `argc` and `argv` into a `List[String]`,
replacing bad UTF-8 with U+FFFD; makes the real implementation of each
capability in `main`'s `uses`; and returns `main`'s `ExitCode`.

A panic writes its message and position to standard error and exits with
status 101, as does a stack overflow; running out of memory writes a message
and calls `abort`. In a test worker each is reported to the runner instead.
A report's text is built in a fixed buffer, so failing never allocates, even
when memory ran out. None of this uses stdio, so there are no buffers to flush.

## Positions

Positions are relative to their definition, so adding a line at the top of a
file changes no generated code below it. A site that reports a position
passes the address of its definition's *anchor* and its line and column
within the definition. An anchor is an external constant, one per definition,
holding the file's path and the definition's first line, defined in one C file
generated at link time, so moving a definition changes only that file. A
release build names files from the package's root, so the program is the same
wherever it was built, and can emit `#line` directives, since it compiles
every definition again anyway.

## Code run while compiling

A constant that cannot be folded, a tagged template's check, and a call the
prover knows the arguments of run through this same generator, as compiled
code, built for the host with the target's `USize`, so a 32-bit target's
results are computed on a 64-bit host.

- **A constant's evaluator** writes the value's binary form to standard output:
  a scalar's bytes, a record's fields in order, a variant's index and then its
  fields, an array's elements, and storage's length and then its elements. The
  compiler reads it back into static data by the type's shape. Values are
  never shared, so every value is a tree. It runs with no time limit, since
  its code is pure and terminates.
- **A `Template_check` instance** builds a template of the literal texts and no
  parts, evaluates each `requires` clause of `from_template` that can run, and
  writes each out as a `Bool`. In a clause that runs, `a ==> b` evaluates `b`
  only where `a` holds, since `b` may be defined only there. This is the one
  place a clause is evaluated. It runs with the test time limit, and its
  results are kept under the key of the code that ran, as test results are.
- **A `Call_evaluation` instance** calls a function with constant arguments and
  writes its result.

## Tests

### The test program

A test run builds one program of every test that must run, the standard
library's runner, and a generated `main` that gives the runtime a table of
the tests. The runner is Truss on `fork`, `pipe`, `poll`, and `waitpid`. It
forks one worker per core after startup, so workers share its loaded code,
sends each a test's number, and reads back records of the test's end and its
`echo` output. Failing in a worker writes a record to its pipe where another
program writes to standard error.

- **A worker whose test fails ends,** and the runner starts a new one, so a new
  process starts only after a failure. Ending the worker also lets an `assert`
  inside a lambda end its test. A worker whose test exceeds the time limit is
  killed.
- **A test must free every block it allocates.** The runtime counts live
  blocks, and a test that ends with more than it started with is a compiler
  bug, since Truss has no way to leak a value, so every test that compiles
  Truss also checks its drops.
- **The runner writes a line as each test starts and a record as each ends,**
  so `truss test` can show progress. Results come in the order tests end, and
  `Compile.run_tests` puts them back in order.

### Test results

A test's result is kept under a key built from all the code it can reach,
with no names, so renaming or moving a definition finds its results done.

- **An instance's own hash** is of its LIR with each reference written as its
  place in the instance's references, and each path as a number in the order
  first met.
- **The key of everything an instance can reach** is its own hash and its
  references' keys, in order.
- **Instances that reach each other are keyed as a group,** since a key cannot
  be made of keys made of it. Tarjan's algorithm finds the groups among
  everything the wanted tests reach, and an instance of a group is keyed by
  the group as a walk from it reaches it.
- **The wanted tests are an input,** which a driver states before asking for
  their keys, since finding groups needs somewhere to start, and starting from
  every test would lower every test's code when one is asked about. Finding
  the groups reads only reference lists, and changes only when a group does,
  so an edit that forms no group costs the keys of the instances that reach
  it. It is the one step here whose cost follows the tests asked about, not
  the change.
- **A test's key adds code generation's version and the target,** since
  results such as `USize.maximum` differ between targets.

Two programs that differ only in names give the same key, and any change to
the reached code, a layout's included, changes it. Stage0 keeps only a pass
with nothing to show, never an external test's, since a failure's message and
an `echo` give positions, which the key leaves out. A sanitized run keeps
nothing.

## Failures

| Failure | Reported as |
|---|---|
| A compiler bug: an invariant of code generation does not hold | An exception with its stage and context, which nothing catches; the command line reports it once and exits with status 2 |
| A valid program stage0 cannot build yet | An exception with the construct and its position, which the driver gives as the build's error |
| A build that cannot be done | The C compiler's, linker's, or run's output |

A broken invariant that the OCaml standard library finds first is turned into
a bug where an instance is lowered, so no failure of the compiler reads as a
failure of the program.

**`Verify` checks the LIR,** because each instance is a C file of its own that
declares its callees from its own side, so a caller and a callee that disagree
would compile and link without complaint. Each instance is checked once its
passes have run: its blocks and locals exist, no `yield` is left, returns
match the result, a call passes as many arguments as its target takes, and
writes a large result to a place that shares no memory with a place it also
passes by address. Everything a build links is checked together before any C
is emitted: each call, table entry, and function value names its callee with
the signature the callee has.

## Building

- **An instance's LIR is a query,** keyed by the instance, the target, and
  whether the build has run-time checks, so a test run after an edit lowers
  only the instances the edit reached. Each computation lowers in a context of
  its own, so nothing is cached where another query could use it without
  reading its inputs.
- **A constant computed by running code** is the one result a query cannot make,
  so its query says so, the build runs the evaluator, and every instance that
  uses the constant refers to it by name.
- **Object files are kept by an exact key:** the C's text, the C compiler's
  identity, and the flags. Early cutoff happens at the LIR: an unchanged LIR
  gives unchanged C, so its object is found and no test that reaches it runs
  again. The C compiler's identity is only in the object key, so upgrading
  clang invalidates no test result. Each object is written under a temporary
  name and renamed into place, and an object a build finds is touched, so a
  cache that drops by age drops only unused ones.
- **Every build compiles one C file per instance,** in parallel.
- **A development build copies small callees into the caller's file** as
  `static inline`, only from the standard library and registry packages, so
  an edit to a project's own function compiles only it again. Development
  builds compile at `-O1`, which avoids the stack traffic of `-O0`.
- **Release builds** compile at `-O2` with ThinLTO, still one file per instance,
  so each object is cached on its own.
- **`truss build` and `truss run` refuse a program whose `main` can reach a
  `todo`,** which `Compile.unshippable` finds without compiling, and `build`
  refuses an `echo` too.
- **Stage0 links in full every time,** the one step of an everyday edit whose
  cost grows with the whole program, with the objects' names in a file, since
  a command line cannot hold them all.

## Not built

- **Lowering from the MIR.** Code generation lowers the core form itself.
- **A check that reports its caller's position,** as Rust's `#[track_caller]`
  does, for a check that fails in a called library function.
- **A constant's value kept between runs.**
- **Checkers shipped compiled** with the toolchain, for each host and width of
  `USize`.
- **A float's text without the C library.** The loop is Truss; the digits are
  `snprintf`'s and the check `strtod`'s.
- **`match` as a decision tree,** which the MIR builder is to make.
- **Room reserved for an interpolation,** since the literal lengths are known.
- **Small callees of small callees, and generated functions, in the caller's C
  file.**
- **The standard library and registry packages at `-O2` in development
  builds.**
- **A lending method that lends through a call to itself.**
- **Waiting, in a test program, for a signal the system ignores unless asked
  for,** which macOS discards while it is blocked.
- **A cursor over a method that lends places to be changed,** a lambda in a
  pulled method, and a default passed by address in one.
- **A range without both of its ends, as a value.**
- **A template without interpolation as a constant,** computed while compiling
  and copied where an owned value is needed, which is never more expensive
  than building it; and a template's literals as static data.
- **A `parallel for` over a `List`'s read-only `each` in chunks.** It is a
  `while` loop that keeps an index, and cannot be a `for` over a range yet,
  since inside a `for`, `yielded` names the loop's own cursor, so its
  `ensures` cannot be proven.
- **A `parallel for` over any other method at once,** which needs a way for a
  collection to split itself, as rayon has.
- **A wait for standard input, a terminal, a child's exit, or a file that parks
  the task.** Each holds a thread: an inherited descriptor shares its mode with
  other processes, `waitpid` blocks, and a file cannot be waited for with
  `epoll` or `kqueue`.
- **More tasks than the system allows mappings,** about thirty thousand on
  Linux by default, since each task's stack is a mapping with a guard page.
- **Keeping an instance's C and a linked program** by their inputs.
- **Incremental linking,** likely through a long-running runner that loads
  changed definitions as a small shared library, which needs no state carried
  over since Truss has no mutable globals.
- **Release-only optimizations,** such as calling `main`'s real
  implementations directly and giving proven `requires` to the C compiler as
  assumptions.
- **Comparing development and release builds** by running both.
- **Program arguments that are not UTF-8** are not decided; stage0 replaces bad
  sequences with U+FFFD.
- **Static or dynamic libc on Linux** is not decided; stage0 links dynamically.
