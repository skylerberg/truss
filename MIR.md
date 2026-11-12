# Truss MIR

This document describes the design of stage0's mid-level IR, the MIR, in
`stage0/mir/`. Its builder is built, and no stage reads it yet:
[Not built](#not-built) lists the order the rest is built in. The MIR is a control-flow graph of each
definition's body, built from the core form that
[TYPECHECKER.md](TYPECHECKER.md) describes. The ownership check, the prover
([PROVER.md](PROVER.md)), and code generation ([CODEGEN.md](CODEGEN.md)) are
to read it in place of the core form. The MIR of a definition is a query
of the code database, which [DATABASE.md](DATABASE.md) describes.

## Motivation

The core form is a tree that is still close to the source: it has
compound assignment, five kinds of loop, lending calls as places, and
specifications in the same type as executable code. The ownership check,
the prover, and code generation each lower that tree themselves. The
ownership check builds its own control-flow graph of points, code
generation builds the LIR, and the prover runs the tree forward. So each of
them decides, separately:

- the order in which operands, index keys, and right sides are evaluated
- where a temporary lives, and where a borrow of one ends
- how `match`, `let ... else`, `?`, loops, and early exits flow

When two of them decide differently, the program that is checked is not the
program that runs. The prover then proves facts about code that is not
compiled, which is an unsound proof, and the ownership check accepts code
whose compiled order is a use after move. The MIR makes each of these
decisions once, in its builder, and every consumer reads the result.

The MIR also spares each consumer the parts it never needs. Code generation
and the ownership check read no specification, and the prover reads no
drop. Each of them still matches on every core form today, with cases that
can never be reached.

Rust has the same shape. Its MIR is generic, its borrow checker runs on
MIR, code generation monomorphizes MIR, and the Rust verifiers Prusti,
Creusot, and Kani read MIR. Swift's SIL serves its ownership verification
and its optimizer the same way. Verus is the exception: it reads Rust's
HIR into a verification IR of its own, so it must match rustc's semantics
separately.

## Where it sits

```text
syntax tree ──▶ type checker ──▶ core form ──▶ MIR builder ──▶ MIR
                                    │                          │
                              exhaustiveness   ┌───────────────┼─────────────────┐
                                             ▼                 ▼                 ▼
                                      ownership check        prover     monomorphize ──▶ LIR ──▶ C
```

The core form stays the type checker's output. The exhaustiveness check of
patterns reads it, as Rust's does on THIR, because it needs the patterns as
written. The MIR builder is its only other reader.

PROVER.md explains why the prover has no proof program between Truss and
the logic, as Boogie and Why3 have: a second representation of every body,
read only by the prover, would cost more than it gives. The MIR is a
second representation, but all three consumers read it, and it
makes them agree.

## Contents

| The MIR has | Because |
|---|---|
| Generic bodies, before monomorphization | The prover proves a generic function once for every instantiation. Code generation substitutes type arguments into the MIR of each instance, as rustc does. |
| Places and values, not memory | The prover models values. The ownership check has ruled out aliasing, so an update of a `mut` place is an update of a value. Pointers, layout, and calling conventions are the LIR's. |
| Explicit temporaries, in evaluation order | Each operand is evaluated into a local before the operation that uses it, so the order is the order of statements. |
| Temporaries that hold a borrowed place | `items[next()] += 5` lends `items[...]` once and writes through the loan. The core form cannot hold a place across statements. |
| Origins | Every statement and terminator has the origin of the core node it comes from, so a diagnostic finds its source text. |
| Specifications as core expressions | A contract, a loop clause, and a condition that cannot run are core expressions, which only the prover reads. |
| Ghost code | `proof` blocks, conditions that cannot run, and the locals that specifications need, such as `yielded`, are ghost statements. Code generation and the ownership check skip them. |

| The MIR leaves out | Where it is |
|---|---|
| Drops | Code generation elaborates them from the MIR's moves, as it does on the LIR today. |
| Instances, layout, the calling convention | The LIR |
| Unwinding | Nothing unwinds: a panic ends the program (DESIGN.md, "No hidden failure"), so a call is a statement and not a terminator. |
| The patterns as written | The core form, for the exhaustiveness check |

## Bodies

A definition's MIR is its body and the bodies of its lambdas. Each body has:

- **Locals,** numbered, each with a Truss type: the parameters, the
  bindings of patterns, temporaries, borrow locals (see
  [Places and operands](#places-and-operands)), and ghost locals. Each has
  the name it is written with, or none.
- **Basic blocks,** each a list of statements and one terminator.
- **For a lambda, its captures:** the locals of the enclosing body that it
  borrows, in order of first use.

The control-flow graph is reducible. Every loop is a natural loop with one
header, because Truss has no `goto`, and `break` and `continue` leave only
loops that enclose them.

### Places and operands

A place is a local followed by projections: a field of a record, and a
field of a variant that a test has selected. A constant's static data is a
place too, and it is read-only.

A local is one of:

- **a source local:** a parameter, `self`, or a local that a pattern or a
  lambda binds, with its mode. A local bound with `Read` or `mut` is the
  place it was bound to, as a borrowed parameter is the caller's place, and
  not a copy of it.
- **a temporary,** a value with no name, which is dead at the end of the
  statement that makes it.
- **a lent local,** the part that a lending call lends, or a compound
  assignment's target. It is the place itself, so a place is evaluated once
  however often it is read, and its loan lasts until it is dead.

A lending call, such as `items[index]` (a call of `Index.at`), makes a lent
local with a `lend` statement. The core form's `Lent` place lends for the
rest of its statement, so the builder makes the lent local dead where the
statement ends.

An operand is one of:

- `use place`, which reads the value out of the place: a copy for a type
  that copies implicitly, and a move otherwise. It names the core node it
  reads for, by which the ownership check reports a move.
- `borrow place`, read-only or `mut`, for a parameter that borrows
- a constant: unit, a literal of a built-in type, or a string literal

The type decides between a copy and a move, so the builder needs no fact
about types, and the MIR is a function of the core form alone.

### Statements

| Statement | Meaning |
|---|---|
| `place = rvalue` | Write a value to a place. |
| `place = call(callee, arguments)` | A call. The callee is the core form's: a function, a trait method with its evidence, a capability method, an intrinsic that is not a primitive operation, or a function value. An argument the source leaves out is `default`, and the callee fills it in, as DESIGN.md requires. |
| `local = lend callee(arguments)` | A call of a lending method, whose part the lent local is. |
| `place = slice slice_range(base, start, stop)` | A slice, whose result views `base`. |
| `place = template from_template(record)` | A tagged string, with its literal texts, on which the prover runs the tag's checks. |
| `place = pull cursor` | The next value of the built-in cursor of a yielding method, an `Option`. A user type's `Cursor.next` is an ordinary call. |
| `live locals`, `dead locals` | Where locals start to hold values, and where they stop: the end of a scope, of a statement, or of a loan. A jump out of scopes, such as a `break`, ends them first. |
| `assert operand` | An `assert` that can run: stop the program if the `Bool` is false. |
| `echo operand` | Record a value's debug output. |
| `provide implementations`, `provide end` | The start and the end of a `provide` block. |
| `fork start`, `fork end` | The start of each branch of a `parallel` or `concurrent` block, and the end of its last. Code generation outlines each branch, as it outlines the LIR's regions. |
| `ghost assert`, `proof` | An `assert` that cannot run, and a `proof` block, which only the prover reads. |

| Rvalue | Meaning |
|---|---|
| an operand | |
| `operation(op, operands)` | A primitive operation on built-in types. See [Primitive operations](#primitive-operations). |
| `compare(comparison, left, right)` | A comparison of two values of one built-in type. |
| `not operand` | |
| `construct(variant, fields)` | A record or a variant, with every field, in the order the fields are evaluated. A field that is a `borrow` lends its place to the value, as a yielded construct does. |
| `array(elements)` | An array literal. |
| `is_variant(place, variant)` | Whether a sum type's value holds the variant. |
| `convert(conversion, operand)` | A conversion the type checker inserted. |
| `to_any(operand, trait, evidence)` | A value as `any Trait`. |
| `copy(operand)` | A `copy()` that the compiler implements. |
| `function(path)`, `lambda(body, captures)` | A function value. |

| Terminator | Meaning |
|---|---|
| `goto block` | Jump. |
| `branch(operand, yes, no)` | Branch on a `Bool`. |
| `switch_variant(place, cases)` | Branch on a sum type's variant. |
| `each(call, part, body, after)` | A `for` loop over a call of a yielding method. `body` runs once for each part the callee yields, which the local `part` holds, and ends with `next` or a jump to `after`. |
| `next` | The end of an iteration of the enclosing `each`. |
| `yield(mode, operand, resume)` | In a lending or yielding method, give a part to the caller's loop, and continue at `resume` unless the loop has ended. |
| `return operand` | Return a value, or nothing. |
| `exit_tasks(tasks, exit)` | An early exit from `concurrent` code: end these tasks, then return or jump. |
| `unreachable` | A point the prover shows is never reached: the last arm of a `match` whose guards cover every case, or `unreachable` as written. |
| `todo` | Stop the program at a `todo`. |

Every other loop is a natural loop of jumps. Its header block carries the
loop's `invariant`, `decreases`, and `cost` clauses, its schedule (one
iteration after another, or at once for a `parallel for` or a
`concurrent for`), and, for a loop over an integer range, its counter.

`each` stays a structured terminator, unlike other loops. Code generation
inlines the yielding method and runs the body at each of its `yield`s, and
it cannot always pull a cursor instead: `Ownership.pullable` refuses
methods that yield `mut` places or that yield through themselves. The
ownership check borrows the call's receiver for the region, and the prover
reads the callee's contract for each part.

## Evaluation order

The MIR builder is the one place that decides the order of evaluation.
These are its rules:

1. **A call** evaluates an indirect callee, then its arguments in order.
   The `mut` borrows of its arguments start after the last argument is
   evaluated, so a later argument cannot mutate a place an earlier one
   borrowed.
2. **An assignment** `target = value` evaluates `value`, then the index
   keys of `target`, then stores.
3. **A compound assignment** `target op= operand` evaluates `operand`,
   then the index keys of `target`, once, into a borrow local. Then the
   operator takes the old value and its result is stored. No other code
   runs while the target holds no value.
4. **`&&`, `||`, and `==>`** evaluate their right operand only when the
   left does not decide the result.
5. **A `match`** evaluates its scrutinees in order. Each arm tests its
   patterns, then binds, then evaluates its guard, then runs its body.
6. **A constructor** evaluates its fields in the order they are written,
   then each default. A record update evaluates its base, then each update
   in order.
7. **A `for` loop** evaluates its range or its call before the first
   iteration.

SYNTAX.md and DESIGN.md state the rules that a programmer can observe.

## Primitive operations

An operation means one thing however it is written. `a + b` on `Int64`,
`a.add(b)` on `Int64`, and `intrinsic::add(a, right: b)` are the same
`operation(add, [a, b])`, and every consumer reads it the same way:

- **The prover** gives it the operation's obligations and facts: no
  overflow for `add`, a divisor that is not zero for `divide`, an amount
  below the width for a shift, the bounds of a bitwise result, and the
  IEEE 754 model of a float.
- **Code generation** checks at run time, in a build that checks, the
  operations that may fail. It lowers both spellings through one function
  already.
- **The cost** of an operation is a primitive step, which a `time` bound's
  constant absorbs, however it is written.

The core form keeps the two spellings, `Operator` and a call whose callee
is `Intrinsic`, because the type checker records the source spelling. The
MIR builder maps both to `operation`, so no consumer can tell them apart.
An intrinsic that is not a primitive operation, such as `storage_push` or a
system call, stays a call.

This gives the standard library's own arithmetic the program's checks.
The bodies of `impl Add for Int8` and the other operator traits call
`intrinsic::add`, and they run when generic code adds through a type
parameter, so a weaker check there would be a weaker check of every such
program. Rust writes its `impl Add for i32` as `self + other`, so the
operator's body is the same MIR operation as every other `+`.

## Pattern matching

The MIR builder lowers every `match`, `is`, and `let ... else` once, for
every consumer, to tests, bindings, guards, and jumps. No consumer
interprets a pattern.

A test of a variant, a literal, or a range is a primitive operation: it
has no effect, cannot fail, and always ends, so the order of these tests
cannot be observed. An `Equal_to` pattern is different: it calls the
type's `Equal.equal`, and although that call has no `uses` and ends, an
`impl` may allocate, and a cost clause can count allocations. A guard is
code, and runs only after its arm's patterns match.

So the builder may choose the order of the primitive tests, and of nothing
else:

- **It tests arms in order,** as stage0 does today: each arm's patterns,
  then its bindings, then its guard, then its body, and on a failure the
  next arm. The graph is linear in the size of the `match`.
- **It may build a decision tree** (Maranget, "Compiling Pattern Matching
  to Good Decision Trees", 2008) over the primitive tests, which tests each
  part of the value once. A call of `equal` and a guard run on exactly the
  paths where arm order runs them, and in the same order, so a cost clause
  can count them by reading the arms in order. The tree is used where it stays linear in the size of the
  `match`, and arm order elsewhere: a tree can be exponential in the
  number of columns, and the prover's queries grow with the graph, so the
  bound keeps a large `match` provable.

Because there is one builder, a better tree is faster code and smaller
queries at once, and no consumer changes. Each arm's first block records
the arm's origin, so the prover still says which arm a counterexample
takes.

## Lowering the core form

| Core form | MIR |
|---|---|
| `Compound_assign`, `Current_target` | The operand, a `lend` of the target, the operation on the old value, a store, and `end_lend` |
| `Lent`, `Temporary` | A `lend` statement, or a temporary local, with the loan ended at the end of the statement |
| `If`, `Match`, `Matches`, `let ... else`, `?` | Branches, variant switches, comparisons with literals, and calls of `equal`, with the bindings as assignments of locals (see [Pattern matching](#pattern-matching)) |
| `Operator`, a call of an intrinsic that is a primitive operation | `operation` (see [Primitive operations](#primitive-operations)) |
| `While`, `For` over a range, `For` over a cursor | A natural loop, with a counter or a `pull` at its header, and the clauses on the header |
| `For` over a call of a yielding method | `each` |
| `Parallel`, `Concurrent`, `parallel for`, `concurrent for` | Regions |
| `Task_exit`, `Return`, `Break`, `Continue` | `exit_tasks`, `return`, and jumps |
| `Lambda` | A body of its own, and a `function` rvalue |
| `Template` | A call of the tag's `from_template` that keeps the literal texts, on which the prover runs the tag's checks |
| `Slice` | A call of `slice_range` with its base borrowed, whose result views the base |
| `Record_update`, an array's `Collection_literal` | Constructions |
| `Proof`, a condition that cannot run | Ghost statements |
| `Old`, `Yielded`, `Finished` | Ghost locals, which the builder assigns at entry, at each part, and at the end |
| `Result`, `Quantified`, `Identical`, `Specification_function`, `Method_time`, `Implies`, `Map_literal` | Unchanged inside the core expressions of specifications. They do not appear in executable code. |

A range loop has a fact that the prover needs and the source does not
write: the counter is at least the start and at most the stop. The builder
writes it on the loop header, as an assumption that is ghost code.

## How each consumer reads it

### The ownership check

The check's graph of points is the MIR. Its dataflow analyses of moves and
views run on the MIR's statements, and its loans are borrow locals and the
borrows of call arguments, which end where the MIR says. The rules for
moves, views, and borrows do not change; the builder of the graph
goes away.

### The prover

The prover runs each body forward, as now, over a reducible graph in place
of a tree. At a join of blocks, each local that differs gets a fresh
symbol, so the verification condition still grows with the body and not
with its paths, as in Boogie's passive form. A loop is cut at its header:
the locals it may change are havocked there, its invariant is assumed, the
body runs once, and the invariant is shown at each back edge. One rule
covers every loop that is not an `each`, so the prover has one translation
of loops where today it has five.

A call is read by its contract, as now. An `each` is read by the yielding
method's contract for each part. A `lend` and its `end_lend` are the
lending method's contract for the part it lends and for the value it hands
back. Ghost statements are its own.

### Code generation

Code generation instantiates a definition's MIR for each instance and
lowers it to the LIR. Evaluation order, temporaries, short-circuits, and
the flow of patterns are already in the MIR, so the lowering decides only
the LIR's concerns: pointers, layout, the calling convention, drop
elaboration, the inlining of yielding and lending methods, and the
outlining of regions.

## Queries

The MIR of a definition is a query on its core form and its interface, so
it is built once and read by all three consumers. A function for
specifications only has none, since its body never runs. The MIR is
canonical: its blocks are in reverse postorder from the entry, with the
blocks that control cannot reach removed, and its locals are numbered in
the order the builder makes them, which follows the core form.

## Specifications

A specification is a core expression, of the same type as executable code.
The MIR holds executable code, so code generation and the ownership check
never read a specification, and the prover reads specifications as core
expressions and code as MIR.

A type of its own for specifications would let a type exclude `Result`,
`Old`, `Quantified`, and the other forms that only specifications have.
It is not worth its cost:

- **Most forms are shared.** A specification calls functions, applies
  operators, compares, matches, constructs, reads fields, and branches, as
  code does. A separate type would repeat each of these forms, and the type
  checker would build two trees, for about a dozen forms that only
  specifications have.
- **The MIR already separates them where it matters.** Code generation and
  the ownership check read the MIR, which has no specification forms, so
  they have no case for one.
- **Some conditions are both.** An `assert` that can run is code that the
  builder lowers and a fact the prover uses, and an executable quantifier
  in code runs as a loop. One type holds them without a conversion.

Dafny, F*, and Verus also write specifications and code in one language of
expressions, and tell them apart by mode, as Truss does with
`condition.executable` and the type checker's rules on where a
specification-only form may appear.

The prover reads a pure computation in two places: in code, as MIR, and in
a specification, as a core expression. The two must give the same term, as
PROVER.md requires of `let sorted = is_sorted(items)` and
`ensures is_sorted(items)`. Both readings call the same functions for each
operation and each callee's contract, so only the walk over the two
representations differs. An `assert` that can run is proven from the
local that the MIR computes, so it is read once.

The rule that keeps the two apart is checked twice. The type checker
rejects a specification-only form in code, and the MIR builder treats one
that reaches it as a bug in the compiler.

## Not built

The builder is built. The rest is built in this order, and each step
removes the code that it replaces:

1. **The ownership check** reads the MIR, and its own graph builder is
   removed.
2. **Code generation** lowers the MIR to the LIR, and its lowering of the
   core form is removed.
3. **The prover** runs the MIR forward, and its walk of the core form is
   removed.
4. **The core form** loses the forms that only the builder then reads,
   such as `Current_target`, and its consumers' cases for
   specification-only forms in executable code.

The prover already reads `Operator` and a call of an intrinsic that is a
primitive operation through one translation, since the core form names the
operation in both. Pattern matching as a decision tree comes after step 2,
as an improvement of the builder.
