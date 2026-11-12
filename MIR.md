# Truss MIR

This document describes the design of stage0's mid-level IR, the MIR, which
is to live in `stage0/mir/`. None of it is built yet: [Not built](#not-built)
lists the order it is built in. The MIR is a control-flow graph of each
definition's body, built from the core form that
[TYPECHECKER.md](TYPECHECKER.md) describes. The ownership check, the prover
([PROVER.md](PROVER.md)), and code generation ([CODEGEN.md](CODEGEN.md)) are
to read it in place of the core form. The MIR of a definition is a query
of the code database, which [DATABASE.md](DATABASE.md) describes.

## What the MIR is for

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

The MIR also takes from each consumer what it never needs. Code generation
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
second representation, but all three consumers read it, and it is what
makes them agree.

## What the MIR keeps

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

A place is a local followed by projections: a field of a record, a field of
a variant that a test has selected, and the element that a borrow local
holds. A constant's static data is a place too, and it is read-only.

A **borrow local** holds a borrow of a place. A lending call, such as
`items[index]` (a call of `Index.at`), makes one with a `lend` statement,
and the borrow lasts until an `end_lend` statement. The core form's
`Lent` place is a lending call whose loan ends with the statement; the MIR
builder places the `end_lend` at the end of that statement. A compound
assignment's target and a borrowed operand of a call are borrow locals in
the same way, so a place is evaluated once however often it is read.

An operand is one of:

- `copy place`, for a type that copies implicitly
- `move place`, which leaves the place without a value
- `borrow place`, read-only or `mut`, for a parameter that borrows
- a constant: a literal of a built-in type, or a string literal

The builder chooses between `copy` and `move` from the type. The ownership
check reports a `move` that is not allowed, as it does for a `Use` today.

### Statements

| Statement | Meaning |
|---|---|
| `local = rvalue` | Write a value to a local or a place. |
| `local = call(callee, arguments)` | A call. The callee is the core form's: a function, a trait method with its evidence, a capability method, an intrinsic, or a function value. An argument the source leaves out is `default`, and the callee fills it in, as DESIGN.md requires. |
| `borrow = lend callee(arguments)` | A call of a lending method, whose result is a borrow local. |
| `end_lend borrow` | The end of a borrow local's loan. For a `mut` loan, the lender's place has the lent part's final value from here on. |
| `local = pull cursor` | The next value of the built-in cursor of a yielding method, an `Option`. A user type's `Cursor.next` is an ordinary call. |
| `assert local` | An `assert` that can run: stop the program if the `Bool` local is false. |
| `echo place` | Record a value's debug output. |
| `ghost statement` | A statement that only the prover reads: an assertion or an assumption of a core expression, an assignment to a ghost local, or a call of a theorem. |
| `region(kind)`, `regions_end` | The start of a region of a `parallel` block, a `concurrent` block, or a loop whose iterations run at once, and the end of the last region. Code generation outlines each region, as it outlines the LIR's. |

| Rvalue | Meaning |
|---|---|
| an operand | |
| `operation(op, operands)` | A primitive operation on built-in types. One that may fail, such as an addition that may overflow, is checked at run time in the builds that CODEGEN.md says check it, and the prover shows that it does not fail. |
| `compare(comparison, left, right)` | A comparison of two values of one built-in type. |
| `construct(type, variant, fields)` | A record or a variant, with every field, in the order the fields are evaluated. |
| `is_variant(place, variant)` | Whether a sum type's value holds the variant. |
| `convert(conversion, operand)` | A conversion the type checker inserted. |
| `function(lambda or path, captures)` | A function value. |
| `to_any(operand, trait, evidence)` | A value as `any Trait`. |

| Terminator | Meaning |
|---|---|
| `goto block` | Jump. |
| `branch(local, yes, no)` | Branch on a `Bool`. |
| `switch_variant(place, cases, default)` | Branch on a sum type's variant. |
| `loop(header)` | Enter the natural loop at `header`. The header carries the loop's `invariant`, `decreases`, and `cost` clauses, and its schedule: one iteration after another, or at once as the regions of a `parallel for` or a `concurrent for`. |
| `each(call, pattern, body, after)` | A `for` loop over a call of a yielding method. `body` is a region that runs once for each part the callee yields, and ends with `continue` or `break`. |
| `yield(mode, operand, resume)` | In a lending or yielding method, give a part to the caller's loop, and continue at `resume` unless the loop has ended. |
| `return operand` | Return a value, or nothing. |
| `exit_tasks(tasks, exit)` | An early exit from `concurrent` code: end these tasks, then take `exit`, a `return`, a `break`, or a `continue`. |
| `unreachable` | A point the prover shows is never reached: the last arm of a `match` whose guards cover every case, or `unreachable` as written. |
| `todo` | Stop the program at a `todo`. |

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
   evaluated, so a later argument cannot mutate what an earlier one
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

## Lowering the core form

| Core form | MIR |
|---|---|
| `Compound_assign`, `Current_target` | The operand, a `lend` of the target, the operation on the old value, a store, and `end_lend` |
| `Lent`, `Temporary` | A `lend` statement, or a temporary local, with the loan ended at the end of the statement |
| `If`, `Match`, `Matches`, `let ... else`, `?` | Branches, variant switches, comparisons with literals, and calls of `equal`, with the bindings as assignments of locals |
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
borrows of call arguments, which end where the MIR says. The rules about
what is moved, viewed, and borrowed do not change; the builder of the graph
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
lending method's contract for the part it lends and for what it hands
back. Ghost statements are its own.

### Code generation

Code generation instantiates a definition's MIR for each instance and
lowers it to the LIR. Evaluation order, temporaries, short-circuits, and
the flow of patterns are already in the MIR, so the lowering decides only
what is the LIR's: pointers, layout, the calling convention, drop
elaboration, the inlining of yielding and lending methods, and the
outlining of regions.

## Queries

The MIR of a definition is a query on its core form, so it is built once
and read by all three consumers. It is canonical in the way the LIR is:
locals numbered in order of first use, blocks in reverse postorder,
nothing unused. A change that leaves a definition's MIR unchanged, such as
a renamed local, does not reach the ownership check, the prover, or code
generation.

## Open questions

- **Primitive operations and intrinsic calls.** The core form has an
  `Operator` for `+` and a call of an intrinsic for `intrinsic.add(...)`.
  The prover checks both for overflow and division by zero, but it checks
  shift amounts, models floats, and states facts about bitwise operations
  only for `Operator`. One `operation` in the MIR would give a call of an
  intrinsic the operator's checks and facts; two would keep the
  difference.
- **`match` as a decision tree.** CODEGEN.md's list of what is not built
  asks for one. The builder could make the tree once, for every consumer.
  The prover's queries would then test parts of a value in the tree's
  order, which may change what it can prove quickly.
- **A type of its own for specifications.** Keeping specifications as core
  expressions leaves `Result`, `Quantified`, and the other
  specification-only forms in the core form's executable type. A separate
  type would let the type of executable code exclude them.

## Not built

The MIR is not built. It is built in this order, and each step removes
the code that it replaces:

1. **The builder,** from the ownership check's graph builder, which
   already lowers the core form to a control-flow graph in evaluation
   order.
2. **The ownership check** reads the MIR, and its own graph builder is
   removed.
3. **Code generation** lowers the MIR to the LIR, and its lowering of the
   core form is removed.
4. **The prover** runs the MIR forward, and its walk of the core form is
   removed.
5. **The core form** loses the forms that only the builder then reads,
   such as `Current_target`, and its consumers' cases for
   specification-only forms in executable code.
