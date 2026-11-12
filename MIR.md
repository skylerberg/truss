# Truss MIR

This document describes stage0's mid-level IR, the MIR, in `stage0/mir/`: a
control-flow graph of each definition's body, built from the core form of
[TYPECHECKER.md](TYPECHECKER.md). The ownership check reads it, and the
prover ([PROVER.md](PROVER.md)) and code generation
([CODEGEN.md](CODEGEN.md)) are to read it in place of the core form (see
[Not built](#not-built)). A definition's MIR is a query of the code database
([DATABASE.md](DATABASE.md)).

## Motivation

The core form is a tree close to the source, with compound assignment, five
kinds of loop, lending calls as places, and specifications in the same type
as code. Each consumer lowering it on its own decides separately the order of
evaluation, where a temporary lives and a borrow ends, and how `match`, `?`,
and early exits flow. When two decide differently, the program checked is not
the program that runs: the prover proves facts about code that is not
compiled, and the ownership check accepts code whose compiled order is a use
after move. The MIR makes each decision once, in its builder, and spares each
consumer the forms it never reads. Rust's borrow checker, code generation,
and verifiers share its MIR for the same reason.

```text
syntax tree ──▶ type checker ──▶ core form ──▶ MIR builder ──▶ MIR
                                    │                          │
                              exhaustiveness   ┌───────────────┼─────────────────┐
                                             ▼                 ▼                 ▼
                                      ownership check        prover     monomorphize ──▶ LIR ──▶ C
```

The exhaustiveness check reads the core form, because it needs patterns as
written. PROVER.md explains why the prover has no proof program of its own;
the MIR is a second representation too, but all three consumers read it,
which is what makes them agree.

## Contents

| The MIR has | Because |
|---|---|
| Generic bodies, before monomorphization | The prover proves a generic function once, and code generation substitutes type arguments per instance. |
| Places and values, not memory | The prover models values, and the ownership check has ruled out aliasing. Pointers and layout are the LIR's. |
| Explicit temporaries, in evaluation order | The order is the order of statements. |
| Temporaries that hold a borrowed place | `items[next()] += 5` lends `items[...]` once and writes through the loan, which the core form cannot hold across statements. |
| Origins on every statement | A diagnostic finds its source text. |
| Specifications as core expressions, and ghost statements | Only the prover reads them; the others skip them. |

| The MIR leaves out | Where it is |
|---|---|
| Drops | Code generation elaborates them from the MIR's moves. |
| Instances, layout, the calling convention | The LIR |
| Unwinding | Nothing unwinds, so a call is a statement, not a terminator. |
| Patterns as written | The core form |

The control-flow graph is reducible: a `while` loop is a natural loop, a
`for` loop is a structured terminator whose body is a region, and Truss has no
`goto`. A local bound `Read` or `mut` is the place it was
bound to, not a copy, and a lent local is the place itself, so a place is
evaluated once however often it is read. Whether a `use` copies or moves is
decided by the type, so the MIR is a function of the core form alone.

**A `for` loop is a structured terminator,** over a yielding call, an integer
range, or a cursor, carrying its clauses and its schedule, because each
consumer needs the body as a region: code generation inlines a yielding method
and runs the body at each `yield`, which it cannot always replace with a
cursor, splits a `parallel for` over a range into chunks, and runs each
iteration of a `concurrent for` as a task; the ownership check borrows what the
loop iterates over for the body; and the prover reads a yielding method's
contract for each part. A `while` loop is a natural loop whose header carries
its clauses.

**A jump out of scopes ends what it leaves:** the loans, the bindings, the
statements' temporaries, and a `provide` block. A `return` leaves every scope
after its value is held in a local no scope ends, so a consumer drops owned
values where the MIR says they end.

## Evaluation order

The builder is the one place that decides the order of evaluation. Each
operand of an operation, but a constant or a `mut` borrow, is held where it is
evaluated, so a later operand cannot change what an earlier one read. A `mut`
borrow starts where the operation runs: the `mut` borrows of a call's
arguments start after the last argument is evaluated, so a later argument
cannot mutate a place an earlier one borrowed. A compound assignment
evaluates its operand, then the target's index keys once into a borrow local,
so no other code runs while the target holds no value. A `match` tests each
arm's patterns, then binds, then runs its guard. The rules a programmer can
observe are SPECIFICATION.md's.

## Primitive operations

`a + b` on `Int64`, `a.add(b)`, and `intrinsic::add(a, right: b)` are one
`operation(add, ...)`. The core form keeps both spellings, because the type
checker records the source, and the builder maps both to one operation, so no
consumer can tell them apart. The prover gives it the same obligations, code
generation the same check, and the cost the same step. So the standard
library's own arithmetic, whose operator `impl`s call intrinsics, gets the
program's checks, and generic code that adds through a type parameter is
checked as strongly as code on `Int64`.

## Pattern matching

The builder lowers every `match`, `is`, and `let ... else` once, to tests,
bindings, guards, and jumps. A test of a variant, a literal, or a range has no
effect, cannot fail, and ends, so the builder may choose the order of those
tests and of nothing else: an `Equal_to` pattern calls `equal`, which may
allocate, and a guard is code.

Stage0 tests arms in order, which is linear in the size of the `match`. A
decision tree (Maranget, 2008) tests each part of the value once, and runs a
call of `equal` and a guard on exactly the paths arm order does, so a cost
clause can still count them by reading the arms. It is to be used only where
it stays linear, since a tree can be exponential and the prover's queries grow
with the graph. One builder means a better tree is faster code and smaller
queries at once.

## How each consumer reads it

- **The ownership check** builds its graph of points from the MIR's
  statements, and its loans are the MIR's. An element of a `List`, `Slice`,
  or `Array` is a place of its own, so lending one lends no part of the
  collection.
- **The prover** is to run each body forward over the graph. At a join, each
  local that differs gets a fresh symbol, so the verification condition grows
  with the body, not its paths. A `while` loop is cut at its header and a
  `for` loop at its terminator, whose iteration adds only facts: a range's
  element lies in the range, and a part meets its callee's contract. That
  gives one translation of loops where the core form has five.
- **Code generation** is to instantiate each definition's MIR per instance and
  lower it to the LIR, deciding only the LIR's concerns: pointers, layout, the
  calling convention, drops, inlining of yielding and lending methods, and
  outlining of regions.

The MIR is canonical: blocks in reverse postorder from the entry, with
unreachable blocks removed, and locals numbered in the order the builder makes
them. A function for specifications only has none.

## Specifications

A specification is a core expression, of the same type as code. A type of its
own would let a type exclude `Result`, `Old`, and the other forms that only
specifications have, but most forms are shared, the MIR already keeps
specifications from the consumers that do not read them, and some conditions,
such as an `assert` that can run, are both. Dafny and Verus also write both
in one language of expressions.

The prover reads a pure computation as MIR in code and as a core expression
in a specification, and the two must give the same term, so both readings
call the same functions for each operation and callee contract. The type
checker rejects a specification-only form in code, and the builder treats one
that reaches it as a compiler bug.

## Not built

The builder is built, and the ownership check reads the MIR. The rest comes in
this order, each step removing the code it replaces:

1. **Code generation** lowers the MIR to the LIR, and its lowering of the core
   form is removed.
2. **The prover** runs the MIR forward, and its walk of the core form is
   removed.
3. **The core form** loses the forms that only the builder then reads, such as
   `Current_target`, and its consumers' cases for specification-only forms in
   code.

Pattern matching as a decision tree comes after step 1.
