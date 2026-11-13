# Truss MIR

The MIR is stage0's mid-level IR: a control-flow graph of each definition's
body, built from the core form of [TYPECHECKER.md](TYPECHECKER.md). The
ownership check reads it, and the prover ([PROVER.md](PROVER.md)) and code
generation ([CODEGEN.md](CODEGEN.md)) are to read it in place of the core
form (see [Not built](#not-built)).

## Motivation

The core form is a tree close to the source, with compound assignment, five
kinds of loop, lending calls as places, and specifications in the same type
as code. Each consumer that lowers it on its own decides separately the
order of evaluation, where a temporary lives and a loan ends, and how
`match`, `?`, and early exits flow. When two consumers decide differently,
the program checked is not the program that runs: the prover proves facts
about code that is not compiled, and the ownership check accepts code whose
compiled order is a use after move. The MIR makes each decision once, in its
builder. Rust's borrow checker, code generation, and verifiers share its MIR
for the same reason.

```text
syntax tree ──▶ type checker ──▶ core form ──▶ MIR builder ──▶ MIR
                                    │                          │
                              exhaustiveness   ┌───────────────┼─────────────────┐
                                             ▼                 ▼                 ▼
                                      ownership check        prover     monomorphize ──▶ LIR ──▶ C
```

The exhaustiveness check reads the core form, because it needs patterns as
written.

## Contents

| The MIR has | Because |
|---|---|
| Generic bodies, before monomorphization | The prover proves a generic function once, and code generation substitutes type arguments per instance. |
| Places and values, not memory | The prover models values, and the ownership check has ruled out aliasing. Pointers and layout are the LIR's. |
| Explicit temporaries, in evaluation order | The order is the order of statements. |
| Temporaries that hold a borrowed place | `items[next()] += 5` lends `items[...]` once and writes through the loan, which the core form cannot hold across statements. |
| Specifications as core expressions, and ghost statements | Only the prover reads them; the others skip them. |

| The MIR leaves out | Where it is |
|---|---|
| Drops | Code generation elaborates them from the MIR's moves. |
| Instances, layout, the calling convention | The LIR |
| Unwinding | Nothing unwinds, so a call is a statement, not a terminator. |
| Patterns as written | The core form |

- **The graph is reducible.** A `while` loop is a natural loop, and Truss has
  no `goto`.
- **A `for` loop is a structured terminator** whose body is a region, because
  each consumer needs the body as a unit: code generation runs it at each
  `yield` or as a task, the ownership check lends the collection for it, and
  the prover reads the yielding method's contract for each part.
- **A jump out of scopes ends what it leaves:** loans, bindings,
  temporaries, and a `provide` block.

## Evaluation order

The builder is the one place that decides the order of evaluation. Each
operand is held where it is evaluated, so a later operand cannot change what
an earlier one read. The `mut` borrows of a call's arguments start after the
last argument is evaluated, so a later argument cannot change a place an
earlier one borrowed. A compound assignment evaluates its operand before its
target, so no other code runs while the target holds no value.

## Primitive operations

`a + b` on `Int64`, `a.add(b)`, and `intrinsic::add(a, right: b)` are one
operation in the MIR, so no consumer can tell them apart. The standard
library's own arithmetic, whose operator `impl`s call intrinsics, then gets
the program's checks, and generic code that adds through a type parameter is
checked as strongly as code on `Int64`.

## Pattern matching

The builder lowers every `match`, `is`, and `let ... else` once, to tests,
bindings, guards, and jumps. It may reorder tests of variants, literals, and
ranges, which have no effect, and nothing else: an `Equal_to` pattern calls
`equal`, which may allocate, and a guard is code.

Stage0 tests arms in order. A decision tree (Maranget, 2008) would test each
part of the value once, and is to be used only where it stays linear, since
a tree can be exponential and the prover's queries grow with the graph.

## Specifications

A specification is a core expression, of the same type as code. Most forms
are shared, the MIR already keeps specifications from the consumers that do
not read them, and some conditions, such as an `assert`, are both. Dafny and
Verus also write both in one language of expressions. The prover reads a
pure computation as MIR in code and as a core expression in a
specification, and both readings call the same functions, so they give the
same term.

## Not built

The builder is built, and the ownership check reads the MIR. The rest comes
in this order, each step removing the code it replaces:

1. Code generation lowers the MIR to the LIR, and its lowering of the core
   form is removed.
2. The prover runs the MIR forward, and its walk of the core form is
   removed.
3. The core form loses the forms that only the builder then reads.

Pattern matching as a decision tree comes after step 1.
