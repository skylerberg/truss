# Truss Prover

The stage0 prover takes the MIR of each body that runs ([MIR.md](MIR.md)), the
core form of its specifications and ghost code
([TYPECHECKER.md](TYPECHECKER.md)), its callees' interfaces and contracts,
and the bodies it reads as definitions. For each definition it finds every
*obligation*, a fact that must hold for the program's promises to be kept,
builds one solver query for each, runs a pinned solver within a fixed number
of steps, and reports each obligation it could not prove, with a
counterexample. Its queries run on the code database
([DATABASE.md](DATABASE.md)).

It does not type-check, resolve names, or read syntax trees, and it infers
no specifications.

## Structure

```text
core forms, interfaces, contracts
        │
        ▼
a body, run forward ──▶ obligations ──▶ pruned queries ──▶ solver ──▶ answers
                             ▲                                          │
                    termination, costs                                  ▼
                                                 counterexample ──▶ diagnostics
```

A body is run forward with every value a term of the logic, and each fact
that must hold where it is reached becomes an obligation, with the facts
gathered before it. Each obligation is cut down to the facts it can use,
written canonically, and given to the solver.

**One walk reads Truss and makes the verification conditions.** Boogie and
Why3 put a proof program between the language and the logic, at the cost of
a second representation of every body that only the prover would read. The
MIR ([MIR.md](MIR.md)) is a second representation too, but every consumer
reads it.

**Early cutoff happens twice.** A definition's obligations are one query, and
each obligation's answer is kept under the hash of its query's text. So a
definition that read nothing that changed keeps its obligations, and one
whose obligations are made again asks the solver only about queries whose
text changed.

## Obligations

| Obligation | Where |
|---|---|
| An index or slice is in bounds | Each index, through the `requires` of the `impl` of `Index` it reaches |
| An operation does not overflow or divide by zero | Each such operation on a built-in integer, including the intrinsic ones an `impl` of `Add` calls |
| A shift amount is below the width | Each `<<` and `>>` |
| `unreachable` is never reached | Each, including those after guards |
| A call's `requires` holds | Each call, including theorems and calls in specifications |
| An `ensures` holds | Each way a function returns, and for a lending or yielding method each `yield` and each end |
| A type's invariant holds | Wherever SPECIFICATION.md says other code could see the value |
| A loop invariant and a loop's `cost` hold | On entry and at the end of each iteration |
| A callback's `requires` holds | Each call through, and each function passed for, a parameter whose type has a `requires` |
| Recursion and loops end | Each call in a cycle, and each loop, in a function with a `time` clause |
| A cost clause holds | Each function with one |
| A law holds | Each law of each trait an `impl` implements by hand |
| An `impl` keeps its trait's contract | Each method of an `impl` |
| `assert` holds | Each `assert` in a theorem or a proof |
| A specification is well defined | Each call, index, and division in a contract, a loop's clauses, an invariant, and a potential |
| The type checker's and ownership check's obligations | An `Integer` that fits; two indexes or ranges that are disjoint |

## The logic

### Values are values

Mutable value semantics keeps the logic small. No two names change the same
memory, so the prover has no heap, no aliasing, and no permissions, which
verifiers for Rust and for languages with references need.

- **Every value is a term,** and nothing about it depends on where it is
  stored.
- **A `mut` parameter is two values,** on entry and on return. A call with
  `mut items` replaces `items` with a fresh value that the callee's `ensures`
  relates to the old one.
- **A view is the value it views,** since the original is frozen while it is
  used.
- **Moves, drops, and copies are invisible,** since a moved value is never
  used again and a copy equals its original.
- **Capability calls return fresh values.** The prover never models an
  implementation's state: a call gives a value of which only the method's
  `ensures` is known. So no proof assumes that state stays the same between
  calls, and concurrent tasks cannot invalidate one.
- **`parallel` and `concurrent` branches are read one after another,** since
  they change disjoint places.

### Types as sorts

| Truss | In the solver |
|---|---|
| Built-in integers, `Integer` | The integers, with a built-in type's range as a fact about each value of it |
| `Bool` | Booleans |
| `Character` | Integers up to `0x10FFFF` that are not surrogates |
| `Float32`, `Float64` | The SMT-LIB floating-point theory, bit for bit |
| Records and sum types whose fields are visible | Algebraic datatypes |
| Opaque types from another package, types defined as `todo`, the mathematical collections, type parameters, `any` types, function types | Uninterpreted sorts |

- **Integers are mathematical integers,** and each operation on a built-in
  integer is exact with an obligation that the result is in range, as in
  Dafny and Verus.
- **Bitwise operations are known by a few facts,** such as that `a & b` is at
  most each unsigned operand, which proves the bounds most bit manipulation
  needs. An `assert ... by bit_vector` is proven by bit-blasting, in a query
  of its own, as with Verus's `by (bit_vector)`.
- **An opaque type from another package is a sort** known by its methods and
  model, which keeps `opaque` meaningful to proofs.
- **Each intrinsic means what the compiler makes it do,** which is part of
  the [trusted base](#the-trusted-base).

### Mathematical collections

`Sequence`, `FiniteSet`, `FiniteMap`, and `Multiset` are types of
`standard::specification` whose operations are pure functions with contracts
written in Truss, so the trusted base holds only those contracts, not axioms
in the prover. The solver's own theory of sequences is not used: its
behavior differs between solvers and versions, and it is a common source of
unstable proofs. Extensionality is the one axiom, since a contract cannot
state that two sequences with the same elements are identical.

### Equality

Structural equality is the solver's equality, which it substitutes through
everywhere. Every other `==`, and each ordering, is a function of its
operands, with the laws of `Equal` and `Ordered` as facts.

### Generic code is proven once

A generic function is proven once, for every type argument, as Dafny and
Verus prove generic code. Its type parameters are sorts the solver knows
nothing about, and each bound brings its trait's methods with their
contracts and laws, so generic code may use a trait's contracts but not its
implementations.

Code generic over an integer trait is the exception: it is proven once for
each built-in type that implements the trait. The traits are sealed, so
those are every instance there can be, and one proof over an unknown sort
would need a symbolic width, which the bit-vector theory does not have.

## Functions in the logic

[Bodies and contracts in proofs](SPECIFICATION.md#bodies-and-contracts-in-proofs)
decides when a body is a definition. In the solver:

- **A pure function with a `time` clause is a function symbol,** so
  `let sorted = is_sorted(items)` and `ensures is_sorted(items)` are the same
  term. Its termination makes this sound.
- **Any other function is known by its contract,** never its body, and gives
  a fresh result at each call.
- **A method of a trait or an `impl` is unfolded at each call,** since its
  contract is the trait's.
- **Recursive definitions unfold once per use,** as fuel does in Dafny. A
  proof that needs more calls a theorem or asserts the steps.
- **A lambda is proven where it is written,** and its assumptions hold only
  inside it, since it may run any number of times, including none. A lambda
  passed for a parameter whose type has a `requires` assumes that `requires`
  of its arguments, so in `indices.map(fn(i) { values[i] })` the lambda knows
  that `i` is one of `indices`.

Callers' proofs depend on a function's contract, not its body, so editing
`is_sorted`'s body re-proves only `is_sorted`.

## Verification conditions

**A body is run forward in passive form** (Flanagan and Saxe, 2001): every
fact is guarded by its path's condition, and where paths join, each local
that differs gets a fresh symbol, so a body's queries grow with the body, not
with its number of paths. A body that runs is run from its MIR, block by
block in reverse postorder, so its order of evaluation and its scopes are the
ones code generation compiles. Each computation it names, such as a call or
a constructor, is read through the same functions as in a specification,
given its operands' values, so code and specification give the same term.
A specification, a proof, a `proof` block, and a quantifier's body are
formulas, which the type checker keeps free of loops, assignments, and early
exits, and are read from the core form.

- **A call** asserts each `requires`, gives each `mut` argument a fresh
  value, keeping its old one for `old`, and assumes each `ensures` and the
  invariants of the result and each `mut` argument.
- **A `while` loop is cut at its head.** Its invariants are asserted on
  entry, every place the body may change gets a fresh value, the invariants
  are assumed, the body runs once, and the invariants are asserted again.
- **A `for` loop** uses the contract of the `each` it calls, with a ghost
  `yielded` of the parts earlier iterations received. A range of integers is
  the one loop the prover knows itself.
- **A lending call** gives the statement the part, about which the clauses
  that mention `result` are known, and afterward assumes the method's end
  clauses. So `mut grid.cell(position).visit()` is known to change exactly
  one cell.
- **A type's validity** is its invariants and its fields' validity, assumed
  of each parameter on entry and of each call's result, and asserted wherever
  an invariant must hold. A private `mut self` method neither assumes nor
  asserts it of `self`, so it can be a step of an update.
- **Code the prover cannot read soundly stops the walk,** and none of the
  definition's obligations count as proven: an obligation is never assumed
  because the code around it could not be read.

**Proofs** follow the same walk. A theorem is proven like a function that
returns nothing, and a call to one assumes its `ensures`. A `proof` block is
walked where it is written and never compiled. A law is a fact wherever the
trait's methods are used on a bounded parameter or a type whose `impl` proved
the law. A replacement of a provided method proves that its result equals
the provided body.

## Queries

**Each obligation gets a query of its own:** the facts on the paths that
reach it, the obligations before it, assumed since each has its own query,
the facts of the functions and types it mentions, and its negation. A small
query is answered quickly and the same way every time, where one query for a
whole function can fail because of an unrelated part of it, which is why
Dafny's `--isolate-assertions` exists.

**A query holds only the facts that can matter.** Starting from the
obligation's symbols, each fact that mentions a kept symbol is kept, until
nothing more is added. Dropping a fact is always sound, and a change to a
function no kept fact mentions leaves the query's text, and its answer,
unchanged.

**The prover chooses triggers,** since Truss has no syntax for them: the
smallest applications that name every bound name, leaving out those that
would make a matching loop.

**A query's text is canonical,** so its hash can be its key. Every symbol is
named by its first appearance in a fixed walk, never by its Truss name, so
renaming or moving a definition finds its callers' proofs done, and the
answer depends only on meaning, since solvers can change their answers when
only names change.

**The solver is deterministic:**

- **Z3, pinned.** Another version is refused, since its answers could
  differ, and the version is part of every answer's key.
- **A fixed limit in steps.** Each query runs with the same `rlimit`, which
  counts work, not time, so a slow machine never fails a proof a fast one
  passes. The limit does not grow with a query's size, which would make an
  answer depend on facts unrelated to its goal.
- **One process per query,** with a fixed random seed, since a solver that
  answered earlier queries carries state that can change later answers.

## Termination

Each package's call graph is a query of its own, since a cycle can only be
seen across definitions. Its edges are every way a function can reach
another (see [Termination](SPECIFICATION.md#termination)), including using
an `impl` where a bound needs one. Each edge in a cycle through a function
with a `time` clause is an obligation that the callee's measure is smaller
than the caller's. Parts are ordered by rank, as Dafny orders its datatypes,
so recursion over a tree whose children are a list ends with no
`decreases`.

## Costs

**Costs are ghost counters.** The prover adds a ghost `Integer` counter on
each path for each resource with a cost clause, so costs are proven by the
same verification conditions as everything else. `time` counts one for each
call and each loop iteration, plus each callee's own bound. A callee's cost
is its cost clause's bound, never its body's.

**Exact bounds add exactly,** so `cost calls(visit) == items.length()`
follows from a loop that calls `visit` once per element.

**Asymptotic bounds are proven with fixed constants.** `O(f)` promises a cost
at most `c * f + d`, and each callee has unknown constants of its own. Truss
removes them in two steps:

1. **Count in units.** Each callee's `O(g)` counts as `g + 1`. Every callee's
   real cost is at most `C` times its counted cost, for `C` the largest of
   their constants, so `counted <= c' * f + d'` proves `O(f)`.
2. **Use fixed constants.** With no unknown left, every bound is proven with
   `c' = 2^17` and `d' = 2^16`.

A recursive call then adds `c' * f + d'` with its arguments, which is sound
by the termination measure. So binary search's
`1 + c' * log(n / 2) + d' <= c' * log(n) + d'` holds because
`log(n / 2) == log(n) - 1`, which is exact because of how SPECIFICATION.md
rounds `log`.

**A loop's cost per iteration is inferred, then proven.** A wrong guess fails
a proof but never makes one. When none is found, the error asks for a `cost`
clause on the loop.

**Amortized bounds are proven with potentials.** A method with
`cost amortized time O(f)` proves that its counted cost, plus the potential
of its result and `mut` parameters afterward, minus their potential on
entry, is within the bound. Potentials never go below zero, which is proven
for each type from its invariants.

## Running code while proving

Some obligations are about values known when compiling, which no solver can
decide by reasoning, such as a regular expression's validity. The prover
runs a pure call whose arguments are all literals, and a tag's check of a
template's literal text, and takes the result as a fact.

- **The prover does not depend on code generation.** The evaluator is an
  oracle, like the solver, which the driver supplies.
- **A run is done again when its code changes,** keyed by code generation's
  key of everything it can reach. Without this, a callee's new body would
  leave callers proven by its old result, which would prove a false
  `ensures`.
- **This trusts compiled code,** as Lean's `native_decide` does, and each
  obligation's state says whether its proof does, so a reviewer can see which
  proofs rely on it.

## Holes

A `todo` in a theorem or a proof is the one gap a proof may have. It is
recorded as a hole, not a failure, and a build refuses a program that can
reach one. A hole ends its path, as `assume false` would, which is sound
because a hole is never in a built program. A `todo` in code also ends its
path, so contracts can be written and proven before the code.

## Diagnostics

Each obligation not proven is an error with a code for its kind, and:

- **The fact, in Truss, at the operation:** "`count + 1` may overflow `UInt8`."
- **Whether the solver found a counterexample or ran out of steps,** which
  means the fact may be true but needs help.
- **The values** of the parameters and locals in the counterexample, written
  as Truss, and the branches its path takes, so an agent can turn them into a
  failing test.
- **A fix that moves the condition up as a `requires`,** where it names only
  the parameters, constants, and literals. A fix that would change the code's
  semantics, such as a checked operation, is named, not offered.

## Incremental work

| Edit | Solved again |
|---|---|
| A function's body | The queries whose paths pass through the change |
| The code a run reaches | The run, and the outcomes that used it |
| A function's `ensures` or `requires` | Queries that kept it after pruning, and for `requires` each caller's obligation |
| A body that is a definition | Queries that unfolded it |
| A type's invariant, a trait's law | Queries that used it, and each `impl`'s proof of the law |
| A name of a local or definition | Nothing, since queries number their names |
| A new `impl` | Its own obligations only |
| A new solver version, or a new limit | Everything, once |

## The trusted base

A proof is as trustworthy as:

- the solver, and the translation into its logic
- the prover's own facts: extensionality, the definitions of `log` and
  `power`, the facts about bitwise operations, and a derived `Equal`'s
  meaning
- the contracts of `standard::specification`, which define the mathematical
  collections and are not proven
- the meanings of the intrinsics, their declared costs, and the C library's
  table
- the standard library's contracts whose bodies end in an intrinsic the
  prover knows only by its type
- compiled code, for the checks that are run

Every test build's run-time checks test the trusted base against real
executions, and `stage0/tools/proof_fuzz` mutates examples to look for a
proof the prover should not have made.

## Interfaces to other stages

- **The type checker and the ownership check** give each core form with the
  obligations they create.
- **Code generation** runs checks for the prover.
- **The build** refuses a package with an obligation not proven, and a
  program whose `main` reaches a hole. A dependency's proofs are the
  program's too, since a release build omits the checks they replace.

## Not built

- Contracts for the intrinsic module's system calls.
- Proofs for a 32-bit `USize`. The prover reads `USize` and `ISize` as 64
  bits in every package, and code generation builds only for 64-bit targets.
- Facts under an assumed quantifier.
- `span` as a resource.
