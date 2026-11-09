# Truss Prover

This document designs stage0's prover: everything between the type checker's
checked forms and the knowledge that every promise a program makes holds. It
follows the decisions in [DESIGN.md](DESIGN.md) and [SYNTAX.md](SYNTAX.md),
reads what [TYPECHECKER.md](TYPECHECKER.md) produces, and states what
[CODEGEN.md](CODEGEN.md) relies on. It is being built in
[`stage0/prover/`](stage0/prover); [What is built](#what-is-built) says how
far it has come, and `truss prove DIRECTORY` runs it over a package.

## What the prover does

The prover takes the checked form of each definition, the interfaces and
contracts of what it calls, and the bodies it reads as definitions. For each
definition it finds every *obligation*, a fact that must hold for the
program's promises to be kept, builds one solver query for each, runs a
pinned solver on it within a fixed number of steps, and reports each
obligation it could not prove.

The prover:

- finds the obligations of every function, method, `impl`, type, theorem,
  law, and test: the operations that could fail, the `requires` of every
  call, every `ensures`, invariant, law, and cost clause, termination, and
  the obligations the type checker recorded
- translates Truss values, types, and functions into the logic of an SMT
  solver
- builds a verification condition for each obligation from the paths that
  reach it, and turns it into a canonical query whose hash is its cache key
- checks termination over each package's call graph, and proves cost
  bounds by counting
- evaluates calls whose arguments are all known by running compiled code,
  which is how a tagged template's check is proven
- reports what it could not prove, with the path, values that break it,
  and a fix where one is exact

It does not:

- type-check, resolve names, or look at the syntax tree beyond the spans
  that diagnostics point at. Everything it needs is in the checked form.
- infer specifications. Loop invariants, measures, and contracts are
  written; the few loops whose facts are worked out alone get them from the
  contracts of the methods they call (see [Loops](#loops)).
- decide whether a test may run. Tests run as soon as the code
  type-checks, with run-time checks of every operation that could fail (see
  DESIGN.md, "Tests do not wait for proofs"). Only builds of programs wait
  for the prover.

## Structure

```text
checked forms, interfaces, contracts
        │
        ▼
     Paths ──▶ Obligations ──▶ Vc ──▶ Prune ──▶ Query ──▶ Solver ──▶ results
        ▲            ▲                                       │
   Meaning, Encode   Termination, Costs                      ▼
                                                     Counterexample ──▶ diagnostics
```

| OCaml module | Job |
|---|---|
| `Logic` | The solver's terms and sorts, and printing them as SMT-LIB |
| `Encode` | Truss types as sorts, and Truss values and operations as terms |
| `Meaning` | Which functions are definitions and which are contracts, and the axioms each gives |
| `Paths` | A checked body as a proof program: assignments, `assume`, `assert`, and branches |
| `Obligations` | Every obligation of a definition, each with its kind and position |
| `Vc` | Verification conditions from proof programs, by weakest preconditions |
| `Triggers` | The patterns that let the solver use each quantified fact |
| `Termination` | The package's call graph, its cycles, and the measure each call must decrease |
| `Costs` | Counters for each resource, and the obligations of cost clauses |
| `Prune` | The facts each query needs, and no others |
| `Query` | A query's canonical text, its hash, and its cached result |
| `Solver` | Running the pinned solver on one query, within its limit |
| `Evaluate` | Running compiled code on known arguments |
| `Counterexample` | The solver's model as Truss values and the path it takes |
| `Prover` | The entry point, as queries over the definitions of a build |

Each is its own dune library, as in the type checker. The prover depends on
`Types` and `Checked` but not on the type checker itself, as TYPECHECKER.md
intends.

### One definition at a time, one obligation at a time

The prover works as the type checker does, through queries with traces (see
TYPECHECKER.md, "One definition at a time, through queries"), and goes one
step further:

- **Proving a definition is a query** that reads its checked form and,
  through the environment, the interfaces, contracts, definitions,
  invariants, and laws its obligations mention. Each is recorded in its
  trace.
- **Each obligation is a solver query of its own,** whose result is cached
  under the hash of its canonical text (see [Queries](#queries)). Editing
  one statement changes the queries of the obligations whose paths pass
  through it, and leaves every other query's text, and so its result,
  exactly as it was.
- **Early cutoff happens twice.** A definition whose obligations come out
  the same needs no solving. A definition whose verification conditions
  were rebuilt solves only the queries whose text changed.

## Obligations

Every fact the prover must show, and where it comes from:

| Obligation | Where |
|---|---|
| An index or slice is in bounds | Each `items[i]` and `items[a..b]`, through the `requires` of the `impl` of `Index` the call reaches |
| An operation does not overflow | Each `+`, `-`, `*`, negation, and conversion on a built-in integer |
| A division has a nonzero divisor, and is not the least value over `-1` | Each `/` and `%` on a built-in integer |
| A shift amount is less than the width | Each `<<` and `>>` |
| `unreachable` is never reached | Each `unreachable`, including the ones after guards that the type checker added |
| A call's `requires` holds | Each call, including calls to theorems in proofs and calls in specifications |
| An `ensures` holds | Each way a function returns, and for a lending or yielding method, each `yield` and each way it ends |
| A type's invariant holds | Each value built or updated with `with`, each argument and returned value, each `mut` parameter when its function ends, and each `yield` where a method may end |
| A loop invariant holds | On entry to the loop, and at the end of each iteration |
| A loop's `cost` holds | On entry to the loop, and at the end of each iteration |
| A callback's `requires` holds | Each call through a function-typed parameter whose type has a `requires` |
| A function passed as a callback accepts what it is promised | Each named function passed where a parameter's type has a `requires`: that `requires` implies the function's own |
| Recursion and loops end | Each call in a cycle of the call graph, and each loop, in a function with a `time` clause |
| A cost clause holds | Each function with one (see [Costs](#costs)) |
| A law holds | Each law of each trait an `impl` implements by hand |
| An `impl` keeps its trait's contract | Each method of an `impl` with clauses of its own |
| A replacement gives the provided result | Each method that replaces a provided one |
| `assert` holds | Each `assert` in a theorem or a proof |
| A specification is well defined | Each call's `requires`, index, and division inside a specification |
| An `Integer` fits where a built-in integer is expected | Recorded by the type checker |
| Two indexes or ranges do not overlap | Recorded by the type checker |
| A function value's costs imply the expected costs | Recorded by the type checker |
| Map literal keys are distinct | Each map literal |

An obligation names its kind, its definition, and its position within the
definition, as every result does. A test's obligations are proven like any
function's; that its run checks them too changes nothing here.

## The logic

### Values are values

Mutable value semantics is what keeps the logic small. No two names can
change the same memory, so the prover has no heap, no aliasing, and no
permissions to track, unlike verifiers for Rust (Prusti's permissions,
Creusot's prophecies) or for languages with references (Dafny's `modifies`
and `reads` clauses):

- **Every Truss value is a term.** A record is a term built from its
  fields, a list is a term whose model is a sequence, and nothing about a
  value depends on where it is stored.
- **A `mut` parameter is two values,** the one on entry and the one on
  return, which `old(...)` and the parameter's name stand for in
  `ensures`. A call with `mut items` replaces `items` with a fresh value
  that the callee's `ensures` relate to the old one.
- **A view is the value it views.** The original is frozen while the view
  is used, so a slice is a term computed from the list, and nothing can
  make the two disagree.
- **Moves, drops, and copies are invisible.** A moved value is never used
  again, and a copy equals its original, so ownership adds nothing to a
  proof.
- **Capability calls return fresh values.** The prover never models an
  implementation's state. A call to `Clock.now()` gives a value about which
  only the capability method's `ensures` is known, so two calls may give
  different results. After `provide mut files { ... }`, `files` holds a
  fresh value of its type that meets its type's invariant.
- **A call that returns `Never` ends its path.** `Panic.crash` and calls to
  functions that never return are followed by nothing.
- **`parallel` branches run in order,** as DESIGN.md allows: the type
  checker has shown that they touch disjoint places, so any order gives
  the same result.

### Types as sorts

| Truss | In the solver |
|---|---|
| Built-in integers, `Integer` | The integers, with the range of a built-in type as a fact about each value of it |
| `Bool` | Booleans |
| `Character` | Integers up to `0x10FFFF`, without the surrogates |
| `Float32`, `Float64` | The SMT-LIB floating-point theory, bit for bit |
| `Unit` and records with no fields | Left out |
| Records and sum types whose fields are visible | Algebraic datatypes, with type parameters when generic |
| Opaque types from another package, and types defined as `todo` | Uninterpreted sorts, known through their methods and their model |
| `Array[Element, count]` | A sequence of length `count` |
| `Sequence`, `FiniteSet`, `FiniteMap`, `Multiset` | Sorts of the prover's own, with the axioms below |
| Type parameters | Uninterpreted sorts |
| `any Trait` | An uninterpreted sort for each trait and set of associated types |
| Function types | An uninterpreted sort for each arity, with an `apply` function |
| `Never` | No values |

- **Integers are mathematical integers.** Each value of a built-in integer
  type comes with its range as a fact, and each operation on one becomes
  an exact operation and an obligation that the result is in range, as in
  Dafny and Verus. `wrapping_add` and its siblings are defined with
  remainders, and the checked and saturating ones with `if`.
- **Bitwise operations get a second encoding.** On integers, `&`, `|`, `^`,
  `~`, and shifts are functions the solver knows only by a few facts, such
  as `0 <= a & b <= a` for unsigned values and shifts by a literal as
  multiplication by a power of two. That proves the bounds most bit
  twiddling needs. When a query that mentions a bitwise operation is not
  proven that way, and every integer in it is of a built-in type, the
  prover tries it once more with every integer as a bit-vector of its
  width, where the solver decides such facts exactly. Verus asks for this
  by hand with `by (bit_vector)`; Truss tries both, always in the same
  order, and caches both answers.
- **Floats follow IEEE 754 exactly,** as DESIGN.md requires, through the
  solver's floating-point theory. `==` on floats is `fp.eq` or both NaN,
  and `<` puts NaN last, which is the lawful comparison DESIGN.md defines.
  The `ieee_` comparisons are the theory's own.
- **Datatypes stay datatypes** within the package that can see their
  fields. Outside it, an opaque type is a sort with no structure, so a
  proof in another package can rely only on what its methods and its model
  promise, which keeps `opaque` meaningful to proofs.

### Mathematical collections

`Sequence`, `FiniteSet`, `FiniteMap`, and `Multiset` are sorts with axioms
written in the prover, as Dafny's prelude axiomatizes its `seq`, `set`,
`map`, and `multiset`. The solver's own theory of sequences is not used: its
behavior differs between solvers and versions, and its decision procedures
are a common source of unstable proofs, while a fixed set of axioms with
explicit triggers behaves the same on every query.

- **A `Sequence`** has a length, indexing, slicing, `append`,
  `concatenate`, and `update`, and two sequences are equal exactly when
  their lengths and their elements are, which is extensionality.
- **A `FiniteSet`, `FiniteMap`, and `Multiset`** have membership, a size,
  and the usual operations, each with its extensionality axiom.
- **Each type's `model()`** is a function from its sort to its model's.
  Inside the standard library, `List`'s `model()` is a definition over its
  buffer, whose model the intrinsic module states. Outside it, `model()` is
  known only through the contracts of `List`'s methods, which is how other
  packages reason about lists.

### Equality

- **Structural equality is the solver's equality.** For a type with
  structural equality (see DESIGN.md, "Equality, ordering, and deriving"),
  `a == b` is the solver's `=`, which the solver substitutes through
  everywhere.
- **Every other `Equal` is a function** with the laws of `Equal` as facts:
  reflexive, symmetric, and transitive. From `a == b` the prover concludes
  only what those laws and the type's contracts give.
- **A derived `Equal` that is not structural** is defined field by field
  with each field's own `==`, so a `Point` of floats is equal exactly when
  its coordinates are, by the lawful float comparison.

### Generic code is proven once

A generic function is proven once, for every type argument, as Dafny and
Verus prove generic code, not once per instance. Its type parameters are
sorts the solver knows nothing about, and each bound brings the methods of
its trait as functions with the trait's contracts and laws. This is what
lets a generic function's proof be cached like any other, and it is why a
trait's contracts and laws, not its implementations, are what generic code
may use.

## What functions mean

DESIGN.md's [What a function means to the prover](DESIGN.md#what-a-function-means-to-the-prover)
decides when a body is a definition. In the solver:

- **A function used in specifications is a function symbol.** A pure
  function with a `time` clause is a function in the logic, applied to its
  arguments, wherever it is called, in code as in specifications, so
  `let sorted = is_sorted(items)` and `ensures is_sorted(items)` mean the
  same term.
- **Its contract is an axiom.** For every argument that meets its
  `requires`, its `ensures` holds of its result. Dafny states the same
  axiom for each function. It is sound because the function terminates,
  and is defined, wherever the `requires` holds.
- **A definition is a second axiom,** that the function's result is its
  body, for every argument that meets its `requires`. It is stated only
  where the body may be read: in the function's own package if the body
  reads an opaque type's fields, and everywhere otherwise.
- **Recursive definitions unfold once per use.** An axiom that could unfold
  itself forever would let the solver loop, so a recursive definition is
  stated with fuel, as Dafny states it: each use unfolds one level, and a
  proof that needs more calls a theorem or asserts the steps between. A
  definition that is not recursive unfolds without limit.
- **Every other function is a fresh result.** A call to a function that is
  not pure, or has no `time` clause, gives a new value about which its
  `ensures` is known, and two calls are not known to agree.
- **Function values are applied through `apply`.** A named function passed
  as a value has an axiom that applying it is calling it. A lambda that
  captures values is a term built from what it captures, and when its body
  is functional, applying it is its body, so a contract such as `List.map`'s
  `ensures result[i] == transform(self[i])` gives the caller facts about its
  own lambda. Only a function type that is pure and has a `time` clause can
  be applied in a specification, which the type checker ensures.
- **A lambda passed where a parameter's type has a `requires`** is
  checked with that `requires` assumed of its arguments, with the call's
  arguments in place of the callee's parameters. In
  `indices.map(fn(i) { values[i] })`, the lambda knows
  `indices.model().contains(i)`, and the caller's facts about `indices` do
  the rest. A call through such a parameter, in the callee's body, asserts
  the `requires` of its arguments.

Callers' proofs depend on whether a body is a definition, and on the body
itself when it is. Both are in the trace of every proof that used the
definition, and pruning (see [Queries](#queries)) keeps a definition out of
the queries that do not need it, so editing the body of `is_sorted`
re-proves only the queries that unfolded it.

## Verification conditions

### Proof programs

`Paths` turns each checked body into a *proof program*, a small control-flow
graph whose statements are:

| Statement | Meaning |
|---|---|
| `x := term` | A new version of a local or a place |
| `havoc x` | `x` takes any value of its sort, such as a `mut` argument after a call |
| `assume fact` | The rest of the path may rely on `fact` |
| `assert fact, obligation` | `fact` must hold here; the rest of the path may rely on it |

This is the shape of Boogie, the intermediate language behind Dafny, and of
Why3's, cut down to what Truss needs. Proof programs have no loops: each
loop is cut at its head by its invariant, as below. `Vc` gives each version
of each variable its own name, then computes weakest preconditions in the
compact form of Flanagan and Saxe ("Avoiding Exponential Explosion", 2001),
so a verification condition grows with the body, not with its number of
paths.

### Calls

A call to a function that is not a definition the prover reads becomes:

1. `assert` each `requires`, with the arguments in place of the parameters
2. for each `mut` argument, `havoc` it, keeping its old value for `old`
3. the result is a fresh value, or the function symbol applied to the
   arguments when the function is pure and has a `time` clause
4. `assume` each `ensures`, and each type invariant of the result and of
   each `mut` argument

A call the type checker resolved to an `impl` uses the `impl`'s contract; a
call through a bound or through `any` uses the trait's. A capability call
uses the capability method's contract.

### Loops

- **A `while` loop** is cut at its head. Its invariants are asserted on
  entry, every place the body may change is havocked, the invariants are
  assumed, and the body runs once from there, after which the invariants
  are asserted again. The places a body may change are the ones the type
  checker recorded it as assigning or passing `mut`, so nothing else loses
  what was known about it.
- **A `for` loop** is the same, with what the `each` it calls promises. A
  ghost sequence, `yielded`, holds what the earlier iterations received.
  At the head, the loop's invariants and the method's clauses that hold
  where it may end are assumed of `yielded`. Each iteration either takes a
  fresh value meeting the method's clauses for each `yield`, runs the body,
  and appends the value, as the body left it, to `yielded`, or leaves with
  `finished` true. A `break` leaves with `finished` false.
- **Nothing about loops is built in.** `for i in 0..count` knows
  `i < count` because a range's `each` promises
  `ensures self.start <= result && result < self.end`, and a loop over a
  list runs once per element because `List.each` promises
  `ensures finished ==> yielded.length() == self.length()`. A user's
  collection whose `each` promises the same gets the same facts.

### Lending and yielding methods

- **In the method's own body,** each `yield` asserts the clauses that
  mention `result`, with the part as `result`. For a `mut` part, the part's
  place then takes a fresh value that meets the part's type invariant,
  since the caller may have changed it, and the part is appended to
  `yielded`. In a yielding method, each `yield` also asserts the clauses
  that hold where the method ends, with `finished` false, and the invariant
  of `self`, since a loop may stop there. At the end of the body, those
  clauses are asserted with `finished` true.
- **At a call to a lending method,** the caller's statement gets the part,
  about which the clauses that mention `result` are known. When the
  statement is done with it, `self` is havocked, and the clauses that hold
  where the method ends are assumed, with `yielded` holding the part as the
  statement left it. This is how `mut grid.cell(position).visit()` is known
  to change exactly the one cell.
- **A pulled cursor** carries `yielded` as a ghost part of its value.
  `next()` gives `Some` of a value that meets the method's clauses for each
  `yield`, or `None`, after which the method's other clauses hold with
  `finished` true.

### Type invariants

Each type with invariants has a validity predicate: the conjunction of its
invariants and the validity of its fields.

- **Validity is assumed** of each parameter on entry, each result of a
  call, each value a call left in a `mut` argument, and each value received
  from a `yield`.
- **Validity is asserted** where DESIGN.md says an invariant must hold:
  where a value is built or updated with `with`, where it is passed to a
  call or returned, for each `mut` parameter where its function ends, and
  at each `yield` where a yielding method may end.
- **A private method that takes `mut self`** neither assumes nor asserts
  the validity of `self`. A call to one from a method of the same type
  passes `self` without asserting it, so a half-finished update can be
  finished by a helper. Its `requires` and `ensures` carry what it needs and
  leaves.
- **Values that are not parameters keep what is known.** A local that was
  valid stays known to be valid until it changes, so a body may break an
  invariant between two calls and restore it.
- **Functions in an invariant are definitions or contracts like any
  others,** so a type's validity may unfold `is_sorted` or rely on its
  contract.

### Specifications

Every specification is first checked to be well defined, as Dafny checks
its expressions: each call in it meets its callee's `requires`, each index
is in bounds, and each division has a nonzero divisor, reading `&&`, `||`,
`==>`, and `if` from left to right, so the right side may rely on the left.
A `requires` is checked with the `requires` before it, an `ensures` with
every `requires` and the `ensures` before it, and an invariant with the
invariants before it. Only then is the specification used.

- **Arithmetic is exact** on `Integer`, and an `Integer` passed where a
  built-in integer is expected carries the type checker's obligation that
  it fits.
- **`old(e)`** is `e` evaluated in the versions of the parameters on entry.
- **A quantifier over a range or a collection** is a quantifier whose bound
  name is limited to it: `forall i in 0..count => p` is "for every integer
  `i` with `0 <= i < count`, `p`", and over a list it ranges over the
  indexes of the list's model.

### Proofs

- **A theorem is proven like a function** that returns nothing: its
  `requires` are assumed, its body runs, and its `ensures` are asserted.
  A call to a theorem asserts its `requires` and assumes its `ensures`.
  A theorem that calls itself is a proof by induction, which its
  `decreases` makes sound.
- **A `proof` block's statements** are part of the proof program at that
  point and nowhere else. Its calls and `assert`s add facts for the
  obligations after it. Codegen never sees it.
- **`assert`** in a theorem or a proof is an obligation, and a fact for the
  rest of the path. In a test, it is also checked when the test runs.
- **A law** of a trait is a fact, quantified over its parameters, wherever
  the trait's methods are used on a type that implements it: for a type
  parameter bounded by the trait, and for a concrete type whose `impl`'s
  laws are proven. Each hand-written `impl` must prove each law, from the
  `impl`'s method contracts and definitions and the body of its `proof`
  definition, if there is one. A law's own proof never uses that law.
- **A derived implementation** gives axioms by the version of the rule that
  derived it: equality field by field, ordering by variant and then field by
  field, and the laws that follow. Nothing is proven for it, as DESIGN.md
  says.
- **An `impl` with clauses of its own** proves its own `ensures` and cost
  clauses, and that the trait's `requires` implies its own.
- **A method that replaces a provided one** proves that its result equals
  the provided body, which is a definition, with the trait's `requires`
  assumed.

## Queries

### One query per obligation

Each obligation gets a query of its own: the facts on the paths that reach
it, the obligations before it on those paths, which are assumed since each
is proven by its own query, the axioms of the functions and types it
mentions, and the negation of the obligation. The solver proves the
obligation by finding no way to satisfy the query. Dafny's
`--isolate-assertions` and Verus's `spinoff_prover` do the same for
stability: a small query is answered quickly and the same way every time,
while one query for a whole function can fail because of an unrelated part
of it.

### Pruning

A query holds only the facts that can matter to it. Starting from the
symbols of the obligation and its path, `Prune` adds each axiom whose
triggers use only symbols already included, and repeats until nothing more
is added, as Dafny's pruning does. A change to a function that no included
axiom mentions leaves the query's text, and so its cached result, alone.

### The canonical form

A query's text is canonical, so that its hash can be its cache key:

- **Names are numbered.** Every symbol, whether a definition, a local, a
  version of a local, or a sort, is named by the order of its first
  appearance in a fixed walk of the query, never by its Truss name. This is
  how DESIGN.md's promise holds that renaming or moving a definition finds
  its callers' proofs already done, and solvers are known to change their
  answers when only names change, so numbering also makes the answer
  depend only on the meaning.
- **Order is fixed.** Declarations come in the order of their numbers,
  and facts in the order of the walk.
- **Positions are not in the query.** The obligation's position is kept
  beside it, for its diagnostic.

### The solver

- **Z3, pinned,** as Dafny, Verus, and F* use. Its version is part of the
  prover's version, and so of every cache key, as IMPLEMENTATION.md says.
  A second solver, such as cvc5, could be added later as another version.
- **A fixed limit in steps.** Each query runs with the same `rlimit`, which
  counts the solver's work, not time, so a slow machine never fails a proof
  a fast one passes. The limit is set by the prover's version, not by the
  project or the code, so a proof that passes anywhere passes everywhere. A
  proof that needs more help gets it from a `proof` block or a theorem.
- **One process per query,** given the query's text through SMT-LIB, with a
  fixed random seed and one thread. A solver that answered earlier queries
  carries state that can change later answers, so no state is shared. Many
  queries run at once, one per core.
- **A cached result is a fact about the text.** The cache key is the hash
  of the query's text, the solver's identity, and its options, so a result
  can be reused, or shared between machines, whenever the text is the same.

## Quantifiers and triggers

A quantified fact helps the solver only when the solver knows when to use
it, which SMT solvers decide by *triggers*: terms that, when they appear,
make the solver instantiate the fact. Dafny and Verus choose most triggers
themselves, and Verus asks for them by hand where its choice fails. Truss has
no syntax for triggers, so the prover always chooses:

- **A trigger is a set of terms** that together mention every bound name,
  and that are applications of functions, indexing, or fields, never
  arithmetic or equality, which the solver cannot match on.
- **The smallest such terms are chosen,** as Dafny does, and every set of
  them that covers the bound names is used, so the fact applies wherever
  any of them appears.
- **A quantifier with no trigger** is still sound to assume, but never
  used. A proof that would need it fails, and its diagnostic says that the
  quantified fact could not be used, with the reason, so that it can be
  stated through a function that is.
- **A quantifier being proven needs no trigger.** Its bound names become
  fresh constants.

## Termination

`Termination` builds each package's call graph as a package check, with its
own query and trace, since a cycle can only be seen across definitions:

- **Edges are every way a function can reach another:** a call, naming a
  function as a value, and, inside an `impl`'s methods, using that `impl`,
  as DESIGN.md's [Termination](DESIGN.md#termination) describes. An `impl`
  used where a bound needs it is an edge from the code that uses it to every
  method of that `impl`.
- **Cycles cannot cross packages.** Packages do not depend on each other in
  a cycle, and a function in one package reaches another package's
  functions only through what code in the first package names, so every
  cycle lies within one package's graph.
- **Each edge in a cycle through a function with a `time` clause is an
  obligation:** the callee's measure, with the call's arguments, is smaller
  than the caller's. A measure is the `decreases` clause, compared in
  order, where each `Integer` stays at or above zero. Without one, the
  call must be structural: an argument is a part of the caller's argument
  in the same position.
- **Parts are ordered.** A field or a variant's field is smaller than the
  value it is in, and an element of a standard collection's model is
  smaller than the collection, so an element of a part is smaller than the
  whole. Dafny orders its datatypes and sequences the same way.
- **An edge from using an `impl`, or from naming a function as a value,
  passes no arguments,** so it can never be shown to decrease. Such a
  cycle through a function with a `time` clause is an error that names the
  cycle, and says to write the recursion as a direct call on a part.
- **Each loop in a function with a `time` clause** must end. A `for` loop
  ends because the `each` it calls has a `time` clause. A `while` loop with
  a `decreases` clause proves that it decreases on every iteration and
  stays at or above zero. Without one, the prover tries one measure, which
  is the simple case DESIGN.md mentions: for a condition `a < b` or
  `a <= b`, the measure `b - a`, and for `a > b` or `a >= b`, `a - b`. If
  that measure does not work, the loop needs a `decreases` clause, which
  the error says.

## Costs

### What is counted

`Costs` adds a ghost counter for each resource that has a cost clause:

| Resource | Counts |
|---|---|
| `time` | One for each primitive operation and each call, plus each callee's own `time` |
| `allocations` | Each allocation, and each callee's `allocations` |
| `allocated_bytes` | The bytes of each allocation, and each callee's `allocated_bytes` |
| `calls(target)` | Each call to the target, and each callee's count for it |

A counter is an `Integer` in the proof program, increased at each step and
each call, so costs are proven by the same verification conditions as
everything else. A callee's cost is what its cost clause promises, never
what its body does, as DESIGN.md requires.

### Exact bounds

A bound written with `<=` or `==` is an obligation on the counter where the
function returns, with the counter starting at zero. Callees' exact bounds
add exactly, so `cost calls(visit) == items.length()` follows from a `for`
loop that calls `visit` once per iteration over a list it runs through once.

### Asymptotic bounds

`O(f)` promises that the cost is at most `c * f + d` for some constants. The
constants are what makes this hard to prove: each callee has constants of its
own, unknown to the caller, and the prover must find the caller's. Truss
removes them in two steps:

1. **Count in units.** Each callee's `O(g)` is counted as `g + 1` with its
   arguments, each step as 1, and each call through a function value `visit`
   as `time(visit)`, which is at least 1. Every callee's real cost is at
   most `C` times what is counted, where `C` is the largest of the callees'
   constants and 1. That `C` is a fixed number, though unknown, so a bound
   `counted <= c' * f + d'` proves the real cost is at most
   `C * c' * f + C * d'`, which is `O(f)`.
2. **Try fixed constants.** Since counting in units removed every unknown,
   the prover tries a short, fixed list of pairs for `c'` and `d'`, in
   order, and stops at the first one the solver proves. The list starts with
   `c' = 2^17` and `d' = 2^16`, which covers bounds whose terms differ by
   large constant factors, a recursion with any number of recursive calls,
   and the base cases of recursion, and then tries `d' = 0`. Each try is its
   own query, so a cost clause's result is as deterministic and as cached
   as any other.

Recursion uses the same constants: a recursive call adds `c' * f + d'` with
its arguments, which is the induction hypothesis, made sound by the measure
that proves termination. So binary search's
`1 + c' * log(n / 2) + d' <= c' * log(n) + d'` holds because
`log(n / 2) == log(n) - 1` for every `n` at least 1, one of the facts the
prover gives the solver about `log`. That fact is exact because DESIGN.md
rounds `log(n)` as it does. A tree's `O(size)` walk needs `c' > d'`, and
merge sort's `O(n * log(n))` needs `c'` large enough to pay for the merge,
which the first pair gives both.

### Loops

A loop's cost is its number of iterations times a bound on each iteration,
plus what happens before and after:

- **The number of iterations** of a `for` loop is the length of `yielded`,
  which the `each` it calls bounds, as `List.each`'s
  `ensures yielded.length() <= self.length()` does. That of a `while` loop
  is at most one more than its measure's starting value, when the measure
  is a single `Integer`.
- **Each iteration's bound** is the iteration's counted cost, with each
  value the loop changes replaced by an upper bound the loop's invariants
  or its range give in terms of values it does not change. So `work(i)`
  inside `for i in 0..count`, with `work` costing `O(i)`, is bounded by
  `count` on every iteration.
- **The prover adds the invariant** that the counter is at most its value
  on entry plus the iterations so far times that bound, or, for an exact
  bound, exactly that.

- **A loop with a `cost` clause** is not bounded iteration by iteration.
  The clause is an invariant about the counter since the loop began: it is
  asserted on entry, assumed at the head, and asserted again after each
  iteration, and the loop's constants are found as a function's are, from
  the same list. After the loop, its cost is counted as its bound, plus one,
  in the state the loop ended in, as a call with that bound would be. So
  a loop over rows of different lengths states
  `cost time O(yielded.length() + total_cells(yielded))`, and each
  iteration only has to show that it spent no more than its row adds to
  the bound.

### Amortized bounds

- **A value's potential** is its type's `cost potential` plus the
  potentials of its parts, as DESIGN.md defines it, through the model of a
  standard collection for its elements.
- **Potential is counted in a unit of its type's own,** one unknown constant
  for each type with a potential, the same for every method of the type, so
  that potential saved by one method pays for another's work.
- **A method with `cost amortized time O(f)`** proves that its counted cost,
  plus the potential of what it returns and of each `mut` parameter
  afterward, minus the potential of each parameter on entry, is within the
  bound.
- **A call to one** adds its bound to the caller's counter and subtracts the
  change in potential of what it changed, so a caller with a plain bound
  pays for the potential it consumed from what it was given: a function
  that pushes `count` times can promise `O(count + items.length())`.
- **Potentials never go below zero,** which is proven for each type with
  one, from its invariants.

## Running code while proving

Some obligations are about values known when compiling. The check of a
tagged template, `requires is_valid_pattern(template.literals)`, applies a
function to literal text, which no solver can decide by reasoning about a
regular-expression parser.

- **A call whose arguments are all constants is evaluated.** When an
  obligation mentions a call to a pure function with a `time` clause, which
  is compiled rather than for specifications only, and whose arguments are
  all known values, `Evaluate` runs the compiled function in the test
  runner's workers and adds its result as a fact, as CODEGEN.md's
  [Code run while compiling](CODEGEN.md#code-run-while-compiling) describes.
  The rest of the obligation, such as conditions on the template's parts,
  is proven as usual.
- **This trusts compiled code.** A fact from running code is only as true as
  code generation and the C compiler, which is what Lean's `native_decide`
  trusts too. It is the price of a check that no solver could make, and
  `--check-proofs` executions test it like every other trust.
- **A run has the project's test time limit.** A function with a `time`
  clause always ends, but not necessarily soon. One that runs past the
  limit is an error that names the call.
- **Results are cached** by the function's compiled code and the arguments.

## Holes

A `todo` in a theorem, a `proof` block, or a `proof` definition is the one
gap a proof may have, as DESIGN.md says. The obligations it was to prove are
recorded as holes rather than failures, with the facts in scope, so the
tools can list them as tasks. A build of a program refuses one that can
reach a hole, as it refuses one that can reach a `todo` in code. Tests run
regardless, with their run-time checks.

## Diagnostics

Each obligation the prover could not prove is an error, with the shared
`Diagnostic` type from LEXER.md, a code for each kind of obligation, such as
`prover.index`, `prover.overflow`, `prover.requires`, `prover.ensures`,
`prover.invariant`, `prover.termination`, and `prover.cost`, and:

- **What could not be shown,** written in Truss: "`index < items.length()`
  may be false here", pointing at the operation, with a note at the clause
  it comes from.
- **Whether the solver found a counterexample or ran out of steps.** A
  counterexample means the fact can be false on some path. Running out of
  steps means it may be true but needs help, and the message says so.
- **The path and the values.** With a counterexample, the solver's model is
  turned back into Truss values, written as debug output writes them, and
  the branches the path takes are listed by position. An agent can turn
  these values into a test, which then fails at its run-time check if the
  code is wrong.
- **An exact fix where there is one.** For an obligation that mentions only
  parameters, the fix adds it to the function as a `requires`. DESIGN.md's
  other fixes, checking it with an `if`, using the checked version of the
  operation, and `uses Panic`, change what the code means, so the message
  names them without applying them.
- **One error per cause.** An obligation that the same failure makes
  unprovable on another path, such as a second index into the same list
  with the same index, is not reported again.

## Incremental work

The prover's results follow the rules of every stage (see DESIGN.md,
"Incremental builds"):

| Edit | Proven again |
|---|---|
| A function's body | The queries whose paths pass through what changed |
| A function's `ensures` | Queries that used it: the function's own, and callers' that included it after pruning |
| A function's `requires` | The same, plus each caller's obligation to meet it |
| A body that is a definition | Queries that unfolded it |
| A type's invariant | Queries that assumed or asserted it |
| A trait's law | Each `impl`'s proof of it, and queries that used it |
| A local's name or a definition's name or module | Nothing, since queries number their names |
| A `proof` block | The queries after it in its body |
| A new `impl` | That `impl`'s own obligations, never its trait's callers |
| A new solver or prover version | Everything, once, through the version in each key |

## The trusted base

A proof is as trustworthy as:

- the solver, and the prover's translation into its logic
- the axioms of the mathematical collections, of `log` and `power`, and of
  the derivation rules
- the contracts the compiler declares for the intrinsic module, which the
  standard library is proven against
- compiled code, for the calls `Evaluate` runs

Everything else, including the whole standard library above the intrinsic
module, is proven. Sanitizers, `--check-proofs`, and the run-time checks of
every test build test the trusted base against real executions.

## Interfaces to other stages

- **The type checker** gives checked forms, interfaces, contracts, the
  places each loop changes, and the obligations it created, as
  TYPECHECKER.md describes. The prover never reads a syntax tree.
- **Code generation** relies on the prover for builds of programs: a
  program is built without run-time checks only once every obligation it
  can reach is proven. Test builds do not wait. The prover relies on code
  generation to run the calls `Evaluate` makes.
- **The build** refuses a program that can reach an unproven obligation or
  a hole in a proof.
- **The language server** shows each obligation's state at its position,
  and the counterexample of each one that failed.

## Testing

The tests follow IMPLEMENTATION.md's rules for testing: each gives a small
input and states one fact about the result, and there are no golden files.

- **Focused tests.** A test gives a few small definitions and asserts that
  one obligation, named by its kind and position, is proven, or is not,
  with the counterexample's values when it matters. For example:
  `items[i]` inside `for i in 0..items.length()` is proven; `count + 1`
  with a `UInt8` count is not, with `count == 255`; a `lends mut` call
  leaves every other cell of the grid unchanged.
- **Soundness tests.** Every hole this design closes has a test that it
  stays closed: two `impl` methods that reach each other through a generic
  function cannot prove their `time` clauses; substituting through a
  `Point` of floats proves nothing; a specification cannot call a function
  that uses `Panic`; a law cannot be used in its own proof.
- **Deterministic queries.** A test builds the queries of the same
  definition twice and asserts that their texts are byte-identical, and
  that renaming every definition gives the same texts.
- **Incremental work is tested as behavior.** A test proves a few
  definitions, edits one, and asserts exactly which queries were solved
  again.
- **The documents' examples are proven.** Once the standard library has its
  contracts, every complete example in the documents proves, each as a test
  of its own.
- **Tools, run by hand, in `stage0/tools/`:** a fuzzer that mutates the
  documents' examples and checks that every obligation the prover proves
  never fails its run-time check when the mutated program runs, and a
  benchmark of solving time over the standard library.

## What is built

The prover is built in three libraries: `logic`, the terms and their
canonical text; `solver`, the pinned Z3; and `prover`, which holds the rest
of the table in [Structure](#structure) as two modules for now, `Translate`,
which does the work of `Encode`, `Paths`, `Obligations`, and `Vc`, and
`Prover`, the entry point and its diagnostics. Proof programs are not a data
structure of their own yet: `Translate` executes a checked body forward in
the passive form `Vc` describes, guarding every fact by its path and giving
each local a fresh symbol where paths join.

It proves, with one canonical, numbered, hashed query per obligation:

- overflow of `+`, `-`, `*`, `/`, `%`, and negation on built-in integers;
  division by zero and the least value over `-1`; shift amounts; and
  `unreachable`
- every `requires` at a call to a function, a theorem, or a trait method
  whose contract it reads, and every `ensures` at each way a function
  returns, with `old`, `result`, and `mut` arguments. A call resolved to an
  `impl` reads the `impl`'s clauses with its trait's, and its own `requires`
  when it states any; a call through a bound reads the trait's. Each
  callee's clauses are read with the call's type arguments, and its
  `ensures` is assumed only where its `requires` holds.
- an `impl`'s method keeps its trait's contract: the trait's `requires`
  is assumed and must imply the method's own, and the trait's `ensures`
  is shown at each way it returns, since calls through a bound rely on
  them
- indexing, through the `impl` of `Index` a call reaches, so every index
  into a `List` or a `Slice` is checked against `key < self.length()`; and
  assigning to an element, after which the collection is not known any
  more, since `lends mut` contracts are not read yet
- functional bodies as definitions: a pure function with a `time` clause
  and a functional body is unfolded once at each call, where its
  `requires` holds, unless its body reads what the prover cannot
- `if`, blocks, `let` and `var` with any pattern that cannot fail,
  assignment and compound assignment to a local, to a field of a place, or
  to an element, `return`, `parallel`
  blocks in order, and `proof` blocks
- records and sum types whose fields the package sees, as algebraic
  datatypes with their variants and fields sorted by name: building them,
  with fields defaulted, reading fields, variants with no fields,
  constants, `with`, `match` with guards and every pattern but strings and
  alternatives that bind, `is`, `?` on a `Result` or an `Option`, and `==`
  as the solver's equality for types with structural equality. Each field
  read is in its type's range, and a counterexample shows a value by its
  variant and fields.
- `while` loops, `for` loops over ranges of integers, and `for` loops over
  an `each` method, whose elements are fresh values of their type, since
  `yield`s' contracts are not read yet; with invariants on entry and after
  each iteration, and, in a function with a `time` clause, termination by
  `decreases`, the one measure the prover tries itself, or the `time`
  clause of the `each` a loop calls
- recursion over each package's call graph, whose edges are calls,
  functions named as values, and `impl`s used where a bound needs one: a
  call in a cycle through a function with a `time` clause, or a theorem,
  must decrease the caller's `decreases` measure, compared in order, by the
  callee's; a use of an `impl` that reaches back cannot, and is an error;
  and every call from such a function must reach something with a `time`
  clause. Structural recursion without a `decreases` is not proven yet.
- type invariants, as [Type invariants](#type-invariants) describes: a
  value's validity, its type's invariants with its fields' validity, is
  assumed of parameters, call results, values left in `mut` arguments, and
  a loop's elements; the type's own invariants are shown where a value is
  built or updated with `with`, and its validity where it is passed to a
  call, returned, or left in a `mut` parameter or `mut self`; a private
  method that takes `mut self` neither assumes nor shows its `self`'s, and
  neither does a call to one for its receiver
- `assert` in theorems and proofs, assumed in tests
- quantifiers over ranges and over the integers, in specifications
- the type checker's `Integer_fits` obligations

A call to anything whose contract it does not read yet, such as a trait
method or a capability, gives a value known only by its type's range, and
so does building a type whose fields the package cannot see, and `==` on a
type without structural equality: sound, but it proves little. A
definition that uses anything else, such as a lambda, a string, a float, a
cursor, or a lending or yielding method's own body, is reported as
`prover.unsupported` with what stopped it, and none of its obligations
count as proven. A cost bound, and a loop's
`cost`, are reported as not proven yet, while the rest of the definition is
proven as usual.

## Open questions

- **Turning off a definition.** Dafny and Verus can hide a body from the
  solver, which keeps large definitions from slowing queries that do not
  need them. Pruning may be enough; if not, a way to say so is needed.
- **The limit in steps.** Its value, and whether it should grow with the
  size of a query, are to be set by measuring the standard library's
  proofs.
- **Contracts for concurrency.** Tasks and channels are capabilities, so
  their contracts are what code can rely on, but what those contracts
  should say about ordering is not designed yet.
