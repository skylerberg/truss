# Truss Prover

This document describes stage0's prover, in
[`stage0/prover/`](stage0/prover). It takes the core form of each definition
([TYPECHECKER.md](TYPECHECKER.md)), its callees' interfaces and contracts,
and the bodies it reads as definitions. For each definition it finds every
*obligation*, a fact that must hold for the program's promises to be kept,
builds one solver query for each, runs a pinned solver within a fixed number
of steps, and reports each obligation it could not prove, with a
counterexample. Its queries run on the code database
([DATABASE.md](DATABASE.md)).

It does not type-check, resolve names, or read syntax trees: the core form has
every callee, every operation, and every type solved. It infers no
specifications. It does not decide whether a test runs; tests run as soon as
the code type-checks, and only builds of programs wait for proofs.

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
Why3 put a proof program between the language and the logic, which keeps the
two apart at the cost of a second representation of every body that only the
prover would read. The MIR is a second representation too, but every consumer
reads it, and the walk is to read it in place of the core form (see
[MIR.md](MIR.md)).

### One definition at a time, one obligation at a time

- **A definition's obligations are a query** that reads its core form and,
  through the environment, the interfaces, contracts, definitions,
  invariants, and laws its obligations mention, each recorded in its trace.
  Its result is every obligation with its solver query, not the answers.
- **Each obligation is a query of its own,** whose answer is kept under the
  hash of its canonical text. Editing one statement changes only the queries
  whose paths pass through it.
- **Early cutoff happens twice:** a definition that read nothing that changed
  keeps its obligations, and one whose obligations are made again asks the
  solver only about queries whose text changed.

## Obligations

| Obligation | Where |
|---|---|
| An index or slice is in bounds | Each index, through the `requires` of the `impl` of `Index` it reaches |
| An operation does not overflow, or divides by zero | Each such operation on a built-in integer, including the intrinsic ones an `impl` of `Add` calls; on an unsigned type only the bound it can pass |
| A shift amount is below the width | Each `<<` and `>>` |
| `unreachable` is never reached | Each, including those after guards |
| A call's `requires` holds | Each call, including theorems and calls in specifications |
| An `ensures` holds | Each way a function returns, and for a lending or yielding method each `yield` and each end |
| A type's invariant holds | Each value built or updated, passed or returned, each `mut` parameter at the end, each part yielded or lent `mut` when the lend ends, each value a loop changes at the end of an iteration, and each `yield` where a method may end |
| A loop invariant and a loop's `cost` hold | On entry and at the end of each iteration |
| A callback's `requires` holds, and a function passed for it accepts every argument it is promised | Each call through, and each function passed for, a parameter whose type has a `requires` |
| A function value accepts every argument of its type | Each function with a `requires` used as a value other than in a call or as an argument |
| Recursion and loops end | Each call in a cycle, and each loop, in a function with a `time` clause |
| A cost clause holds | Each function with one |
| A law holds | Each law of each trait an `impl` implements by hand |
| An `impl` keeps its trait's contract, and a replacement gives the provided result | Each method of an `impl` |
| `assert` holds | Each `assert` in a theorem or a proof |
| A specification is well defined | Each call, index, and division in a contract, a loop's clauses, an invariant, and a potential |
| The type checker's and ownership check's obligations | An `Integer` that fits; two indexes or ranges that do not overlap |
| A `FiniteMap` literal's keys are distinct | Each one in a specification |

- **An obligation names its kind, its definition, and its position within the
  definition.**
- **A constant is one symbol where it is used,** with its value stated once in
  each query as a fact, so a large table is not repeated at each use. Its own
  obligations are reported where it is defined.
- **Two places lent together** are shown to be at different indexes. Only
  elements of a `List`, `Slice`, or `Array` are lent together, and a slice is
  some elements of its collection, so two slices, or a slice and an index,
  reach different elements too.

## The logic

### Values are values

Mutable value semantics keeps the logic small. No two names change the same
memory, so the prover has no heap, no aliasing, and no permissions, which
verifiers for Rust and for languages with references need.

- **Every value is a term,** and nothing about it depends on where it is
  stored.
- **A `mut` parameter is two values,** on entry and on return; a call with
  `mut items` replaces `items` with a fresh value the callee's `ensures`
  relate to the old one.
- **A view is the value it views,** since the original is frozen while it is
  used, so `items[a..b]` is that run of the collection's model.
- **Moves, drops, and copies are invisible,** since a moved value is never used
  again and a copy equals its original.
- **Capability calls return fresh values.** The prover never models an
  implementation's state: a call gives a value of which only the method's
  `ensures` is known, and after `provide mut files { ... }`, `files` is a
  fresh value that meets its invariant.
- **An `any` value is known through its trait.**
- **A call that returns `Never` ends its path.**
- **`parallel` branches run in order,** since they touch disjoint places.

### Types as sorts

| Truss | In the solver |
|---|---|
| Built-in integers, `Integer` | The integers, with a built-in type's range as a fact about each value of it |
| `Bool` | Booleans |
| `Character` | Integers up to `0x10FFFF` that are not surrogates |
| `Float32`, `Float64` | The SMT-LIB floating-point theory, bit for bit |
| Records and sum types whose fields are visible | Algebraic datatypes, one per type with its arguments |
| Opaque types from another package, types defined as `todo`, the mathematical collections, type parameters, `any` types, function types | Uninterpreted sorts |

- **Integers are mathematical integers,** and each operation on a built-in
  integer is exact with an obligation that the result is in range, as in
  Dafny and Verus.
- **Each intrinsic means what the compiler makes it do.** Wrapping arithmetic
  is the exact result brought into range by a remainder; a float converted to
  an integer must fit, since the compiled cast is undefined otherwise; an
  integer converted to a float is the nearest float, ties to even. A storage,
  a view, and an array are each known by a `Sequence` model, which
  `storage_model`, `view_model`, and `array_model` name, and each operation
  reads or changes that sequence. These meanings are part of the trusted base
  (see [The trusted base](#the-trusted-base)).
- **A C function is given only an address into a storage,** so every storage
  it is lent keeps its length and capacity. Each function's row of the C
  library's table says how many elements it reads or writes through each
  address, and that many must be there.
- **A slice passed to change** changes only its run of its owner.
- **Bitwise operations get a second encoding.** On integers they are functions
  known by a few facts: for unsigned values `a & b` is at most each operand,
  `a | b` at least each, both below every power of two both operands are below,
  and a shift is a multiplication or division by a power of two. That proves
  the bounds most bit twiddling needs. A query not proven that way is tried
  once more with each bitwise operation defined exactly on its operands' bits,
  which the solver decides by bit-blasting. Verus asks for this by hand; Truss
  tries both, always in the same order, and caches both answers. Only the
  bitwise operations change, so the second query is equivalent to the first.
- **Floats follow IEEE 754 exactly.** `==` on floats is `fp.eq` or both NaN,
  and `<` puts NaN last. A float `%` is known only by its type.
- **Datatypes stay datatypes** within the package that can see their fields,
  and outside it an opaque type is a sort known by its methods and model,
  which keeps `opaque` meaningful to proofs. Variants and fields are in the
  order of their names, so reordering them changes no query.
- **Text is its bytes.** A plain string literal is a `String` with its bytes;
  one with interpolations is the calls the core form has for it.

### Mathematical collections

`Sequence`, `FiniteSet`, `FiniteMap`, and `Multiset` are types of
`standard::specification` whose operations are pure functions with contracts
written in Truss, so the trusted base holds only those contracts, not axioms
in the prover. The solver's own theory of sequences is not used: its
behavior differs between solvers and versions, and it is a common source of
unstable proofs.

- **Extensionality is the one axiom,** since a contract describes a result and
  cannot state that two sequences with the same elements are identical; its
  kin hold for sets and maps. Each is stated for the pairs `identical`
  compares, not every pair, which would have the solver compare every pair it
  knows.
- **A `List`, `Set`, or `Map` literal is the calls that build it,** known by
  their contracts.
- **`identical(a, b)` is the solver's equality.**
- **Each type's `model()` is a function to its model's sort,** known through
  the contracts of the type's methods.

### Equality

- **Structural equality is the solver's equality,** which it substitutes
  through everywhere.
- **Every other `==`, and each ordering, is a function of its operands,** with
  the laws of `Equal` and `Ordered` as facts. Neither uses capabilities, so a
  comparison always gives the same answer, as their laws assume.
- **A derived `Equal` that is not structural is defined field by field,**
  unfolded once for each two values compared, so a `Point` of floats is equal
  exactly when its coordinates are.
- **Every other derived method is its derived body,** a definition like any
  pure functional body.

### Generic code is proven once

A generic function is proven once, for every type argument, as Dafny and
Verus prove generic code. Its type parameters are sorts the solver knows
nothing about, and each bound brings its trait's methods with their contracts
and laws, so a generic proof is cached like any other, and generic code may
use a trait's contracts but not its implementations.

**Code generic over an integer trait is proven once for each built-in type
that implements it.** The traits are sealed, so those are every instance there
can be, and one proof over an unknown sort would need a symbolic width, which
the bit-vector theory does not have. A failure names its instance, as in
"Where `Self` is `Int8`: ...".

## Functions in the logic

[Bodies and contracts in proofs](SPECIFICATION.md#bodies-and-contracts-in-proofs)
decides when a body is a definition. In the solver:

- **A pure function with a `time` clause is a function symbol,** wherever it
  is called, so `let sorted = is_sorted(items)` and `ensures is_sorted(items)`
  are the same term. Where its `requires` holds, its `ensures` holds of its
  result, which is sound because it terminates there.
- **A functional body is unfolded at each call,** unless it reads something the
  prover cannot see from there.
- **A body is read across packages only where it is exported:** a
  `public transparent` function, a trait's provided method, and a derived
  method. Where an obligation is not proven and its query names a callee
  whose body is hidden, the definition is translated again with every callee
  read as its own package reads it. If that proves, the message says the
  callee's body is not visible, and names the fixes: an `ensures` with the
  needed fact, or `public transparent fn`.
- **On a quantifier's bound values,** a definition with no `requires` is
  stated once for every argument, since a fact about one call would name the
  bound values. A contract, with its `requires`, and a pure function's range
  are stated once the same way.
- **Recursive definitions unfold once per use,** as fuel does in Dafny. A
  proof that needs more calls a theorem or asserts the steps.
- **An argument that holds a call is named once,** by a symbol equal to its
  term, so a query grows only with the calls in it, not by a factor at each
  level of nesting.
- **A query that runs out of steps is asked again with contracts alone.**
  Unfolding gives the solver every definition a query reaches, which can be
  too much where a callee's `ensures` states the fact, and leaving facts out is
  sound. So Truss needs no way to hide a body from the solver, as Dafny and
  Verus have: pruning keeps out a definition a query does not reach, and this
  keeps one it reaches from costing a proof its contract would give.
- **Every other function is a fresh result** at each call, known by its
  `ensures`.
- **A function value whose type has a `time` clause and no `uses`** is applied
  to its arguments, so two calls with the same arguments agree. A pure
  function named as a value is that function. A lambda with a functional body
  is its body applied, and two lambdas with the same body over the same
  captures are the same value, so a function's bound and a loop's bound that
  both write `fn(row) { row.length() }` mean the same sum.
- **A lambda is proven where it is written,** with fresh arguments, and its
  assumptions hold only inside it, since it may run any number of times,
  including none. One with a body that is not functional is known by the facts
  its body proved, for every argument that meets its assumptions.
- **A lambda passed where a parameter's type has a `requires`** is checked with
  that `requires` assumed of its arguments, with the call's arguments for the
  callee's parameters, so in `indices.map(fn(i) { values[i] })` the lambda
  knows that `i` is one of `indices`. A call through the parameter in the
  callee proves it with the parameters' values on entry, even where a `mut`
  parameter has changed since.

Callers' proofs depend on whether a body is a definition, and on the body when
it is, and both are in their traces. Pruning keeps a definition out of the
queries that do not need it, so editing `is_sorted`'s body re-proves only the
queries that unfolded it.

## Verification conditions

### Running a body forward

The walk takes four kinds of step: a new version of a local or place, a havoc
that gives one any value of its sort, an assumption, and an assertion with
its obligation. These are Boogie's statements, cut down, in the passive form
of Flanagan and Saxe (2001): every fact is guarded by its path's condition,
and where paths join, each local that differs gets a fresh symbol, as does the
joined condition, so a body's queries grow with the body, not with its number
of paths. No step goes around a loop: each loop is cut at its head.

- **The right side of `&&`, `||`, or `==>` runs on one path,** which joins the
  path where it did not run if it changes a local or spends a cost. A `match`
  arm's guard runs only where its patterns matched, so the next arm is tried
  from both.
- **A binding a pattern lends `mut`** is a local of the arm, written back to
  its part of the scrutinee wherever the arm ends.
- **A `mut` slice argument's bounds** are the values computed for the
  argument, so they are not evaluated again after the call.
- **`parallel` and `concurrent` branches are read one after another,** since
  they change disjoint places and a capability call already gives a fresh
  value. An exit from a branch takes effect where the block ends, after the
  other branches run to their own ends, so each later branch is read from the
  exit as well as from where the branch before it ended. A `return` from a
  `concurrent for` iteration returns where the loop ends, with a value known
  by its type, since which iteration's value it is is not known.
- **An `assert` makes one query,** and is then a fact for the rest of the path.
- **Code the prover cannot read soundly stops the walk,** and none of the
  definition's obligations count as proven: an obligation is never assumed
  because the code around it could not be read.

### Calls

A call asserts each `requires`, havocs each `mut` argument, keeping its old
value for `old`, gives a fresh result or the function symbol applied, and
assumes each `ensures` where the `requires` held, and the invariants of the
result and each `mut` argument. A call resolved to an `impl` reads the
`impl`'s clauses with its trait's. A call through a bound on `Self` read where
`Self` is known reaches that type's `impl` when the bounds on its parameters
hold.

- **A channel's `send` and `receive` have no `time` clause,** since waiting
  may never end. That one sender's messages arrive in order is about two
  tasks' histories, which no contract of one task's code can state, so the
  library's tests check it under many schedules instead.
- **A tagged template is a call of `from_template`** on a template whose
  literals are known by their bytes, and the tag's `requires` is proven from
  them, or by [running the check](#running-code-while-proving).
- **A call whose callee's contract cannot be read,** a call of an intrinsic,
  and building a type whose fields the package cannot see give a value known
  only by its type's range: sound, but it proves little.

### Loops

- **A `while` loop is cut at its head.** Its invariants are asserted on entry,
  every place the body may change is havocked, the invariants are assumed,
  the body runs once, and the invariants are asserted again. The places that
  may change are those the body assigns, passes `mut`, loops over `mut`, or
  matches with a `mut` binding, so nothing else loses its facts.
- **Validity is an invariant of every loop:** each changed value valid on entry
  is valid at each head and asserted at each iteration's end.
- **A `for` loop** uses the contract of the `each` it calls, with a ghost
  `yielded` of the parts earlier iterations received. Each iteration takes a
  fresh value meeting the method's clauses for each `yield`, runs the body,
  and appends the value as the body left it, or the loop leaves with
  `finished` true; a `break` leaves with it false.
- **A range of integers is the one loop the prover knows itself,** with the
  loop variable the start plus the length of `yielded` in its clauses. Every
  other loop's facts come from its `each`'s contract.

### Lending and yielding methods

- **In the method's body,** each `yield` asserts the clauses that mention
  `result`. A `mut` part then takes a fresh value that meets its invariant,
  since the caller may have changed it, which is written back to its place.
  In a yielding method each `yield` also asserts the clauses that hold where
  it ends, with `finished` false, and `self`'s invariant, since a loop may
  stop there.
- **At a call to a lending method,** the statement gets the part, about which
  the clauses with `result` are known. When the statement is done, `self` is
  havocked and the end clauses are assumed, with `yielded` the part as left.
  So `mut grid.cell(position).visit()` is known to change exactly one cell.
- **A pulled cursor** spends its method's whole cost where it is made, and
  carries `yielded` and whether it has ended as ghost parts of its value.
- **A loop over a type's own `Cursor`** promises no end, so in a function that
  must end it needs a `decreases`.

### Type invariants

Each type with invariants has a validity predicate: its invariants and its
fields' validity.

- **Validity is assumed** of each parameter on entry, each call's result, each
  value a call left in a `mut` argument, and each value received from a
  `yield`, and asserted wherever SPECIFICATION.md says an invariant holds.
- **A private method that takes `mut self`** neither assumes nor asserts the
  validity of `self`, and a call to one from a method of the type passes
  `self` without asserting it.
- **A local keeps its known facts until it changes,** so a body may break an
  invariant between two calls and restore it.
- **Validity is not computed twice for one type on one path.** A type that
  contains itself through a type with an invariant, as
  `type Tree = Leaf | Branch(children: Map[String, Tree])` does through
  `Map`'s, gets `true` for the nested request.
- **Another package's opaque type** has a validity the prover never unfolds,
  since its values come from its own package, which shows it.

### Specifications

A contract and a loop's invariants are checked to be well defined where they
are shown, as Dafny checks its expressions, each with the clauses before it.
Inside a quantifier these are checked for each value its range admits, so
`forall i in 0..items.length() + 1 => items[i] > 0` is not well defined, and a
quantifier body's assumptions hold only for those values.

- **`old(e)`** is `e` in the parameters' versions on entry.
- **A quantifier over a range or collection** limits its bound name to it:
  over a list or sequence, the indexes of the model; over a set, its elements.
- **A quantifier over a type** has each value in its range and meeting its
  invariants. A quantifier in code is read as one in a specification.

### Proofs

- **A theorem is proven like a function** that returns nothing, and a call to
  one asserts its `requires` and assumes its `ensures`.
- **A `proof` block is walked at that point and nowhere else.** Code generation
  never sees it, so nothing it assigns reaches the code after it, and a
  `return` or an endless loop inside it does not end the program's path.
- **`assert` in a test is assumed,** since the test's run checks it.
- **A law is a fact,** quantified over its parameters, wherever the trait's
  methods are used on a bounded parameter or a type whose `impl`'s laws are
  proven. Each hand-written `impl` proves each law (`prover.law`) from its
  methods' contracts and definitions and its `proof` definition, whose
  parameters are bound by position to the law's. A law's own proof never uses
  that law, and a proof that never ends shows nothing.
- **An `impl`'s method keeps its trait's contract.** Its body is proven under
  its own `requires`, or the trait's when it states none, the trait's
  `requires` must imply its own, and its `ensures` is shown under the trait's
  `requires`, since calls through a bound rely on it.
- **A trait's provided body is proven once,** with `Self` a type parameter
  bounded by the trait, so every `impl` that keeps it keeps the trait's
  clauses.
- **A replacement of a provided method** proves that its result equals the
  provided body under the trait's `requires`.

## Queries

### One query per obligation

Each obligation gets a query: the facts on the paths that reach it, the
obligations before it, assumed since each has its own query, the facts of the
functions and types it mentions, and its negation. A small query is answered
quickly and the same way every time, where one query for a whole function can
fail because of an unrelated part of it, which is why Dafny's
`--isolate-assertions` exists.

### Pruning

A query holds only the facts that can matter: starting from the obligation's
symbols, each fact that mentions a kept symbol is kept, with its symbols,
until nothing more is added. A quantified fact waits until every symbol of one
of its triggers is kept, which also keeps quantifiers out of queries that do
not need them. Dropping a fact is always sound, and a change to a function no
kept fact mentions leaves the query's text, and its answer, alone.

### Triggers

Truss has no syntax for triggers, so the prover chooses them:

- **A trigger is a set of applications** of the query's own functions that
  together name every bound name, each only as an argument, since the solver
  matches by shape: `items[i]` is a trigger and `items[i + 1]` is not.
- **The smallest terms are chosen,** and one application naming every bound
  name is preferred to a set.
- **Matching loops are avoided:** an application the fact's own body would
  match with a larger term, as `f(i)` matches `f(i + 1)`, is left out when
  anything else is left.
- **A definition triggers on the term it defines.**

When no trigger is found, the solver chooses its own, and a query that then
runs out of steps says so, since an `assert` that names the term can supply
the trigger.

**A value made inside a quantifier is a function of its bound names.** A fact
known of such a value is a hypothesis inside each quantifier the solver
skolemizes, where the bound names are constants, so it costs no
instantiation. Stating it for every value of the bound names would run the
solver out of steps on the standard library's nested quantifiers.

### The canonical form

A query's text is canonical, so its hash can be its key. Every symbol is named
by the order of its first appearance in a fixed walk, never by its Truss name,
so renaming or moving a definition finds its callers' proofs done, and the
answer depends only on meaning, since solvers can change their answers when
only names change. Declarations and facts come in a fixed order, and
positions are kept beside the query, for its diagnostic.

### The solver

- **Z3, pinned.** Another version is refused, since its answers could differ,
  and the version is part of every answer's key.
- **A fixed limit in steps.** Each query runs with the same `rlimit`, which
  counts work, not time, so a slow machine never fails a proof a fast one
  passes. The prover's version sets it, not the project. It does not grow with
  a query's size, which would make an answer depend on facts unrelated to its
  goal. A change to it changes every answer's key, so it is made by itself,
  with the benchmark of solving to show its cost.
- **One process per query,** with a fixed random seed, since a solver that
  answered earlier queries carries state that can change later answers.
- **Many queries at once,** one per core. Before any proof is read, every
  definition's queries are solved together; an answer depends only on its
  text, so this gives the same answers as solving them in turn.
- **An answer is a fact about the text,** keyed by the text, the solver's
  version, its options, and its limit, and kept in the store.

## Termination

Each package's call graph is a query of its own, since a cycle can only be
seen across definitions.

- **Edges are every way a function can reach another** (see
  [Termination](SPECIFICATION.md#termination)). An `impl` used where a bound
  needs it is an edge to every method of that `impl`.
- **A trait's method is a node,** with edges to its provided body and to each
  `impl`'s own method of that name, so provided methods that call each other,
  and a method that reaches itself through `any`, are cycles. A call through a
  bound on another type parameter is no edge of its own: it reaches the
  `impl` for the type the parameter is given where the generic code is used,
  so `List[Element].equal` calling `Element.equal` reaches a smaller type's
  `equal`, not itself.
- **Cycles can cross packages through traits,** so a walk reads each node's
  edges from its own package's graph.
- **Each edge in a cycle through a function with a `time` clause, or a
  theorem, is an obligation** that the callee's measure, with the call's
  arguments, is smaller than the caller's. Without a `decreases`, a direct
  recursive call must be structural.
- **Parts are ordered by rank,** as Dafny orders its datatypes: a field read is
  below its value, an element of a sequence below the sequence, and a model no
  higher than its value, so recursion over a tree whose children are a list
  ends with no `decreases`. The order is stated only in a function that can
  call itself with no `decreases`.
- **An edge from using an `impl`, or naming a function as a value, passes no
  arguments,** so a cycle through one is an error that says to write the
  recursion as a direct call on a part.
- **A `while` loop without a `decreases`** gets one measure tried: `b - a` for a
  condition `a < b` or `a <= b`, and `a - b` for `a > b` or `a >= b`, when `a`
  and `b` are functional. Otherwise the error asks for a `decreases`.

## Costs

### Counted operations

The prover adds a ghost `Integer` counter on each path for each resource with
a cost clause, so costs are proven by the same verification conditions as
everything else. `time` counts one for each call and each loop iteration,
plus each callee's own `time`; `allocations`, `allocated_bytes`, and
`calls(target)` count their events and each callee's counts.

- **A specification spends nothing,** wherever it is read.
- **A callee's cost is its cost clause's bound,** never its body's. A callee
  with no clause about a resource may spend any amount of it.
- **The steps between calls and iterations are not counted.** Between two of
  them a body runs at most its own length of primitive operations, which an
  `O(...)` bound's constants absorb, and a `time` bound is always asymptotic.
- **Each intrinsic declares its cost:** a fixed number of steps, steps in
  proportion to a buffer's length, or no bound; and whether it may allocate.
- **A `calls(target)` counter counts a call through any value equal to the
  target,** so a call through an alias such as
  `if flag { visit } else { other }` counts.

### Exact bounds

A `<=` or `==` bound is an obligation on the counter where the function
returns, starting at zero. Exact bounds add exactly, so
`cost calls(visit) == items.length()` follows from a loop that calls `visit`
once per element.

### Asymptotic bounds

`O(f)` promises a cost at most `c * f + d`. Each callee has unknown constants
of its own, and the prover must find the caller's. Truss removes them in two
steps:

1. **Count in units.** Each callee's `O(g)` counts as `g + 1`, each step as
   1, and each call through a function value `visit` as `time(visit)`. A call
   of a trait method that promises only that it ends counts as
   `time(T.method)` for its type: the most any one call of it takes in the
   run, a constant of the run. For a known type whose `impl` promises
   `O(k)`, it is at most `k`. Every callee's real cost is at most `C` times
   its counted cost, for `C` the largest of their constants, so
   `counted <= c' * f + d'` proves `O(f)`.
2. **Try fixed constants.** With no unknown left, the prover tries a short,
   fixed list of pairs for `c'` and `d'`, starting with `2^17` and `2^16`, and
   stops at the first the solver proves. Each try is its own query, so the
   result is deterministic and cached.

A recursive call adds `c' * f + d'` with its arguments, the induction
hypothesis, made sound by the termination measure. Functions in a cycle each
assume the others' bounds with their own constants, which is sound only with
the same pair, so they try only the first. So binary search's
`1 + c' * log(n / 2) + d' <= c' * log(n) + d'` holds because
`log(n / 2) == log(n) - 1` for every `n` at least 1, which is exact because of
how SPECIFICATION.md rounds `log`. `log` of a value of a bounded integer type
is at most the bit length of its largest value, so `O(64)` pays for `log` of
any `UInt64`.

### Loops

- **The number of iterations** of a `for` loop is the length of `yielded`,
  which its `each` bounds; that of a `while` loop is at most one more than its
  single measure's starting value.
- **Each iteration's bound is inferred, and then proven.** In the costs of the
  iterations that completed or broke, each value the loop changes is replaced
  by a bound from the facts at the head and in the body, upper where cost
  grows with it and lower where it shrinks. A wrong guess fails a proof but
  never makes one. When none is found, the error asks for a `cost` clause.
- **The prover adds the invariant** that the counter is at most its entry value
  plus the iterations so far times that bound.
- **A loop with a `cost` clause** is not bounded iteration by iteration: the
  clause is an invariant about the counter since the loop began, and after the
  loop its cost is its bound, as a call's would be.

### Amortized bounds

- **A value's potential** is its type's potential plus its parts', a function
  of the value unfolded once per value asked of, so a recursive type's is
  never unfolded forever. A growable buffer, such as a `List` seen from
  outside its package, holds the potential it saved for growing, between zero
  and its length, plus its elements' potentials. `storage_push` takes one
  amortized step paid from that saving. A view, which cannot grow, holds only
  its elements' potentials.
- **Potential is counted in the units work is counted in,** whatever its type,
  since a callee's real cost is at most `C` times its counted cost less the
  potential it leaves. So a query adds potentials of any types and counted
  work with no factor between them.
- **A method with `cost amortized time O(f)`** proves that its counted cost,
  plus the potential of its result and `mut` parameters afterward, minus the
  potential on entry of each parameter it changes or takes `own`, is within
  the bound. A parameter it only reads keeps its potential.
- **A part lent `mut` is paid for by whoever changes it:** the lending method's
  change in potential leaves the part's out, and the caller counts it.
- **A call adds its bound and subtracts the change in potential it leaves,**
  so a caller with a plain bound pays for the potential it consumed.
- **A plain and an amortized bound count on separate counters,** each with the
  callee's clause of its own kind.
- **A loop that spends or saves potential** bounds its cost so far plus the
  potential of the values it changes, a sum that telescopes. Where an
  iteration's paths join, a cost that names a potential is joined as an
  `ite`, so the potential each path changed cancels against the loop's.
- **Potentials never go below zero,** which is proven for each type from its
  invariants.

### Lambdas and function values

- **A lambda's type's cost clauses,** which can only be constants, are shown
  of its body.
- **`time(f)` for a lambda** is inferred, as a loop iteration's bound is, and
  shown only when a cost being proven uses it.
- **A function type with an `O(...)` time bound** is one unit per call, to the
  code that calls it and to the code that passes it, which must show it.
- **A quantifier in code** costs its range times its body's cost.

## Running code while proving

Some obligations are about values known when compiling, which no solver can
decide by reasoning, such as a regular expression's validity. Stage0 runs two
kinds of code while proving:

- **A call whose arguments are all known literals,** of a pure, non-generic,
  compiled function with a `time` clause reached directly, in the definition's
  package or `transparent`, is run, and its result is a fact of the query. A
  call that cannot be built, or runs past the test time limit, is left to the
  solver.
- **A tag's `from_template` clause that reads only `template.literals`** is
  run on a template of the same literal texts and no parts, for an `impl`
  that is not generic, and its answer holds for every choice of parts.

How it runs:

- **The prover and code generation do not depend on each other.** The
  evaluator is an oracle, like the solver: `Prover.diagnostics` is given a
  value of the prover's own type `Prover.evaluator`, which `stage0/evaluator`
  makes from code generation. A run's result is recorded as an oracle's
  response. A test fails if a prover library reaches a code-generation
  library, or the reverse.
- **A clause that runs true is proven, and one that runs false is an error.** A
  run that times out is an error that is not final, since the same run can
  finish on a less loaded machine.
- **A run is done again when its code changes.** Its response is recorded with
  code generation's key of everything it can reach, which is not among a
  proof's reads, so before deciding any outcome the driver reruns each run
  whose key changed. Without this, a callee's new body would leave callers
  proven by its old result, which would prove a false `ensures`.
- **This trusts compiled code,** as Lean's `native_decide` does, and each
  obligation's state says whether its proof does, so a reviewer can see which
  proofs rely on it.

## Holes

A `todo` in a theorem or a proof is the one gap a proof may have. It is
recorded as a hole, not a failure, and a build refuses a program that can
reach one.

- **A hole's goal is everything after it on its path,** since a proof cannot
  say which later obligations its steps were for, so the path ends there, as
  `assume false` would. That is sound because a hole is never in a built
  program.
- **A `todo` in code also ends its path,** so the contracts of a function whose
  body is `todo` are not checked, and contracts can be written before code.
- **An unfinished `impl`'s laws are not obligations,** but each definition that
  assumes one has a hole there.
- **Holes are not diagnostics;** each definition's outcome lists its holes.

## Diagnostics

Each obligation not proven is an error with a code for its kind, such as
`prover.overflow` or `prover.requires`, and:

- **The fact, in Truss, at the operation:** "`count + 1` may overflow `UInt8`."
- **Whether the solver found a counterexample or ran out of steps,** which
  means the fact may be true but needs help.
- **The values,** from the solver's model, written as Truss writes them: the
  parameters, the locals in scope, and `result`. These are asked for only once
  the query has a counterexample, so a query that proves is keyed by its goal.
  An agent can turn the values into a failing test.
- **The path:** each `if` the counterexample's path reaches and each arm it
  takes, asked of the same model.
- **A fix that moves the condition up as a `requires`,** where it names only
  the parameters as they arrive, constants, and literals: `count + 1` on a
  `UInt8` gives `requires count <= 254`, and an `assert` inside `if flag`
  gives `requires (flag) ==> (...)`. A fix that would change the code's
  semantics, such as a checked operation, is named, not offered.
- **A state for every obligation,** proven or not, at its position.
- **One report for one failure** with the same kind and message in a
  definition.
- **Code the prover cannot read** is `prover.unsupported`, naming the
  construct, and none of the definition's obligations count as proven.

## Incremental work

A caller reads its callee's specification, with a body only where the callee
is a function in the logic and, from another package, `transparent`, so
editing any other body makes no caller's obligations again. A definition's
outcome is a saved result of its obligations and the oracles' responses. The
driver reruns each run whose code key changed, then asks for every outcome,
sends their pending requests to the solver and evaluator together, and asks
again, which takes a round or two.

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
- a few facts about the system: each platform test gives one answer for the
  whole run, a handle's descriptor is a function of the handle, an
  environment entry has no zero byte, and a view of a built-in scalar ends
  below 2^64
- the standard library's contracts whose bodies end in an intrinsic the
  prover knows only by its type
- three facts about `intrinsic::Shared`: other tasks may update its value
  between any two calls, `copy()` is an alias of the same block, and
  `shared_key` is the block's address
- compiled code, for the checks that are run

Every test build's run-time checks test the trusted base against real
executions. `stage0/tools/proof_fuzz` mutates the documents' examples and a
file of integer functions by one token each, and runs every function of a
mutant whose obligations all prove on extremes and random values: a run that
stops at a check is a proof the prover should not have made.
`stage0/tools/proof_benchmark` times the standard library's proofs by module.

## Interfaces to other stages

- **The type checker** gives each core form, with its obligations: a
  `From_integer` conversion that must fit, a widened function value's costs,
  and an `unreachable` arm after guards.
- **The ownership check** gives the pairs of indexes and slices that must reach
  different elements.
- **Code generation** runs checks for the prover, and builds tests and
  `truss run` with run-time checks and `truss build` without them.
- **The build** refuses a package with an obligation not proven, and a program
  whose `main` reaches a hole. A dependency's proofs are the program's too,
  since the build omits the checks they replace, so `truss check` and
  `truss build` prove every project package the command's packages depend on.

## Not built

- **Reading the MIR.** The prover walks the core form.
- **Contracts for the intrinsic module's system calls.** A C function's result
  beyond its table row is known only by its type, as is the address of a view
  of any type but a built-in scalar.
- **Proofs for a 32-bit `USize`.** The prover reads `USize` and `ISize` as 64
  bits in every package, so a package that claims to run everywhere can rely
  on 64 bits and overflow on a 32-bit target. Proving at both widths needs
  the standard library's 32-bit form: `USize.maximum` and the bit operations
  on `USize` are 64-bit today. Code generation builds only for 64-bit
  targets, so no program runs at a width its proofs did not assume.
- **Facts under an assumed quantifier.** A quantifier that is a fact has no
  hypotheses from its body: stated for every value of the bound names, or
  inside the quantifier, they run the standard library's invariants over
  nested maps out of steps.
- **`span`** is not a resource yet. Its rules are `time`'s, with a `parallel`
  block's largest branch where `time` has their sum.
