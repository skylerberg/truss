# Truss Prover

This document describes stage0's prover, in
[`stage0/prover/`](stage0/prover): everything between the core form the
type checker gives each definition and the knowledge that every promise a
program makes holds. It
follows the decisions in [DESIGN.md](DESIGN.md) and [SYNTAX.md](SYNTAX.md),
reads what [TYPECHECKER.md](TYPECHECKER.md) produces, and states what
[CODEGEN.md](CODEGEN.md) relies on. `truss check` and `truss build` run it,
as [CLI.md](CLI.md) describes, and its queries run on the code database,
which [DATABASE.md](DATABASE.md) describes.

## What the prover does

The prover takes the core form of each definition, the interfaces and
contracts of its callees, and the bodies it reads as definitions. For each
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
- decides a tagged template's check by running compiled code
- reports what it could not prove, with values that break it

It does not:

- type-check or resolve names. It walks each definition's core form, in
  which every call names its callee, every operator is the call or the
  operation it means, sugar is desugared, and every type is solved. It
  reads no syntax tree.
- infer specifications. Loop invariants, measures, and contracts are
  written; the few loops whose facts are worked out alone get them from the
  contracts of the methods they call (see [Loops](#loops)).
- decide whether a test may run. Tests run as soon as the code
  type-checks, with run-time checks of every operation that could fail (see
  DESIGN.md, "Tests do not wait for proofs"). Only builds of programs wait
  for the prover.

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

A definition's body is run forward with every value a term of the logic,
and each thing that must hold where it is reached becomes an obligation,
with the facts gathered before it (see
[Verification conditions](#verification-conditions)). Each obligation is
cut down to the facts it can use, written in a canonical form, and given to
the solver (see [Queries](#queries)).

### One definition at a time, one obligation at a time

The prover works as the type checker does, through queries with traces (see
TYPECHECKER.md, "One definition at a time, through queries"), and goes one
step further:

- **A definition's obligations are a query** that reads its core form
  and, through the environment, the interfaces, contracts, definitions,
  invariants, and laws its obligations mention. Each is recorded in its
  trace. Its result is every obligation with its solver query, and not the
  answers.
- **Each obligation is a solver query of its own,** whose answer is kept
  under the hash of its canonical text (see [Queries](#queries)). Editing
  one statement changes the queries of the obligations whose paths pass
  through it, and leaves every other query's text, and so its answer,
  exactly as it was.
- **Early cutoff happens twice.** A definition that read nothing that
  changed has its obligations already. One whose obligations are made again
  asks the solver only about the queries whose text changed, since every
  other answer is found under its key.

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
| An `impl` keeps its trait's or its capability's contract | Each method of an `impl` |
| A replacement gives the provided result | Each method that replaces a provided one |
| `assert` holds | Each `assert` in a theorem or a proof |
| A specification is well defined | Each call's `requires`, index, and division in a function's `requires`, `ensures`, and cost bounds, in a loop's invariants and cost bounds, in a lending or yielding method's clauses, and in a type's invariants and potential |
| An `Integer` fits where a built-in integer is expected | Recorded by the type checker |
| Two indexes or ranges do not overlap | Recorded by the ownership check, for places lent together and for `parallel` branches |
| A `FiniteMap` literal's keys are distinct | Each `FiniteMap` literal in a specification |

An obligation names its kind, its definition, and its position within the
definition, as every result does. A test's obligations are proven like any
function's; that its run checks them too changes nothing here.

- **An index is a call.** `items[i]` reaches the `impl` of `Index` for its
  collection, whose `requires` is the bound, so every index into a `List`
  or a `Slice` is checked against `key < self.length()`. Assigning to an
  element goes through the `lends mut` index, whose contract says how the
  collection takes the element back.
- **A slice,** `items[a..b]`, must be within its collection.
- **Two places lent together** are shown to be at different indexes, each
  read as it is evaluated. Only elements of a `List`, a `Slice`, or an
  `Array` are lent together: the type checker lets no other collection lend
  two parts in one statement when either is `mut`. A slice is some elements of its collection, so
  two slices, or a slice and an index, lent together reach different
  elements too.

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
  make the two disagree. A `List` passed as a `Slice`, or a `String` as a
  `StringSlice`, is a view with the same model, and `items[a..b]` has that
  run of its collection's model.
- **Moves, drops, and copies are invisible.** A moved value is never used
  again, and a copy equals its original, so ownership adds nothing to a
  proof.
- **Capability calls return fresh values.** The prover never models an
  implementation's state. A call to `Clock.now()` gives a value about which
  only the capability method's `ensures` is known, so two calls may give
  different results. After `provide mut files { ... }`, `files` holds a
  fresh value of its type that meets its type's invariant.
- **An `any` value is known through its trait.** Only the trait's contracts
  are known of it, and making one is one allocation.
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
| `Character` | Integers up to `0x10FFFF` that are not surrogates (`0xD800` to `0xDFFF`); converting an integer into a `Character` must show it is one |
| `Float32`, `Float64` | The SMT-LIB floating-point theory, bit for bit |
| Records and sum types whose fields are visible | Algebraic datatypes, one for each type with its type arguments |
| Opaque types from another package, and types defined as `todo` | Uninterpreted sorts, known through their methods and their model |
| `Sequence`, `FiniteSet`, `FiniteMap`, `Multiset` | Uninterpreted sorts, known by their contracts, as below |
| Type parameters | Uninterpreted sorts |
| `any Trait` | An uninterpreted sort for each trait and set of associated types |
| Function types | An uninterpreted sort for each number of inputs |

- **Integers are mathematical integers.** Each value of a built-in integer
  type comes with its range as a fact, and each operation on one becomes
  an exact operation and an obligation that the result is in range, as in
  Dafny and Verus. The intrinsic module's integer operations mean what the
  compiler makes them do: arithmetic that stops the program on overflow or
  a zero divisor gives the exact result when it returns, wrapping
  arithmetic gives the exact result brought into range by a remainder,
  and the overflow tests, the comparisons, `fits`, and `convert` of a
  value that fits are exact. The standard library's integer methods each
  have a `time` clause, so `wrapping_add`, `saturating_add`,
  `checked_add`, `try_from`, and the rest are definitions their callers
  unfold.
- **An array is a sequence.** An `Array[Element, count]` is known by its
  model, which `array_model`, an intrinsic for specifications only, names:
  a `Sequence` of length `count`. A literal of one is that sequence, with
  its elements in order, built in place, so it allocates nothing. Its `at`
  says the element is the model's, so an index below `count` is within it.
  `array_view` is a view whose model is the array's, and `array_at_mut`
  lends the element at an index below `count`, which goes back into the
  array where the lend ends, as `storage_at_mut`'s does into its storage.
- **A storage and a view are sequences.** Each is known by its model, a
  `Sequence` of its elements whose length fits a `USize`, which
  `storage_model` and `view_model`, intrinsics for specifications only,
  name, so `List`, `Slice`, `String`, and `StringSlice` define `model()`
  over their buffers. Each operation reads or changes that sequence as the
  compiler makes it do: `storage_push` appends, `storage_insert` shifts
  what follows, `view_slice` is a run of its view, and `storage_lengthen`
  makes the room a C function wrote into the storage's; `compare_bytes` is
  a total lexicographic order on its views' bytes, zero exactly when they
  are the same. A C function is given only an address into a storage, so
  every storage it is lent keeps its length and its capacity; one passed
  as its room keeps its elements too, and one passed as its elements, to
  change, has elements nothing more is known of. Each function's row of
  the C library's table says how many elements it reads or writes through
  each address, and that many must be there: room after a storage's
  elements, elements of a view or of a storage it changes, or, for a view
  it reads up to a zero, a last element that is zero. A result that is not
  negative is at most the parameter the row names, and each number of the
  system, such as `PATH_MAX`, is one constant. An operation that stops
  the program on a bad index says what holds when it returns. A part
  `storage_at_mut` lends changes nothing until the lend ends, where the
  storage takes back what the caller left in it, and so for `view_at_mut`
  and a view. `storage_view_mut` is a view of the storage's elements to
  change them through, and `storage_take_view`, `view_take_view`, and
  `array_take_view` say the owner's elements from `start` are now the
  view's: the run must lie within the owner, which keeps its length (and a
  storage its capacity) and is otherwise as it was.
- **A slice passed to change** changes only its run of its owner: after
  the call, the owner is as long as it was and the same outside the run,
  and the slice read again is a view of the new run, which the callee's
  postconditions are about.
- **Bitwise operations get a second encoding.** On integers, `&`, `|`, `^`,
  `~`, and shifts are functions the solver knows only by a few facts, such
  as `0 <= a & b <= a` for unsigned values. An unsigned shift multiplies
  or divides by a power of two: `x << k` is `x * power(2, k)` where that
  fits, and `x >> k` is `x / power(2, k)`. `leading_zeros`,
  `trailing_zeros`, and `count_ones` are at most the width, and a nonzero
  unsigned `x` lies from `power(2, width - 1 - leading_zeros(x))` to before
  `power(2, width - leading_zeros(x))`. That proves the bounds most bit
  twiddling needs. When a query that mentions a bitwise operation is not
  proven that way, the prover tries it once more with each such operation
  defined exactly: as the operation on its operands' bits, of their type's
  width, read back as an integer, which the solver decides by
  bit-blasting. Verus asks for this by hand with `by (bit_vector)`; Truss
  tries both, always in the same order, and caches both answers. Only the
  bitwise operations change, not the integers, so arithmetic stays exact
  and the second query means exactly what the first does: an integer that
  is never in its type's range, which recoding every integer as a
  bit-vector would wrap, cannot make it prove something false.
- **Floats follow IEEE 754 exactly,** as DESIGN.md requires, through the
  solver's floating-point theory: literals bit for bit, and `+`, `-`, `*`,
  `/`, and negation rounding to nearest, ties to even. `==` on floats is
  `fp.eq` or both NaN, and `<` puts NaN last, which is the lawful
  comparison DESIGN.md defines. A float `%` is known only by its type.
- **Datatypes stay datatypes** within the package that can see their
  fields. Outside it, an opaque type is a sort with no structure, so a
  proof in another package can rely only on what its methods and its model
  promise, which keeps `opaque` meaningful to proofs. A datatype's variants
  and fields are in the order of their names, so reordering them in the
  code changes no query, and each field read is in its type's range.
- **Text is its bytes.** `String`, `StringSlice`, and a template's
  `Literal` are modeled by their UTF-8 bytes. A plain string literal is a
  `String` with those bytes, which costs nothing. One with interpolations
  is a new `String` known only by its type, since each part is written out
  by its `Display`. A string pattern matches text by its bytes.

### Mathematical collections

`Sequence`, `FiniteSet`, `FiniteMap`, and `Multiset` are types of
`standard::specification`, uninterpreted sorts to the solver, whose
operations are pure functions with `time` clauses and contracts written in
Truss, with `identical`, as `Sequence.append`'s
`ensures identical(result[self.length()], value)`. So they are functions in
the logic, known by those contracts, like any other function, and the
trusted base holds only the contracts, not axioms in the prover. The
solver's own theory of sequences is not used: its behavior differs between
solvers and versions, and its decision procedures are a common source of
unstable proofs.

- **A `Sequence`** has a length, indexing, `append`, `concatenate`,
  `update`, `contains`, and `sum`, which adds up a measure of each
  element: a function value that ends and uses no capabilities. Its laws
  are in the contracts of `append`, `concatenate`, and `update`, and a
  loop's `yielded` meets `append`'s, so a loop's cost can be a sum of what
  its iterations spend.
- **A `FiniteSet` and a `FiniteMap`** have membership, a size, inserting,
  and, for a map, the value under each key and its keys; a set can also
  remove. A `Multiset` has a count of each value so far.
- **Extensionality,** that two sequences with the same length and
  elements are identical, is the one fact contracts cannot state, since a
  contract describes a result, so it is an axiom of the prover's, and so
  are its kin for a set, by what it contains, and a map, by its keys and
  their values. Each is stated for each two values that `identical`
  compares, rather than for every two, which would have the solver
  compare every pair it knows.
- **A literal** of an array or a `Sequence` is a value whose sequence, the
  array's model or the sequence itself, has the literal's length and
  elements. A `FiniteMap` literal holds each key's value and no other key,
  and a `FiniteSet` literal contains what it lists and nothing else. A
  literal of a `List`, a `Set`, or a `Map` is desugared to the calls that
  build it, so it is known through their contracts: a map literal's keys
  must be distinct because `Map.insert_absent` requires it.
- **`identical(a, b)`** is the solver's equality, for every type.
- **Each type's `model()`** is a function from its sort to its model's,
  known through the contracts of the type's methods. That is how code
  reasons about a `List` or a `Slice`, whose contracts are stated through
  their sequences, and about a `Set` or a `Map`, through their `FiniteSet`
  and `FiniteMap`: a pushed element's index and value follow from
  `List.push`'s contract.

### Equality

- **Structural equality is the solver's equality.** For a type with
  structural equality (see DESIGN.md, "Equality, ordering, and deriving"),
  `a == b` is the solver's `=`, which the solver substitutes through
  everywhere.
- **Every other `==`, and each ordering, is a function of its operands,**
  with the laws of `Equal` and `Ordered` as facts. `Equal` and `Ordered`
  use no capabilities, so a comparison always gives the same answer, which
  is what their laws are about. From `a == b` the prover concludes only
  what those laws and the type's contracts give. An arithmetic operator on
  a type that is not built in is a call of its trait's method.
- **A derived `Equal` that is not structural** is defined field by field
  with each field's own `==`, unfolded once for each two values compared,
  so a `Point` of floats is equal exactly when its coordinates are, by the
  lawful float comparison.
- **Every other derived method is its derived body.** A derived `compare`
  orders by variant and then field by field, and a derived `hash` or
  `default` is what the derivation writes, so each is pure and functional,
  and its body is its definition, as any such function's is.

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
  function with a `time` clause, which changes none of its arguments, is a
  function in the logic, applied to its arguments, wherever it is called,
  in code as in specifications, so `let sorted = is_sorted(items)` and
  `ensures is_sorted(items)` mean the same term. An `impl`'s method has a
  `time` clause when its trait's method does, since it keeps the trait's.
- **Its contract is known at each call.** Where a call's arguments meet the
  `requires`, the `ensures` holds of its result. That is sound because the
  function terminates, and is defined, wherever the `requires` holds.
- **A functional body is a definition,** unfolded at each call: where the
  `requires` holds, the call's result is the body's value. A body that
  reads what the prover cannot, such as an opaque type's fields from
  another package, is not unfolded, and the function is known by its
  contract alone.
- **Recursive definitions unfold once per use.** A definition that
  unfolded itself forever would never be finished, so a call to a function
  inside its own unfolding is left as the function applied to its
  arguments. Each use unfolds one level, as fuel does in Dafny, and a proof
  that needs more calls a theorem or asserts the steps between. A
  definition that is not recursive unfolds as deep as it goes.
- **Every other function is a fresh result.** A call to a function that is
  not pure, or has no `time` clause, gives a new value about which its
  `ensures` is known, and two calls are not known to agree.
- **A function value is a value of the logic.** A call through a value
  whose function type has a `time` clause, uses no capabilities, and
  changes none of its arguments is the value applied to its arguments, so
  two calls with the same arguments agree. A call through any other
  function value gives a fresh result.
- **Applied, a function value is what it names.** A pure function named
  as a value is that function applied, or its body where its definition
  holds for every argument. A lambda with a functional body is its body
  applied to its arguments, and two lambdas with the same body over the
  same captured values are the same value, so a bound and a loop's bound
  that both write `fn(row) { row.length() }` mean the same sum. A lambda
  is proven where it is written, with fresh arguments, and must end
  exactly when its function type has a `time` clause.
- **A lambda passed where a parameter's type has a `requires`** is
  checked with that `requires` assumed of its arguments, with the call's
  arguments in place of the callee's parameters. In
  `indices.map(fn(i) { values[i] })`, the lambda knows
  `indices.model().contains(i)`, and the caller's facts about `indices` do
  the rest. A call through such a parameter, in the callee's body, asserts
  the `requires` of its arguments.
- **A named function passed for such a parameter** must accept every
  argument the parameter's type promises it, and keep the type's cost
  clauses.

Callers' proofs depend on whether a body is a definition, and on the body
itself when it is. Both are in the trace of every proof that used the
definition, and pruning (see [Queries](#queries)) keeps a definition out of
the queries that do not need it, so editing the body of `is_sorted`
re-proves only the queries that unfolded it.

## Verification conditions

### Running a body forward

The prover walks each checked body forward, taking steps of four kinds:

| Step | Meaning |
|---|---|
| `x := term` | A new version of a local or a place |
| `havoc x` | `x` takes any value of its sort, such as a `mut` argument after a call |
| `assume fact` | The rest of the path may rely on `fact` |
| `assert fact, obligation` | `fact` must hold here; the rest of the path may rely on it |

These are the statements of Boogie, the intermediate language behind Dafny,
and of Why3's, cut down to what Truss needs. The walk is in the passive form
of Flanagan and Saxe ("Avoiding Exponential Explosion", 2001): every value
is a term, every fact is guarded by the condition of the path it holds on,
and where paths join, each local that differs gets a fresh symbol that each
path defines. So what a body gives its queries grows with the body, not
with its number of paths. No step goes around a loop: each loop is cut at
its head by its invariant, as below. The right side of `&&`, `||`, or
`==>` runs on only one path, so when it changes a local, as a call with a
`mut` argument does, that path joins the one where it did not run, as the
two arms of an `if` do.

An `assert` makes one query: the facts gathered before it, and its fact as
the goal, guarded by its path. Once made, it is a fact for the rest of the
body, since its own query proves it. Code the prover cannot read soundly
stops the walk, and none of the definition's obligations count as proven
(see [Diagnostics](#diagnostics)): an obligation is never assumed because
the prover could not read the code around it.

### Calls

A call becomes:

1. `assert` each `requires`, with the arguments in place of the parameters
2. for each `mut` argument, `havoc` it, keeping its old value for `old`
3. the result is a fresh value, or the function symbol applied to the
   arguments when the function is one in the logic
4. `assume` each `ensures`, where the `requires` held, and each type
   invariant of the result and of each `mut` argument

A callee's clauses are read with the call's type arguments. A call the type
checker resolved to an `impl` reads the `impl`'s clauses with its trait's,
and the `impl`'s own `requires` when it states any. A call through a bound
or through `any` reads the trait's, and a call through a bound on `Self`,
read where `Self` is a known type, reaches that type's `impl`. A capability
call uses the capability method's contract.

- **A tagged template is a call** of its tag's `from_template` with the
  template: its literal texts, each a `Literal` whose model is its bytes,
  and its parts, each turned into the tag's `Part` by its `From`. The
  tag's `requires` is shown of that template, from what the prover knows
  of its text, or by [running it](#running-code-while-proving).
- **A call whose callee's contract cannot be read,** such as one with
  errors, gives a value known only by its type's range. So does a call of
  an intrinsic, and building a type whose fields the package cannot see:
  sound, but it proves little.

### Loops

- **A `while` loop** is cut at its head. Its invariants are asserted on
  entry, every place the body may change is havocked, the invariants are
  assumed, and the body runs once from there, after which the invariants
  are asserted again. The places a body may change are the locals, or
  `self`, that it assigns to, passes `mut`, or loops over `mut`, so nothing
  else loses what was known about it.
- **A `for` loop** is the same, with what the `each` it calls promises. A
  ghost sequence, `yielded`, holds what the earlier iterations received.
  At the head, the loop's invariants and the method's clauses that hold
  where it may end are assumed of `yielded`. Each iteration either takes a
  fresh value meeting the method's clauses for each `yield`, runs the body,
  and appends the value, as the body left it, to `yielded`, or leaves with
  `finished` true. A `break` leaves with `finished` false.
- **`yielded` in a loop's clauses** names what the nearest loop or method
  hands out: a `for` loop's own parts, which for a range are its indexes so
  far, or else, in a lending or yielding method, what the method has handed
  out.
- **A range of integers is the one loop the prover knows itself.** In
  `for i in 0..count`, `i` starts at the range's start, each iteration has
  the next index, and `i < count`.
- **Nothing else about loops is built in.** A loop over a list runs once
  per element because `List.each` promises
  `ensures finished ==> yielded.length() == self.length()`. A user's
  collection whose `each` promises the same gets the same facts.

### Lending and yielding methods

- **In the method's own body,** each `yield` asserts the clauses that
  mention `result`, with the part as `result`. For a `mut` part, the part
  then takes a fresh value that meets its type invariant, since the caller
  may have changed it, which is stored back into its place, through a
  collection's `lends mut` index for an element, and the part is appended
  to `yielded`. In a yielding method, each `yield` also asserts the clauses
  that hold where the method ends, with `finished` false, and the invariant
  of `self`, since a loop may stop there. At the end of the body, those
  clauses are asserted with `finished` true.
- **At a call to a lending method,** the caller's statement gets the part,
  about which the clauses that mention `result` are known. When the
  statement is done with it, `self` is havocked, and the clauses that hold
  where the method ends are assumed, with `yielded` holding the part as the
  statement left it. This is how `mut grid.cell(position).visit()` is known
  to change exactly the one cell.
- **A pulled cursor** is what a yielding method called outside a `for`
  loop makes. The call meets the method's `requires` and spends its whole
  cost there. The cursor carries what it has handed out, `yielded`, and
  whether it has ended, as ghost parts of its value. `next()` gives `Some`
  of a value that meets the method's clauses for each `yield`, or `None`,
  after which the method's other clauses hold with `finished` true. A
  `for` loop over a cursor pulls it so, with `yielded` everything the
  cursor has handed out.
- **A loop over a value of a type's own `Cursor`** calls its `next` by the
  `impl`'s contract until `None`. Such a cursor promises no end, so in a
  function that must end the loop needs a `decreases` clause, which each
  iteration, its pull included, decreases.

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
- **Validity is not computed twice for one type on one path.** A type can
  contain itself through a type that has an invariant. `type Tree = Leaf |
  Branch(children: Map[String, Tree])` does: `Map`'s invariant calls
  functions on its entries, the prover assumes each entry is valid, and an
  entry holds a `Tree`. While the prover is computing the validity of a
  type, a nested request for the validity of the same type is `true`. The
  same rule already applied to a type that contains itself directly in a
  field.
- **Another package's opaque type** has a validity that is a predicate the
  prover never unfolds there: a value of the type comes from its own
  package, which shows the invariant, so elsewhere validity is assumed
  where a value arrives and shown where one leaves, which the facts it
  arrived with already do.

### Specifications

A function's `requires` and `ensures`, and a loop's invariants, are checked
to be well defined where they are shown, as Dafny checks its expressions:
each call in one meets its callee's `requires`, each index is in bounds,
and each division has a nonzero divisor, reading `&&`, `||`, `==>`, and
`if` from left to right, so the right side may rely on the left. A
`requires` is checked with the `requires` before it, an `ensures` with
every `requires` and the `ensures` before it, and a loop's invariant with
the invariants before it. Inside a quantifier, these are checked for each
value its range admits, so `forall i in 0..items.length() => items[i] > 0`
is well defined and `forall i in 0..items.length() + 1 => items[i] > 0` is
not.

- **Arithmetic is exact** on `Integer`, and an `Integer` passed where a
  built-in integer is expected carries the type checker's obligation that
  it fits.
- **`old(e)`** is `e` evaluated in the versions of the parameters on entry.
- **A quantifier over a range or a collection** is a quantifier whose bound
  name is limited to it: `forall i in 0..count => p` is "for every integer
  `i` with `0 <= i < count`, `p`". Over a list or a sequence it ranges over
  the indexes of the model, and over a set, over what the set contains.
- **A quantifier over every value of a type** has each value in its type's
  range and meeting its type's invariants.
- **A quantifier in code** is read as one in a specification is.

### Proofs

- **A theorem is proven like a function** that returns nothing: its
  `requires` are assumed, its body runs, and its `ensures` are asserted.
  A call to a theorem asserts its `requires` and assumes its `ensures`.
  A theorem that calls itself is a proof by induction, which its
  `decreases` makes sound.
- **A `proof` block's statements** are walked at that point and nowhere
  else. Its calls and `assert`s add facts for the obligations after it.
  Codegen never sees it.
- **`assert`** in a theorem or a proof is an obligation, and a fact for the
  rest of the path. In a test it is assumed, since the test's run checks
  it.
- **A law** of a trait, or of a trait it requires, is a fact, quantified
  over its parameters, wherever the trait's methods are used on a type that
  implements it: for a type parameter bounded by the trait, and for a
  concrete type whose `impl`'s laws are proven. Each hand-written `impl`
  must prove each law, under the code `prover.law`, from the `impl`'s
  method contracts and definitions and the body of its `proof` definition,
  if there is one. A law's own proof never uses that law.
- **A derived `Equal`** is the solver's equality, or its definition field
  by field, as [Equality](#equality) says. Nothing is proven for a derived
  implementation, as DESIGN.md says.
- **An `impl`'s method keeps its trait's or its capability's contract.**
  The trait's or capability's `requires` is assumed and must imply the
  method's own, and its `ensures` is shown at each way the method returns,
  since calls through a bound, or of the capability, rely on them. A
  capability's method takes no `self`, so the `impl`'s `self` is left out
  when their parameters are paired. The method's own `ensures` and cost
  clauses are shown as a function's are.
- **A trait's provided body** is proven once, against the trait's clauses,
  with `Self` a type parameter bounded by the trait, so every `impl` that
  keeps it keeps them. A loop over `Self`'s own yielding method reads the
  method's contract and `time` clause through the bound.
- **A method that replaces a provided one** proves that its result equals
  the provided body, which is a definition, with the trait's `requires`
  assumed.

## Queries

### One query per obligation

Each obligation gets a query of its own: the facts on the paths that reach
it, the obligations before it on those paths, which are assumed since each
is proven by its own query, the facts of the functions and types it
mentions, and the negation of the obligation. The solver proves the
obligation by finding no way to satisfy the query. Dafny's
`--isolate-assertions` and Verus's `spinoff_prover` do the same for
stability: a small query is answered quickly and the same way every time,
while one query for a whole function can fail because of an unrelated part
of it.

### Pruning

A query holds only the facts that can matter to it. Starting from the
symbols of the obligation, each fact that mentions one of them is kept,
with its symbols, until nothing more is added. A quantified fact waits
until every symbol of one of its triggers is kept, since the solver uses
it only where terms of that shape are; this also keeps quantifiers out of
queries that do not need them. Dropping a fact is always sound, and a fact about
symbols the obligation never reaches cannot help to prove it. A change to a function that no kept fact mentions leaves the
query's text, and so its kept answer, alone.

### Triggers

A quantified fact helps the solver only when it knows when to use it,
which SMT solvers decide by triggers: terms that, when they appear, make
the solver use the fact for them. Truss has no syntax for triggers, so the
prover chooses them, as Dafny does, and states them in the query:

- **A trigger is a set of applications** of the query's own functions,
  including a datatype's constructors and fields, that together name every
  bound name. A bound name may appear only as an argument, never under
  arithmetic, since the solver matches a trigger by its shape: `items[i]`
  is a trigger and `items[i + 1]` is not.
- **The smallest terms are chosen.** An application that contains another
  naming the same bound names is left out for the smaller one, and a
  single application naming every bound name is preferred to a set.
- **Matching loops are avoided.** An application that the fact's own body
  would match with a larger term, as `f(i)` matches `f(i + 1)` in
  `forall i => f(i) < f(i + 1)`, would make each use of the fact give the
  term for another, without end, so it is left out when anything else is
  left.
- **A definition triggers on what it defines.** An equation whose left
  side is an application naming every bound name, such as a lambda's
  definition, is triggered by its left side alone.

When no trigger is found, the query states none and the solver chooses its
own.

A value made inside a quantifier, such as a call's result, is a function of
the quantifier's bound names in the logic, since it can differ for each of
their values: `forall i in 0..items.length() => same(items[i]) == items[i]`
is about one result for each `i`, not one result for all of them.

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

- **Z3, pinned,** as Dafny, Verus, and F* use. Another version is refused,
  since its answers could differ, and the version is part of every
  answer's key.
- **A fixed limit in steps.** Each query runs with the same `rlimit`, which
  counts the solver's work, not time, so a slow machine never fails a proof
  a fast one passes. The limit is set by the prover's version, not by the
  project or the code, so a proof that passes anywhere passes everywhere. A
  proof that needs more help gets it from a `proof` block or a theorem.
- **One process per query,** given the query's text through SMT-LIB, with a
  fixed random seed. A solver that answered earlier queries carries state
  that can change later answers, so no state is shared.
- **An answer is a fact about the text.** Its key is the hash of the
  query's text, the solver's version, its options, and its limit, so an
  answer can be reused whenever the text is the same. The command line
  keeps answers in the store, one file for each key, so a query solved
  once on a machine is not solved there again.

## Termination

Each package's call graph is a query of its own, with its trace, since a
cycle can only be seen across definitions:

- **Edges are every way a function can reach another:** a call, naming a
  function as a value, and, inside an `impl`'s methods, using that `impl`,
  as DESIGN.md's [Termination](DESIGN.md#termination) describes. An `impl`
  used where a bound needs it is an edge from the code that uses it to every
  method of that `impl`.
- **Cycles cannot cross packages.** Packages do not depend on each other in
  a cycle, and a function in one package reaches another package's
  functions only through what code in the first package names, so every
  cycle lies within one package's graph.
- **Each edge in a cycle through a function with a `time` clause, or
  through a theorem, is an obligation:** the callee's measure, with the
  call's arguments, is smaller than the caller's. A measure is the
  `decreases` clause, compared in order, where each `Integer` stays at or
  above zero. Without one, a direct recursive call must be structural: an
  argument is a part of the caller's argument, compared in the parameters'
  order.
- **Parts are ordered.** Each field read is below the value it is read
  from, in an order of ranks, as Dafny orders its datatypes. An element of
  a sequence is below the sequence, and a value's model is no higher than
  the value, so an element of a field's `List` is below the value too:
  recursion over a tree whose children are a list ends without a
  `decreases`. The order is stated only in a function that can call itself
  again with no `decreases`, the one place it is used.
- **Every call from a function with a `time` clause** must reach something
  with one, or the function may not end.
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

The prover adds a ghost counter for each resource that has a cost clause:

| Resource | Counts |
|---|---|
| `time` | One for each call and each iteration of a loop, plus each callee's own `time` |
| `allocations` | Each allocation, and each callee's `allocations` |
| `allocated_bytes` | The bytes of each allocation, and each callee's `allocated_bytes` |
| `calls(target)` | Each call to the target, and each callee's count for it |

- **A specification spends nothing.** A `requires`, an `ensures`, an
  invariant, or a bound never runs, so what it calls is not counted.
- **A counter is an `Integer` on each path,** increased at each call and
  each iteration, so costs are proven by the same verification conditions
  as everything else. Where paths join, a counter is what the path taken
  spent.
- **A callee's cost is what its cost clause promises,** never what its body
  does, as DESIGN.md requires, read with its parameters as they were passed
  and with `result`. A callee with no clause about a resource may spend any
  amount of it, so a bound that depends on it cannot be proven.
- **The steps between calls and iterations are not counted one by one.**
  Between two of them, a body runs a fixed number of primitive operations,
  at most its own length, so counting them changes only a constant, which
  an `O(...)` bound's constants absorb. A `time` bound is always
  asymptotic, so nothing is lost.
- **Allocations are counted where DESIGN.md says they happen:** building an
  `indirect` variant is one allocation, of a fixed size that is not known
  to the prover, and so is any callee's allocation.
- **The intrinsic module's operations** each take a fixed number of steps,
  steps in proportion to a buffer's length, or are known by no bound, as
  the compiler declares them: arithmetic, reading or swapping in place, and
  making a storage with room for some elements are the first kind;
  inserting into or removing from a storage, giving a storage a new
  capacity, and comparing runs of bytes, the second; running a test and
  reaching the system the third. Making a storage, giving it a new
  capacity, running a test, and reaching the system may allocate; nothing
  else does.
- **A `calls(target)` counter** counts each call through a function value
  or of a capability's method. A callee that is passed the function value,
  or uses the capability, counts what its own `calls` clause about it says;
  one that can reach neither counts nothing; and one passed a lambda that
  captures the function value is known by no bound.

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
   arguments, or 1 where `g` is below zero, each step as 1, and each call
   through a function value `visit` as `time(visit)`, which is at least 1,
   and 1 when its type has an `O(...)` bound. A call of a trait's method
   that promises only that it ends, as `Equal.equal` does, is counted as
   `time(T.method)` for the type `T` it is called on: the longest any one
   call of it takes in the run, a constant of the run, which a bound states
   as `time(Element.equal)`. It is one term for each method and type, so a
   callee's bound and its caller's are about the same term. Every callee's real cost is at
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
that proves termination. Functions that call each other in a cycle each
assume the others' bounds with their own constants, which is sound only if
all of them are proven with the same pair, so each of them tries only the
first. The constants are two symbols in the queries; every query of a
definition that mentions them is asked with the same pair, and the first
pair that proves all of them is taken. So binary search's
`1 + c' * log(n / 2) + d' <= c' * log(n) + d'` holds because
`log(n / 2) == log(n) - 1` for every `n` at least 1, one of the facts the
prover gives the solver about `log`. That fact is exact because DESIGN.md
rounds `log(n)` as it does. `log` of a number is its bit length, `power`
of two numbers is their power, and `log` of a value of a bounded integer
type is at most the bit length of the type's largest value, so a bound of
`O(64)` can pay for `log` of any `UInt64`. A tree's `O(size)` walk needs `c' > d'`, and
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
- **The bound on one iteration is worked out, and then shown.** From what
  the iterations that ended, or were left by `break`, spent, each value the
  loop changes or makes is replaced by a bound on it from the facts at the
  head and in the body: an upper bound where the cost grows with it, and a
  lower bound where it shrinks, and a choice between paths by the larger
  of them. The result is a guess, and every iteration is shown to spend no
  more than it, so a wrong guess fails a proof but never makes one. When no
  bound is found, the error says to give the loop a `cost` clause.
- **The iterations are bounded where the loop is left.** A ghost count of
  them is kept: for a range, the `n`th iteration has the index
  `start + n`, so the count ends at the range's length; for an `each`, it
  is the length of `yielded`, which the method's clauses bound; and for a
  `while` loop with one measure, which every iteration shows to start at or
  above zero and to decrease, a ghost for the measure where the latest
  iteration began keeps the count within one more than the measure on
  entry.

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
  potentials of its parts, as DESIGN.md defines it. In the logic it is a
  function of the value, whose definition is unfolded once for each value
  it is asked of, so a recursive type's potential is never unfolded
  forever. A growable buffer, a storage or a type whose model is the
  sequence of the storage it holds, such as a `List` or a `String`, holds
  what it saved for growing, which is between zero and its length, and the
  sum of its elements' potentials over its model, as `Sequence.sum` gives
  it. `storage_push` takes one step, amortized, paid out of that saving, so
  pushing `count` times costs `O(count + items.length())`. A view, or a
  type whose model is the view it holds, such as a `Slice`, cannot grow,
  so it holds only the sum of its elements' potentials.
- **Potential is counted in a unit of its type's own,** one unknown constant
  for each type with a potential, the same for every method of the type, so
  that potential saved by one method pays for another's work. Since every
  method of the type counts in that one unit, a query adds potential and
  counted work as they are, with no factor between them.
- **A method with `cost amortized time O(f)`** proves that its counted cost,
  plus the potential of what it returns and of each `mut` parameter
  afterward, minus the potential on entry of each parameter it changes or
  takes `own`, is within the bound. A parameter it only reads keeps its
  potential, so the method cannot spend it.
- **A call to one** adds its bound to the caller's counter and subtracts the
  change in potential of what it changed, so a caller with a plain bound
  pays for the potential it consumed from what it was given: a function
  that pushes `count` times can promise `O(count + items.length())`.
- **A loop that spends or saves potential** is bounded by what it has spent
  plus the potential the values it changes hold, which is what telescopes:
  each iteration's bound is on what it spends plus the growth of that
  potential, so potential saved by one iteration pays for the next one's
  work, and where the loop is left, what was spent is within the bound
  plus the potential on entry, less what is left.
- **Potentials never go below zero,** which is proven for each type with
  one, from its invariants, and is a fact about every value that meets its
  type's invariants. A type parameter may hold potential, which is not
  known.

### Lambdas and function values

- **A lambda counts on its own.** Its type's cost clauses, which can only
  be constants since a function type's inputs have no names, are shown of
  its body like a function's.
- **`time(f)` for a lambda** is a bound on one call of it, worked out as a
  loop's iteration is, from the values around the lambda, and shown of
  each way its body ends only when a cost the prover is showing uses it.
- **A function type with an `O(...)` time bound** is one unit per call, to
  the code that calls it and to the code that passes it, which must then
  show it.
- **A function named as a value** is one unit of time per call when its
  own `time` is a constant.
- **A quantifier in code** spends its range times what its body spends.

## Running code while proving

Some obligations are about values known when compiling. The check of a
tagged template, `requires is_valid_pattern(template.literals)`, applies a
function to literal text, which no solver can decide by reasoning about a
regular-expression parser. Stage0 runs two kinds of code while proving.

- **A call whose arguments are all known:** a pure function with a `time`
  clause, compiled rather than for specifications only, not generic,
  reached directly rather than through a bound, with every argument an
  integer or `Bool` literal and a result of one of those. Each such call a
  query mentions is run, as a `Call_evaluation` instance (see CODEGEN.md,
  "Code run while compiling"), and its result is a fact of the query, so
  `count_up(7)` is known to be `7` though nothing in `count_up`'s contract
  says so. A call that cannot be built, or runs past the test time limit,
  is left as the solver knows it.

It also decides a tagged template's checks by running them, as
[Tagged templates](DESIGN.md#tagged-templates) intends:

- **A clause of a tag's `from_template` that reads its template only as
  `template.literals`** is decided by running it, for an `impl` that is not
  generic. A template's parts are values known only at run time, and such
  a clause cannot see them, so it is run on a template of the same literal
  texts and no parts, which gives what it gives for every parts. Any other
  clause is proven by the solver from what the prover knows of the
  template.
- **Code generation runs it**, as a `Template_check` instance (see
  CODEGEN.md, "Code run while compiling"): each clause that can run is
  worked out and written out. A clause that cannot run, such as one that
  calls a function for specifications only, is left to the solver.
- **The prover does not depend on code generation.** `Prover.diagnostics`
  is given the running, and `truss check` gives it through the compiler it
  builds programs with, made only when a template asks for it. So proofs
  stay queries of their own, and what ran is decided only when obligations
  are asked, as the solver's answers are.
- **A clause that runs true is proven, and one that runs false is an
  error** that says so. A run past the test time limit is an error that
  says the check is not known.
- **This trusts compiled code.** A fact from running code is only as true as
  code generation and the C compiler, which is what Lean's `native_decide`
  trusts too. It is the price of a check that no solver could make.

## Holes

A `todo` in a theorem, a `proof` block, or a `proof` definition is the one
gap a proof may have, as DESIGN.md says. What it was to prove is not a
failure: the `todo` is recorded as a hole, with its position, so the tools
can list it as a task. A build of a program refuses one that can reach a
hole, as it refuses one that can reach a `todo` in code. Tests run
regardless, with their run-time checks.

- **What a hole was to prove is everything after it on its path.** A proof
  cannot say which later obligations its steps were for, so the path
  through a hole ends there for the prover, as an `assume false` would,
  and the obligations after it hold trivially. That is sound because a
  hole is never in a program that is built.
- **A `todo` in code also ends its path.** The contracts of a function
  whose body is `todo` are not checked against the body, and none of them
  is reported. DESIGN.md has a package's signatures and contracts written
  before its code. A `todo` in the middle of a body leaves the obligations
  before it checked, and skips the ones after it on that path. It is not
  recorded as a hole, because `truss holes` already lists every `todo`.
- **An `impl`'s laws are skipped while the `impl` is unfinished.** A law
  constrains what the `impl`'s methods return. If a method the `impl`
  defines contains a `todo`, the laws of that `impl` are not obligations.
- **Holes are not errors.** Truss has no warnings, so a hole is not a
  diagnostic: each definition's outcome lists its holes, `truss holes`
  lists every `todo` with what it blocks, and `truss build` refuses a
  program whose `main` can reach a definition with a hole in its proofs.

## Diagnostics

Each obligation the prover could not prove is an error, with the shared
`Diagnostic` type from LEXER.md, a code for its kind of obligation, such as
`prover.overflow`, `prover.requires`, `prover.ensures`, `prover.invariant`,
`prover.termination`, and `prover.cost`, and:

- **What could not be shown,** written in Truss, pointing at the operation:
  "`count + 1` may overflow `UInt8`."
- **Whether the solver found a counterexample or ran out of steps.** A
  counterexample means the fact can be false on some path. Running out of
  steps means it may be true but needs help, and the message says so.
- **The values.** With a counterexample, the solver's model gives the
  values of the definition's parameters, written as Truss writes them:
  "For example, when `count` is 255." A float is the shortest decimal that
  reads back as the same bits, and a record or a variant is its name with
  its fields. An agent can turn these values into a test, which then fails
  at its run-time check if the code is wrong.
- **Code the prover cannot read** is an error of its own,
  `prover.unsupported`, that says what stopped it, and none of the
  definition's obligations count as proven.

## Incremental work

A definition's obligations are made again when something they read
changed, as DATABASE.md describes for every query. The solver is asked
again only about a query whose text changed:

| Edit | Solved again |
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
| A new solver version, or a new limit | Everything, once, through each answer's key |

## The trusted base

A proof is as trustworthy as:

- the solver, and the prover's translation into its logic
- the facts the prover states itself: that the mathematical collections
  are extensional, what `log` and `power` are, the few facts about bitwise
  operations, and what a derived `Equal` means
- the contracts of `standard::specification`, which say what the
  mathematical collections are, so its definitions are not proven
- what the prover knows of the intrinsic module's integer operations, its
  storage and views, and reading and writing bytes, and the costs the
  compiler declares for each intrinsic
- the standard library's contracts whose bodies end in any other
  intrinsic, which the prover knows only by its type, so they are relied
  on and not proven
- compiled code, for the checks that are run

Everything else is proven. The run-time checks of every test build, and
sanitized runs, test the trusted base against real executions.

## Interfaces to other stages

- **The type checker** gives the core form of each definition and its
  interface, as TYPECHECKER.md describes. What the checker leaves the
  prover to show is in the form's nodes: a `From_integer` conversion must
  fit its type, a widened function value's costs must imply the expected
  ones, and a `match` whose guards must be exhaustive ends in an
  `unreachable` arm. A node's origin finds the source text a diagnostic
  quotes.
- **The ownership check** gives the pairs of indexes and slices that must
  reach different elements, by the bracket each is written with.
- **Code generation** runs a tagged template's checks for the prover. It
  builds tests and `truss run` with run-time checks of what the prover
  proves, and `truss build` without them, as CODEGEN.md describes.
- **The build** refuses a package with an obligation that is not proven,
  and a program whose `main` can reach a hole in a proof.

## Not built

- **Contracts for the intrinsic module's floats and system calls.** Only
  the integer operations, storage, views, and what a C function keeps of
  the storages it is lent have meanings. A call of any other intrinsic, and
  what a C function returns beyond the counts `read`, `write`, and
  `snprintf` give, is known only by its type, and what the standard library states no contract for, such as
  the `ieee_` comparisons, is known only by its type.
- **Facts under a quantifier.** A fact that names a quantifier's bound
  name, such as what a callee's `ensures` says of a call on it, is not
  kept. Closed over the quantifier it would be true, but the standard
  library's maps state nested quantifiers over calls, each call's facts
  are about values made for every combination of bound names, and with
  them the solver runs out of steps even with triggers chosen.
- **A diagnostic for a quantifier with no trigger.** When no set of
  applications names every bound name, the solver chooses its own
  triggers; the prover does not yet say so where a proof needed such a
  fact.
- **A function value's contract in the logic.** A lambda whose body is not
  functional, or a named function with a `requires`, is applied as a
  function the solver knows nothing more about, so a contract such as
  `List.map`'s `ensures result[i] == transform(self[i])` gives the caller
  facts about its own lambda only when the lambda's body is functional.
- **The potential of a set's or a map's elements.** A value's potential is
  to include that of the elements of a `Set` or a `Map` it holds, through
  its model, as it does for a collection modeled by a sequence. The
  specification module has no sum over a finite set or map, so a
  potential that needs one is reported as one the prover cannot read.
- **Code the prover cannot read yet.** Among what is reported as
  `prover.unsupported`: a loop over a cursor that is not in a local, and a
  string pattern with a tag or interpolations.
- **More in a diagnostic.** A note at the clause an obligation comes from,
  the branches a counterexample's path takes, listed by position, the
  values of locals, and a fix that adds an obligation about parameters
  alone to the function as a `requires`. DESIGN.md's other fixes, checking
  it with an `if`, using the checked version of the operation, and
  `uses Panic`, change what the code means, so the message is to name them
  without applying them. An obligation that the same failure makes
  unprovable on another path, such as a second index into the same list
  with the same index, is to be reported once.
- **Solving many queries at once,** one for each core. They are solved one
  after another.
- **Proof programs as a data structure of their own,** made from a body
  and then turned into verification conditions by weakest preconditions,
  which would keep reading Truss apart from the logic. One walk does both.
- **Proof states in the language server:** each obligation's state at its
  position, and the counterexample of each one that failed.
- **A fuzzer of proofs, and a benchmark of solving.** The fuzzer is to
  mutate the documents' examples and check that no obligation the prover
  proves fails its run-time check when the mutated program runs. The
  benchmark is to time solving over the standard library.
- **Turning off a definition** is not decided. Dafny and Verus can hide a
  body from the solver, which keeps large definitions from slowing queries
  that do not need them. Pruning may be enough; if not, a way to say so is
  needed.
- **The limit in steps** is not settled. Its value, and whether it should
  grow with the size of a query, are to be set by measuring the standard
  library's proofs.
- **Contracts for concurrency** are not designed. Tasks and channels are
  capabilities, so their contracts are what code can rely on, but what
  those contracts should say about ordering is not decided.
