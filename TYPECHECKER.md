# Truss Type Checker

The stage0 type checker covers every step between the parser's syntax trees
([PARSER.md](PARSER.md)) and the core form that the prover
([PROVER.md](PROVER.md)) and code generation ([CODEGEN.md](CODEGEN.md))
read. It checks the rules of [SPECIFICATION.md](SPECIFICATION.md), and its
queries run on the code database ([DATABASE.md](DATABASE.md)).

For each definition it produces four results:

- a *resolved form*: the referent of every name
- an *interface*: the part other definitions depend on
- a *core form*: the desugared, fully typed definition, which every later
  check, the prover, and code generation read
- *tables* by syntax node: each expression's type, each name's resolution,
  and each call's callee, which tools read

It proves nothing. Every fact that needs the solver, such as an index in
bounds or a `requires` at a call, goes to the prover. It runs no code, and
decides no layout or drop.

## Structure

```text
syntax tree ──▶ Resolve ──▶ Interface ──▶ Body ──▶ core form, tables
   (per definition)  │            │             │
                     └─────▶ diagnostics ◀──────┘
                                  ▲
        Package checks ───────────┘   (impls, cycles, instantiation)
```

- **The checker reads another definition only through a query.** Checking a
  body demands its callees' interfaces, never their bodies.
- **Each query belongs to one phase** and reads only its own and earlier
  phases: trees, declarations, resolution, interfaces, bodies, package-wide
  rules, and diagnostics.
- **The design rules out most cycles between queries.** A signature depends
  only on signatures and shapes, so mutual recursion between functions makes
  no cycle. Each real cycle has a rule: constants that refer to each other,
  mutually recursive types, and traits that require each other.
- **Every result is canonical.** No result is built by iterating a hash
  table, and no inference variable remains in a stored result, so early
  cutoff compares results reliably.

**Later stages record their decisions in tables keyed by node id,** never in
a rebuilt tree. A tree parameterized by its annotations would be stored once
more for each stage. Ids are relative to the definition, so a definition
that only moved keeps every table valid. rustc identifies nodes the same
way. A method is a definition of its own wherever it is written, so an edit
to one method of an `impl` re-checks only that method.

## Name resolution

- **Names are in four namespaces,** told apart by the case rules and by `::`
  and `.`: modules, types, values, and members.
- **An unqualified name** is looked up among the locals, the generic
  parameters, the file's definitions, then the prelude. At most one matches,
  because shadowing is an error.
- **A member is resolved during type checking,** since its meaning depends on
  the receiver's type.
- **The referent of a name is one closed sum type,** matched exhaustively by
  later stages, which never derive a name's kind again, so resolution and
  checking cannot disagree.

### Broken definitions

A definition with a parse error is still registered and checked as far as
possible, so its error is reported once, by the parser, and no use of it
reports a second.

- **A part is broken only if the parser recovered inside it.** A part is a
  signature, a body, a type definition, or a member of a trait or an `impl`.
  A missing body breaks the body and not the signature, so the function keeps
  its interface, and an agent sees the callers' type errors in the same
  build.
- **A broken part gives the `Error` interface or shape,** and any use of one
  is accepted silently.
- **A test that can reach a definition with an error does not run,** and is
  reported as blocked by it. An unproven obligation does not block a test,
  since a test build checks every operation that could fail.

## Parts of a definition

The part of a definition that other definitions' checks read is a result of
its own, so a change to the rest invalidates nothing beyond the definition:

| Definition | Read by other definitions' checks | Read only by its own check |
|---|---|---|
| Function or method | Its *signature*: generic parameters and bounds, the receiver, parameters with their modes and whether each has a default, the result, `uses`, and whether it has a `time` clause | Its body, defaults, and contract |
| Type | Its *shape*: generic parameters, fields and variants, which fields have defaults, `indirect`, `opaque`, and `derives` | Its invariants, potential, and defaults |
| Trait | Its *interface*: parameters, required traits, associated types, method signatures, and law parameters | Each law's `requires` and body |
| `impl` | Its *interface*: generic parameters, trait, type, `uses`, and method signatures | Nothing |
| Constant | Its type, and its value where the checker needs it | Its expression |
| Test, theorem | Nothing | Its body |
| Law proof | Its trait, law, and type | Its body |

- **A function's specification is a result apart from its body:** the core
  form of its parameters and contract, which callers' proofs read. It holds
  the body only where a caller's proof reads it. A second result, the
  exported specification, is what another package's proofs read, with a body
  only for a `public transparent` function.
- **A shape lists its fields by name,** so reordering fields leaves it
  equal. The declaration order is a result of its own, which only a derived
  `Ordered` reads.

## Types

- **Types are nominal.** Function types are compared structurally, and value
  arguments are compared after constants are evaluated, so
  `Array[UInt8, digest_size]` equals `Array[UInt8, 32]` when `digest_size` is
  32.
- **Associated types are normalized** whenever their base is known. There
  are no blanket `impl`s, so a projection on a named type has at most one
  candidate `impl`.

### Errors carry their report

`Error` unifies with every type, so one mistake is reported once. That is
sound only if the mistake was reported, so an `Error` cannot be built without
a report, as rustc's `ErrorGuaranteed` cannot. Code with no report to
propagate either reports, or keeps the type unresolved: an associated type no
`impl` defines equals only itself, so code that depends on it is rejected,
not accepted. A disagreement between resolution, interfaces, and checking is
a compiler bug, and stops the compiler rather than accept code no stage
checked.

### No subtyping

Types are invariant. Exactly four conversions exist, all decided in the one
function that checks a value against its expected type:

| Conversion | Where |
|---|---|
| `Never` to any type | Wherever an expression of type `Never` meets an expected type |
| `List` to `Slice`, `String` to `StringSlice` | An argument for a parameter of the view type, and the key of an index |
| A function value to a function type with more `uses` or weaker costs | Where a whole expression is passed, bound, returned, assigned, or stored |
| A built-in integer to `Integer`, and back | In specifications only |

### Properties of types

`Copyable`, `Plain`, the view property, `Storable`, and structural equality
are derived from a type's shape, as conditions on its parameters, and stored
as a result of the type's definition. A query about
`Option[Option[List[Int64]]]` instantiates `Option`'s conditions with its
arguments and traverses no fields, so a type nested in itself is never
mistaken for a recursive one. Mutually recursive types are computed
together, as a fixed point.

A generic opaque type has a property under the conditions its fields give,
so a parameter no field uses adds none, as Swift's `BitwiseCopyable` does.
Rust's `derive` instead requires the property of every type parameter.

## Checking signatures and definitions

`Interface` checks the externally visible part of each definition on its own.

- **Every type is well formed,** and every bound it requires holds from the
  signature's own bounds: `SortedList[Element]` needs `Element: Ordered`.
- **Clauses are checked in source order,** each with the earlier ones in
  scope.
- **A container's header is lowered alone,** and each method with it, so a
  method's signature does not depend on its siblings.
- **A method an `impl` inherits, and a derived method, has a signature too,**
  because code generation and the prover compile and prove a method per
  `impl`.
- **An `impl`'s method matches its trait's** in parameter names, modes, and
  types, with bounds no stronger and `uses` a subset. Parameter names must
  match, since they are part of how a method is called. The prover shows
  that the method's own clauses are no weaker than the trait's.

### Recursive types

| The type contains itself | Failure the rule prevents |
|---|---|
| In place | Infinite size; the fix marks a variant `indirect` |
| In the input of a function type with a `time` clause | A stored function proven to terminate that calls itself through the value |
| With growing arguments, as `Nested[List[Element]]` | No fixed set of instances to compile |

These are package checks, since packages cannot depend on each other in a
cycle, so neither can their types.

## Checking bodies

**Inference is bidirectional and ends at each statement.** An expression is
either checked against an expected type or has its type inferred, and the
unknown types within a statement are solved by unification. When the
statement ends, each must be solved, so a type error is reported at the
statement that caused it, never at a distant use, and inference costs
follow the size of a statement.

- **A local declared from literals is the one exception.** Its literal type
  outlives the declaration until a use decides it, and a conflict is one
  error at the use, with a note at the statement that decided the type.
- **Each operator is a call of its trait method,** so the checker has no
  operator-specific rules.
- **Lambda arguments are checked last,** after the other arguments have
  decided the types and modes of the lambda's parameters.
- **An `impl` is never chosen from the expected type.**
- **`todo` takes the expected type,** or the `Hole` type, on which every
  operation is accepted, so the rest of the body is still checked.

**Exhaustiveness uses Maranget's usefulness algorithm** ("Warnings for
pattern matching", 2007) over the core form, so it checks the patterns the
prover and code generation read, including those `?` desugars to.

## Ownership

The ownership check enforces the rules of SPECIFICATION.md on modes, moves,
and views within each function. It prevents use after move, dangling views,
changes to a borrowed place, and data races. It reads the definition's MIR
([MIR.md](MIR.md)) and its callees' interfaces.

It builds a graph of points from the MIR, each one action on one place, and
runs three dataflow analyses: the places that may have been moved, the views
each holder may store, and the locals live after each point. A loan is live
while the value that holds it is, as in Rust's non-lexical lifetimes.

- **Places are compared by path, not by index value.** Where `items[i]` and
  `items[j]`, or two slices, may overlap and it matters, the check emits an
  obligation for the prover to prove them disjoint instead of an error.
- **A place can be moved out of a `mut` borrow** if every path reinitializes
  it before the borrow ends. This is sound because a panic ends the program,
  so nothing observes the place uninitialized. Rust unwinds, so it forbids
  the move and offers `mem::replace`.
- **A capturing lambda is a view of what it captures,** so it can be passed
  to a call but not returned or stored. A function passed to an `own`
  parameter of a function type must capture nothing, since the callee may
  store it.
- **`parallel` branches are checked as if they ran at the same time:** a
  place one branch changes overlaps no place another uses. A `concurrent`
  task adds one rule: it keeps a borrow only of a place the yielding method
  cannot change or drop before the task ends.

## Capabilities

At each point of a body a set of capabilities is available: the function's
`uses`, its capability parameters, and what each enclosing `provide`
provides. The check runs on the core form, where every call is a node,
including those that desugaring introduces, so a `for` loop needs what its
collection's `each` uses.

- **A capability parameter's set is inferred at each call,** as the least set
  that satisfies its constraints, and solved after the whole definition is
  checked.
- **A cursor's `next` needs its method's `uses`.** This prevents a use after
  free: a cursor that kept the implementation it was made with could run
  after its `provide` ended.
- **An unused `uses` is not an error,** since a later version may use it and
  callers already provide it.

### Monitors

Where the body of a `provide` can use `Tasks`, an implementation provided
`mut` is a monitor: code generation locks it around each call.

- **A monitor needs `Tasks` at its `provide`,** since the lock goes through
  that `Tasks`. With `Tasks` only in a nested `provide`, two tasks could run
  a `mut self` method at once, a data race.
- **A monitor's capability has no method with a callback that can use a
  capability.** Such a callback could enter a nested monitor while this one
  is held, and two tasks could deadlock.

### Dependency grants

Grants ([PACKAGES.md](PACKAGES.md#grants)) are checked from the signatures of
a dependency's code, never its bodies: at a call, at a function used as a
value, where its `impl` satisfies a bound, and at a `provide` of its type. A
package the manifest does not list is granted nothing, which catches an
`impl` in a transitive dependency. An unused dependency is checked only when
all of a package's code checks, since an unresolved call may hide a use.

## Traits and `impl`s across a package

These checks read more than one definition, so each is a package query.

- **Overlap.** Two `impl`s of one trait for one type constructor overlap when
  their trait arguments unify.
- **Finding an `impl`** searches only the packages the orphan rule allows,
  each lookup one query, so adding an `impl` re-checks only the definitions
  that made that lookup.
- **Object safety** is decided by one function, which code generation also
  uses to build an `any` value's method table, so the two cannot disagree.
- **Instantiation cycles** in which an edge puts a parameter inside a type
  constructor are rejected, as Go does, since such code has no finite set of
  instances.

## Constants

Whether an expression is constant is read from the recorded types and
resolutions, not from its spelling: `+` on built-in numbers is arithmetic,
but `==` on a `String` is a call. The checker evaluates a constant only
where it needs the value, in a type argument or a pattern, and evaluates
exactly, with no code run. Code generation builds every other constant.

## The core form

The core form is a typed, desugared tree of one definition, so no stage that
reads it repeats a decision the type checker made.

- **Calls are resolved,** with one argument per parameter in parameter
  order.
- **Every expression is a place or a value,** and reading a value out of a
  place has its own node, which copies a `Plain` value and moves any other.
- **Syntax is desugared into the calls it costs:** `?` as a `match`, a `for`
  loop as a loop over `each`, a collection literal as calls that allocate and
  insert, an interpolated string as calls of each value's `display`. So
  every call has the obligations of any call.
- **Every node has a type,** with no inference variable or hole, and an
  origin in the syntax tree. Core nodes hold no spans, so reformatting
  changes no core form.
- **A hole is `Never`.** Evaluating a `todo` never returns, so the core form
  holds no operation the checker did not resolve.
- **A derived method's core form is generated** from the type, as the body it
  would have if written by hand.

A test checks the core form's invariants on the standard library and on
every program the type checker's, ownership's, and prover's tests accept.

### Obligations the type checker creates

| Obligation | From |
|---|---|
| Two indexes or ranges of one collection are disjoint | Loans of `items[i]` and `items[j]` that would otherwise conflict |
| An `Integer` fits the built-in integer type expected | A conversion, as for `items[i + 1]` in a specification |
| A guarded `match` is exhaustive | Its last arm, `_ => unreachable` |

## Dependencies

A result depends on exactly the queries it demanded:

| Dependency | Example |
|---|---|
| A resolved form, or a part of it | The body of `parse_config` |
| An interface | The interface of `List.push` |
| A type's shape, or a fact of its definition | The shape of `Point`; whether `Option` is `Plain` |
| A constant's value | `digest_size` |
| The definitions of one name in a file | Those named `count` in `report.truss` |
| A module | Whether `standard::json` exists, and its names `parse` |
| The members of a type with one name | `List`'s members named `length` |
| The `impl`s of a trait for a type constructor, in one package | `Add` for `Instant`, in `Duration`'s package |
| A body fact | Whether `Tree.each` can be pulled |
| A manifest entry | The capabilities granted to `http` |

A checked body never depends on another body, except through two facts of a
callee's body: whether it can be pulled, and whether a `concurrent for` may
iterate over it. So a body edit re-checks that body; an `ensures` edit
re-checks no caller's types; a method added to `List` re-checks the
definitions that looked up that name on `List`; and a definition moved to
another module re-checks its users' names, while their test results stay
valid, since a test's key holds no names.

## The prelude

Built-in types are declared by the compiler in `standard::intrinsic`, with
two types the collections are made of: `Storage[Element]`, owned heap
storage whose drop and copy the compiler generates, and `View[Element]`, a
pointer and a length, which `Slice` and `StringSlice` hold. Everything else
in the prelude is ordinary Truss in [`standard/`](standard), checked like
any package.
