# Truss Type Checker

This document describes name resolution and type checking in stage0, in
[`stage0/`](stage0): every step between the parser's syntax trees
([PARSER.md](PARSER.md)) and the core form that the prover
([PROVER.md](PROVER.md)) and code generation ([CODEGEN.md](CODEGEN.md))
read. It checks the rules of [SPECIFICATION.md](SPECIFICATION.md), and its
queries run on the code database ([DATABASE.md](DATABASE.md)).

For each definition it produces four results:

- a *resolved form*: the referent of every name
- an *interface*: the part other definitions depend on
- a *core form*: the desugared, fully typed definition, which the pattern
  check, the ownership check, the package checks, the prover, and code
  generation read
- *tables* by syntax node: each expression's type, each name's and member's
  resolution, and each call's callee, which the usage check and tools read

It proves nothing: every fact that needs the solver, such as an index in
bounds or a `requires` at a call, goes to the prover, and the core form marks
the few obligations the type checker creates (see
[Obligations the type checker creates](#obligations-the-type-checker-creates)).
It runs no code, and decides no layout or drop.

## Structure

```text
syntax tree ──▶ Resolve ──▶ Interface ──▶ Body ──▶ core form, tables
   (per definition)  │            │             │
                     └─────▶ diagnostics ◀──────┘
                                  ▲
        Package checks ───────────┘   (impls, cycles, instantiation)
```

### One definition at a time, through queries

The type checker reads another definition only through a query, which the
database keeps current.

- **Each check is a query,** keyed by what it checks, such as a definition's
  interface or the members of a type with a given name (see
  [Dependencies](#dependencies)).
- **Checking a body demands its callees' interfaces,** never their bodies.
- **Each query belongs to one phase,** and reads only its own and earlier
  phases: a file's trees, its declarations, resolution, interfaces, bodies,
  package-wide rules, and diagnostics.
- **A cycle between queries is an error, or the design rules it out.** A
  signature depends only on signatures and shapes, so mutual recursion between
  functions makes no cycle. Each real cycle has a rule: constants that refer
  to each other, mutually recursive types, whose group's facts are one result,
  and traits that require each other.

### Deterministic results

Every result is canonical: inference variables are numbered in creation order
within a statement and none remains in a stored result, every list is in
source order or sorted by a stable key, no result is built by iterating a hash
table, and diagnostics are sorted by position and code.

### Node identity

Every node has an id, unique within its definition and assigned by the
parser. Later stages never rebuild a tree; each records its decisions in
tables keyed by id.

- **A span cannot be the key,** because spans are not unique: recovery makes
  zero-width nodes, and a node synthesized for a habit shares another's span.
- **Side tables are better than a tree parameterized by its annotations.**
  With such a tree each stage stores another copy with another type. With side
  tables the tree is stored once, a stage that records a new fact adds a
  table, and a stored result holds only that stage's decisions. rustc
  identifies nodes the same way, by owning item and a number within it.
- **The program's semantics are one more tree, built once:** the core form,
  which the type checker builds while it makes its decisions, so no later
  stage makes them again.
- **Ids are deterministic,** so a definition that only moved keeps its ids and
  every table stays valid. An id means something only within its definition;
  a result refers to another definition by path.
- **A method is a definition wherever it is written,** with its own tree, ids,
  and results, so an edit to one method of an `impl` re-checks only that
  method. Its path is its enclosing declaration, its name, and its receiver
  mode.
- **A generic parameter is identified by its declaring definition and its
  name,** so it has one identity in every tree that can see it.
- **Tables are dense arrays** indexed by id.

## Name resolution

`Resolve` produces the resolved form, reading the definition's tree, the
file's `use` lines, and other files' exports, each through a query.

- **Names are in four namespaces,** told apart by the case rules and `::` and
  `.`: modules, types, values, and members.
- **An unqualified name** is looked up among the locals in scope, the generic
  parameters, the file's definitions, then the prelude. At most one matches,
  because shadowing is an error.
- **A full path starts with a package the file can name.** That name takes two
  segments when the package has an owner: `acme::geometry::vector` is the
  module `vector` of `acme::geometry` if the manifest lists that package.
- **A member is not resolved here,** since its meaning depends on the type
  before the dot, except where the name before the dot is already known to be
  a type, as in `Shape.Circle`.
- **The referent of a name is one closed sum type,** matched exhaustively by
  later stages, which never derive a name's kind again, so resolution and
  checking cannot disagree.
- **One function decides how an expression is read as a name,** so `parse`,
  `(parse)`, and `parse[Int64]` are read the same way by every caller.
- **A definition is identified by package, module path, and name,** and a
  method by its type, name, and receiver mode.
- **A specification word has its meaning only where SPECIFICATION.md gives it
  one,** and is an ordinary name elsewhere.
- **A bare argument is bound to a parameter by type checking,** since that
  needs the callee's signature (see [Operators and calls](#operators-and-calls)).
- **An unresolved name gets a fix** to the closest visible name, and habits
  that are names, such as `null`, get exact fixes.

### Broken definitions

A definition with a parse error is still registered and checked as far as
possible, so its error is reported once, by the parser, and no use of it
reports a second.

**A part is broken only if its tree differs from its source.** A part is a
signature, a body, a type definition, or a member a trait or an `impl` holds
directly. A part is broken if one of its definition's recovered spans (see
[PARSER.md](PARSER.md#interfaces-to-other-stages)) is within it. A
zero-width recovered span at `p` is within the part that starts at `p`, if
any, so a missing body breaks the body and not the signature, and the
function keeps its interface. A parser diagnostic that only enforces a rule
on code parsed as written, such as a misplaced `assert`, breaks nothing, so
the part is checked and an agent sees its type errors in the same build.

- **Every broken definition with a name is registered,** so uses of it resolve.
- **A broken part is never checked.** A broken signature gives the `Error`
  interface, and broken fields the `Error` shape. A broken member affects only
  that member. Synthesized code is always in a broken part, so it is never
  checked.
- **Any use of an `Error` interface or shape is accepted silently,** and gives
  `Error`, which carries the parser's diagnostic (see
  [Errors carry their report](#errors-carry-their-report)).
- **A broken definition is a dependency like any other,** so fixing it
  re-checks exactly the results that used its `Error` interface.
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

- **A function's specification is separate from its body.** It is the core
  form of the parameters and the contract, built before the body so its nodes
  are numbered the same whatever the body is. It holds the body only where a
  caller's proof reads it: a method of a trait or an `impl` in the logic, and
  never a function's or a method of a type's. A second result, the exported
  specification, is what another package's proofs read, with no function's
  body.
- **A public `requires` and `cost` name only public definitions**
  (`types.private_in_public`), since another package's proofs must meet or
  count on them, and the contract of a function other packages cannot see is
  not compared between releases. An `ensures` may name a private function, so
  that callers in the package can know a public function's result in terms of
  its private helpers. Type invariants, laws, and the `requires` of a
  function-typed parameter are not checked yet. The compatibility check does
  not compare the contracts of the private functions these clauses name.
- **An assertion `by bit_vector` names only integers and booleans**
  (`types.not_bit_vector`), since the prover decides it over the bits of
  their fixed widths.
- **A shape has its fields in the order of their names,** so reordering fields
  leaves it equal. The declaration order is a result of its own, which only a
  derived `Ordered` reads.

## Types

The representation of types is in `stage0/types/types.mli`.

- **A built-in type is a `Named` type** whose definition the compiler provides
  in the prelude. Only `Never` and `Integer` have constructors of their own,
  because each has rules no definition could state.
- **Types are nominal.** Function types are compared structurally, including
  the subject of each `calls` clause, so `(fn() cost calls(FileRead) <= 1)` is
  not a `(fn() cost calls(Clock) <= 1)`. Value arguments are compared after
  constants are evaluated, so `Array[UInt8, digest_size]` equals
  `Array[UInt8, 32]` when `digest_size` is 32.
- **Associated types and capability sets are normalized** whenever their base
  is known. There are no blanket `impl`s, so a projection on a named type has
  at most one candidate `impl`. A projection on a generic parameter stays, and
  equals only itself or the type a bound fixes it to. An `any` type's sets are
  empty.
- **Inference variables and undecided literal types exist only during
  checking.** A stored checked form holds neither. A `Hole`, the type of a
  `todo` with nothing expected, is never an error.

### Errors carry their report

`Error` unifies with every type, so one mistake is reported once. That is
sound only if the mistake was reported, so an `Error` cannot be built without
a report, as rustc's `ErrorGuaranteed` cannot.

- **A report is a diagnostic a stage emitted, or a parser's recovered span.**
- **A report is propagated, never invented.** A use that meets an error
  another definition's check reported reads that definition's diagnostics and
  takes the first.
- **Code with no report to propagate either reports, or keeps the type
  unresolved.** An associated type no `impl` defines stays a projection that
  equals only itself, so code depending on it is rejected, not accepted.
- **A pattern that does not match its scrutinee's type still binds its
  names,** with the pattern's `Error`, so every local has a type.
- **An internal inconsistency stops the compiler.** A disagreement between
  resolution, interfaces, and checking is a compiler bug, and raises an
  exception, since continuing would accept code no stage checked.

### No subtyping

Types are invariant. Exactly four conversions exist, all decided in the one
function that checks a value against its expected type, which wraps the
value's core node:

| Conversion | Where |
|---|---|
| `Never` to any type | Wherever an expression of type `Never` meets an expected type |
| `List` to `Slice`, `String` to `StringSlice` | An argument for a parameter of the view type, and the key of an index. This is SPECIFICATION.md's only implicit conversion. |
| A function value to a function type with more `uses` or weaker costs | Where a whole expression is passed, bound, returned, assigned, or stored, never inside a type argument |
| A built-in integer to `Integer`, and back | In specifications only |

For costs, the checker accepts what the constants of the two types show: an
exact count is within a bound it does not exceed, a count is `O(...)`, and
every bound is `finite`. Any other implication is a prover obligation, marked
by a `Widen` node, or read from the argument at a call.

### Properties of types

`Copyable`, `Plain`, the view property, `Storable`, and structural equality
decide the operations on a type's values, as SPECIFICATION.md defines them.
Each is derived from the type's shape, as conditions on its parameters.

- **The properties are facts of a type's definition,** computed once per
  definition and stored as a result of their own, together with whether a
  value can hold a function and the types the type contains.
- **A fact is a list of conditions:** for `Plain`, the types that must be
  `Plain` for the type to be; for the view property, the types of which any
  one makes it a view. A query about `Option[Option[List[Int64]]]`
  instantiates `Option`'s conditions with its arguments, and no query
  traverses fields, so a type nested in itself is never mistaken for a
  recursive one.
- **Mutually recursive types are computed together,** as a fixed point from
  the facts of the types without fields.
- **An associated type is a condition too,** decided per instantiation by the
  `impl` that defines it. One no `impl` defines is assumed not to be
  `Copyable` or `Plain`, and to be a view.
- **A generic opaque type has the properties under the conditions its fields
  give,** so a parameter no field uses adds none, as Swift's checked
  `BitwiseCopyable` does. Rust's `derive` instead requires the property of
  every type parameter. The cost is that a change to such a type's fields can
  change which arguments need the property.
- **Declaring `Copyable` or `Plain` on a type that is not opaque is an error,**
  with a fix that removes it, because the fields already decide it.
- **The view property is part of a type's shape,** so adding a view to a type
  invalidates every result that read the shape.

## Checking signatures and definitions

`Interface` checks the externally visible part of each definition on its own,
from its resolved form and the shapes and interfaces it names.

- **`Self` and `Self.Name` are known only to the lowering of a written type,**
  so only that lowering reports a misplaced one.
- **Every type is well formed,** and every bound it requires holds from the
  signature's own bounds: `SortedList[Element]` needs `Element: Ordered`.
- **The `requires` of a function-typed parameter is not part of its type,** so
  two function types that differ only in it are the same type. The prover
  reads it from the signature.
- **Clauses are checked in source order,** each with the earlier ones in scope.
- **`derives` is checked against the shape,** under the same conditions on the
  type parameters as the derived `impl` has. Each derived `impl` is a
  definition of its own, identified by the type and the trait.
- **A type defined as `todo`** has none of the properties, so it cannot be
  copied and is not a view.

### Traits, `impl`s, and capabilities

A container is checked separately from the methods written inside it:

- **The header is lowered alone,** from its own tree: its generic parameters,
  bounds, `Self`, associated types, and, for an `impl`, its trait, type, and
  `uses`.
- **Each method is lowered with that header.** A method of an `impl` is
  generic over the `impl`'s parameters and then its own, and uses the `impl`'s
  capabilities. A method of a trait is generic over its own parameters only.
- **A method an `impl` inherits, and a method of a derived `impl`, has a
  signature too,** the trait method's with `Self` and the trait's parameters
  substituted, because code generation and the prover compile and prove a
  method per `impl`.
- **An `impl`'s method matches its trait's** in parameter names, modes, and
  types, the result clause, and bounds no stronger, with `uses` a subset.
  Parameter names must match, since they are part of how a method is called.
  Defaults are written only in the trait. The prover shows that the method's
  own clauses are no weaker than the trait's.
- **A set an `impl` defines from itself** is
  `types.unknown_associated_capability`.
- **A law proof's parameters have exactly the `impl`'s bounds.** The prover
  checks a law once for every instantiation of the `impl`, so with fewer
  bounds the type would not implement the trait, and with more the law would
  be taken as proven for types the proof does not cover.
- **A method that overrides a provided method** has exactly its signature, and
  the provided method must be one whose body is a definition.

### Recursive types

| The type contains itself | Failure the rule prevents | Diagnostic |
|---|---|---|
| in place | infinite size | `package.needs_indirect`, with a fix that marks the variant where the cycle starts |
| in the input of a function type with a `time` clause | a stored function proven to terminate that calls itself through the value | `package.not_strictly_positive` |
| with growing arguments, as `Nested[List[Element]]` | no fixed set of instances to compile | `package.growing_type` |

- **Each contained type has an occurrence:** in place, indirect (behind an
  `indirect` variant, a collection's storage, an `any`, or a function's
  output), or a function input. Through another type, the occurrence is a
  function input if either is, in place if both are, and indirect otherwise.
- **How a generic type contains its arguments is a fact of its definition,**
  so `type Wrap(next: Callback[Wrap])` is caught through `Callback`'s fact.
- **An associated type's definition is read too.** With `type Part =
  Kept[Marker]` in an `impl`, `Kept[Marker]` contains itself though no type's
  fields do, and the error is on the `impl`.
- **These are package checks,** since packages cannot depend on each other in
  a cycle, so their types cannot either.
- **A growing type is found by a traversal of its own,** as in Go: the nodes
  are generic types' parameters, and a type grows when a cycle through them
  has an edge whose argument is more than the parameter.

## Checking bodies

### Bidirectional, one statement at a time

An expression is either *checked* against an expected type, which flows
inward from annotations, parameters, and operators, or has its type
*inferred*. Unknown types within a statement are inference variables, solved
by unification. When the innermost statement ends, each must be solved: an
undecided literal takes its default, and any other unsolved variable is an
error with a fix that annotates the `let`. So a type error is reported at the
statement that caused it, never at a distant use, and the cost of inference
follows the size of a statement.

- **A block inside an expression** has its statements inferred separately,
  and its tail checked against the block's expected type.
- **A scrutinee is inferred before its patterns,** as a statement of its own,
  since a pattern needs its scrutinee's type. A scrutinee that is a local of
  undecided literal type stays undecided, and an integer pattern is checked
  once a later statement decides it.

### Literals

A literal's type is decided by the expected type, then by the other operand,
then by its default, as SPECIFICATION.md says. A literal type in the type of a
local outlives the declaration, and unification for it spans statements at the
cost of one variable per such local:

- **The statement that encloses the declaration gives the default:** the
  statement that holds the block, the loop for a loop variable, or the end of
  the body, so an undecided type cannot leak past the local's scope.
- **A use that needs the type takes the default,** as a method call does,
  since method lookup needs the receiver's type. An integer pattern does not
  need it.
- **A specification converts the local to `Integer`,** as it does a built-in
  integer, so `index + 1 <= 11` in an invariant does not make `index` an
  `Integer`, which code cannot have.
- **A conflict is one error, with the deciding statement.** The error is at
  the use, with a note at the statement that decided the type, and later
  mismatches of the same local reuse that report. When a method call gave the
  default, the fix writes the needed type on the `let` or the `for`, as in
  `for index: UInt8 in 0..10`.

Once a literal's type is known, an integer literal must fit it after
negation, and a float literal is rounded once, from its exact decimal value,
ties to even; one that rounds to infinity is an error. The standard library is
checked with its target's width of `USize`. A character or byte literal
records its value, as an integer literal does.

### Operators and calls

Each operator desugars to a call of its trait method, so the checker has no
operator-specific rules: the recorded call is the trait method's, chosen by
the types of both operands once they are known. Compound assignment selects
an `own self` version of the method when the trait has one. Mismatched
integer types, as in `count == length` with a `UInt32` and a `USize`, get
fixes that convert one side with `From`, or `TryFrom` where it can lose
information.

Arguments are matched to parameters in one pass, then checked for parameter
order, with a fix that reorders them. A label is added by a fix only when one
open parameter has a matching type. Each omitted argument is `Default` in the
core form, for the default-presence mask of CODEGEN.md.

- **Lambda arguments are checked last,** after the other arguments have
  decided the types and modes of the lambda's parameters. Its result type can
  still come from its body, as `Output` does in
  `items.map(fn(item) { item.name.copy() })`.
- **Generic arguments are inference variables,** solved from the arguments
  and the expected type, after any explicit type arguments.
- **Bounds are checked wherever generic parameters are instantiated,** once
  the statement has inferred the constrained type: at a call, a function used
  as a value, a `for` loop's `each`, and a generic type named or built. A bound
  that fixes an associated type unifies it with the `impl`'s definition, so a
  bound can decide a type. A statement reports each failed bound once.
- **An `impl` is never chosen from the expected type.**

### Modes at calls

| Parameter | Argument |
|---|---|
| read-only | an unmarked place, which the callee views; a lent part; or a temporary |
| `mut` | `mut place`, or a part lent `mut`. A missing mark gets a fix that adds it. |
| `own` | `own place`, which moves it; `place.copy()`; a temporary; or a `Plain` place or lent part, which is copied |

- **Marks are never redundant.** `own` on a `Plain` place, or any mark on a
  temporary, is an error with a fix that removes it, so each argument has one
  spelling. On a receiver, a mark also chooses the version.
- **A `mut` mark needs a mutable place:** a `var`, a `mut` parameter, a `mut`
  loop's variable, `self` in a `mut self` method, a field or element of one,
  or a part lent `mut`. A constant, a `let`, a read-only or `own` parameter,
  and a captured local are not mutable.
- **A lent part takes no mark.** It is lent read-only or `mut` by the method's
  signature, and cannot go to an `own` parameter unless it is `Plain`.

### Members

`receiver.name` is looked up in the receiver's type: visible fields, the
type's own methods, including those whose head's bound fails, which are an
error naming the bound, the methods of the traits the type implements from
the packages SPECIFICATION.md allows, and `copy()` for a `Copyable` type.

All versions of a name are found by one function, for a method call, a
qualified call, and the `each` of a `for` loop or a quantifier, and the
receiver's mark then picks one. The traits must form one family, each
required by another. Two unrelated traits with a method of the name are an
error at the call, with a fix per trait that writes the call in full. A type's
method and a trait's with the same name and mode are a package check, at the
`impl`.

### Statements and blocks

- **An assignment through an index can insert a key.** If the collection's
  type implements `IndexAssign`, `collection[key] = value` is a call of its
  `assign`, which takes the key as an `own` argument. Otherwise it assigns the
  place `collection[key]` denotes, which must exist. A compound assignment
  reads the place first, so it never goes through `assign`.
- **A statement whose value is not `Unit` or `Never`** gets a fix that writes
  `let _ =`. The arms of an `if` or `match` are unified, ignoring arms of type
  `Never`.
- **A `for` loop** iterates a call of a `yields` method directly, advances a
  cursor, or otherwise calls the value's `each` with the loop's mode. An
  annotation on its pattern unifies with the element type while the header is
  checked, so it decides a range's literals. One that differs is an error,
  never a conversion: C# converts each element of a `foreach` to the written
  type, and that hidden cast can throw or lose data.
- **A `parallel` or `concurrent` block never finishes when a branch never
  does,** for the unreachable-code check.
- **`todo` takes the expected type.** With none it has the `Hole` type, on
  which every operation is accepted, so the rest of the body is still checked,
  and its diagnostic lists the uses of the value.
- **A tagged template is checked as `Tag.from_template(template)`,** with each
  interpolated value converted to the `impl`'s `Part` through `From`.

## Patterns

- **The mode of a pattern's bindings follows its scrutinee's.** A pattern on a
  read-only place binds views of its parts, on a `mut` place `mut` borrows for
  the arm or iteration, and on an owned value its parts as owned values. A
  `Plain` part is copied.
- **Exhaustiveness uses Maranget's usefulness algorithm** ("Warnings for
  pattern matching", 2007) on the vector of scrutinees, over the core form, so
  it checks the patterns the prover and code generation read, including those
  `?` desugars to. Its constructors are variants, `true` and `false`,
  intervals of integers and characters, and constants expanded to their
  values; a constant whose value is not known when compiling covers only
  itself.
- **A missing case** is named, with a fix that adds an arm with `todo` for each.
  An arm, or an alternative of an or-pattern, that earlier ones cover gets a
  fix that deletes it.

## Ownership: moves, loans, and views

`Ownership` enforces the rules of SPECIFICATION.md on modes, moves, and views
within each function, which prevents use after move, dangling views, mutation
of a borrowed place, and data races. It reads the definition's MIR and its
callees' interfaces.

It builds a graph of points from the MIR, each one action on one place: a
read, a move, a `mut` borrow, an assignment, or a binding. The MIR's loans are
live at the points between where they start and end. A lambda's body is a
separate entry, since it runs when called. Three dataflow analyses run on the
graph: the places that may have been moved, the views each holder may store,
and the locals live after each point. A function for specifications only is
not checked.

### Places

A place is a local, a parameter, `self`, or a constant, followed by fields and
by indexes of a `List`, `Slice`, or `Array`; an index of any other collection
is a call of its lending `at`. Two places overlap when one is a prefix of the
other. The checker does not compare index values, so where `items[i]` and
`items[j]`, or two slices, may overlap and it matters, it emits a `Disjoint`
obligation for the prover instead of an error.

### Moves

- **Use after move is an error** on any path, with a note at the move and a
  fix that copies there when the type is `Copyable`.
- **Moved places are tracked by field path,** so one field can be moved.
- **Only an owned place can be moved.** Moving out of a read-only parameter, a
  view, a constant, or an element is an error, with fixes that copy, or for an
  element call a method such as `remove`.
- **A place can be moved out of a `mut` borrow if every path assigns it again
  before the borrow ends:** before return, before the iteration, arm, or
  lambda ends, and in a yielding method before each `yield`, since the
  caller's loop may stop there. A lending method always resumes, so it may
  yield while the place is moved out. This is sound because a panic ends the
  program, so nothing observes the place uninitialized; Rust unwinds, so it
  forbids the move and offers `mem::replace`.
- **A local a value is moved into owns it,** so after `let moved = own items`,
  `items` can be assigned again while `moved` lives.
- **Returning a place that is not owned is an error,** with a fix that copies.

### Loans

| Loan | Kind | Live during |
|---|---|---|
| A read-only argument | shared | the call |
| A `mut` argument or receiver | `mut` | the call |
| A `let` of a place, or a value of a view type | shared | the liveness of the value |
| The receiver of a lending call | shared, or `mut` for `mut self` | the rest of the statement |
| A `for` loop's variable | shared or `mut` | the iteration |
| A `provide` of a place | shared or `mut` | the block |
| An evaluated operand | shared | until its operation runs |

A value's loans are live while it is, which a liveness analysis computes, as
in Rust's non-lexical lifetimes. Under a shared loan no code assigns, moves,
or `mut`-borrows an overlapping place, and under a `mut` loan no other code
uses one. A loan of a view is a loan of the places it views.

- **An evaluated operand stays borrowed until its operation runs,** so
  `show(items[0], count: grow(mut items))` is an error: the call would get an
  element of a list `grow` has since changed.
- **A `match`'s scrutinee stays borrowed while a guard runs,** since a false
  guard matches the later arms against the same value.
- **An argument's `mut` borrow starts at the call,** so
  `mut items.push(items.length())` is allowed, as Rust's two-phase borrows
  allow it.

### Views

Every rule uses one definition of the places a value views,
`Graph.views_of`.

- **A call's result views every argument it could borrow from** that is not
  `Plain`, and every view argument.
- **A `mut` argument that can hold views may store the call's view
  arguments,** and then views their places. A borrowed argument that is not a
  view is never stored, by the callee's own check, so after
  `mut reader.read(mut buffer, limit: 2)` the reader does not view the buffer.
  A function argument whose result is not a view can be stored only in a `mut`
  argument whose type can hold a function.
- **An `if`, a `match`, or a block views every place its tail expressions
  view,** and the checker decides this for every kind of expression, with no
  default case. A place assigned a view keeps its earlier views too, since
  the analysis is a may-analysis.
- **A value copied out of a place has the views the place's root stores, and
  a value that borrows a place views the place.** So a slice read from
  `part`, after `let part = items[0..2]`, views `items`, and can be returned
  when `items` is a parameter.
- **A binding of a `match` or an `is` on a place aliases it,** and a view of
  an alias is a view of the aliased place, so a method can return a slice of
  a field it matched.
- **A function returns a view only of its parameters,** not of a local or an
  `own` parameter, which would dangle. A view copied out of an `own`
  parameter borrows the caller's data, so it can be returned.
- **A view stored in a `mut` parameter must not dangle,** and must come from
  a parameter of a view type, so the signature states which arguments the
  callee may store. Callers do not change, since a `List` converts to a
  `Slice`.
- **A value cannot refer to itself,** as `self.recent = self.items[0..1]`.
- **No view crosses a capability implementation's boundary.** A method of a
  capability's `impl` stores no view it receives and returns no view of its
  own state, because the caller cannot see the implementation. A view the
  implementation was built with can be returned, since its builder keeps the
  data alive while it is provided.
- **Writing through a slice needs every place it views to be mutable.** A
  slice stored in a field is read-only whatever the record's mode.
- **A view argument cannot alias a `mut` argument** of the same call.
- **A stored view cannot view a temporary,** which is dropped at the end of
  its statement; the error asks to bind it first, as Rust's E0716 does. A
  string literal without interpolation is static, so a view of it is fine.
- **An `any Trait` has the views of the value converted to it.**

### Function values

Every function type is a view type, since it does not say whether the
function captures, and the views depend on the value:

- **A named function, or a lambda that captures nothing, has no views,** and
  can be returned and stored freely.
- **A capturing lambda views each captured variable and its environment
  record,** which is a local of the enclosing function, so it cannot be
  returned or stored in a `mut` parameter, but can be passed to a call or
  held in a local record or list.
- **A function value passed to an `own` parameter of a function type must
  capture nothing,** because the callee may store it. A value the caller does
  not own, such as a read-only function-typed parameter, is rejected there too,
  since it may capture. A generic `own` parameter instantiated with a function
  type is tracked by the view rules instead, which is why a capturing lambda
  can be pushed onto a local list.

### Owned values where they are required

A place where an owned value is required, other than a returned place, must
be marked `own` or copied unless it is `Plain`, with both fixes offered. The
type checker reports a missing mark, because only the syntax tree records
marks; in the core form, reading a value that is not `Plain` from a place is
always a move the source permits. A constant expression is exempt, since it is
evaluated when compiling. A tagged string moves its parts into the template,
and a plain string only reads them.

### Yielding and lending

- **A `lends` method yields exactly once on every path.** Every branch of a
  `parallel` block runs, so their yields add. A loop is counted by its paths:
  those that reach the end of the body or a `continue` repeat, and those that
  `break` or `return` do not, so a body that yields and returns yields once.
- **A lending call borrows its whole receiver for the rest of the statement.**
  The condition of an `if` or a `while` is a statement of its own, so its
  loans end before the then-block or the body, unless a name the condition
  binds may alias the lent part: a name bound `mut`, or whose type is a view
  or is not `Plain`. Then they last until that block ends, which prevents a
  dangling name, and never into the `else` block. The core form records the
  choice as `binds_lent_part`, so that the check and the code generator
  agree. An index of a collection other than `List`, `Slice`, or
  `Array` is a lending call, so `grid[a] = grid[b]` needs the right side in a
  `let` first.
- **A yielded constructor lends the places among its fields,** read-only for a
  read-only method and, for a `mut` one, the places marked `mut`. Two places
  lent `mut` to one value cannot overlap, and two indexes produce a `Disjoint`
  obligation. An owned value beside a lent place is
  `ownership.owned_beside_lent`, whose message asks to bind it first.
- **A lent part cannot outlive its loan,** so it is not returned, stored,
  moved, or bound with `let` unless it is `Plain`. A `match` on it binds views
  of its fields, or `mut` borrows when it is lent `mut`.
- **A loop that borrows its collection `mut` may change it on every
  iteration,** so a view the body copied out of one part cannot be used in a
  later iteration.
- **Whether a cursor can be created is checked where it is created,** because
  every holder may pull it, including generic code checked without knowing its
  type arguments.
- **Two facts come from a callee's body:** whether it can be pulled, and the
  task hazard of a method a `concurrent for` iterates over. Each is stored
  apart from the interface, and a caller reads it only when it pulls the
  method or iterates over it concurrently.

### `parallel`

Each branch, and each iteration of a `parallel for`, is checked as if it ran
at the same time as the others: a place one branch mutates, by assignment, a
`mut` borrow, or a move, overlaps no place another branch uses. A use of a view
uses the places it views, so one branch cannot push to a list while another
reads a slice of it.

### `concurrent`

`concurrent` follows the same rule, and adds three because a branch can exit
early and a `concurrent for` task outlives its `yield`:

- **A branch reinitializes every place it moves out of a `mut` borrow,** since
  the code after the block does not run when a branch exits early.
- **An early exit transfers control to its usual target,** for this check.
- **A task keeps a borrow or a view only of a place the yielding method cannot
  mutate or drop,** a place inside a read-only parameter. A `concurrent for`
  is rejected with `ownership.task_outlives_yield` when one of the method's
  `yield`s yields `mut`, or lends or views a place outside a read-only
  parameter. A method that yields by position, whose body is one `for` over a
  range whose body is one `yield`, is accepted, as decided by
  `Core_walk.yields_by_position`. A `Plain` element is copied to the task. A
  callee whose body is unknown, such as a method called through a bound, needs
  an owned element that is not a view. The fact is `Views.task_hazard`,
  computed by the method's own analysis.

## Capabilities

### Capability checking

At each point of a body a set of capabilities is available: the function's
`uses`, its capability parameters, and what each enclosing `provide`
provides. In a method of a capability's `impl` it is the `impl`'s `uses`; an
indirect call there may also use the implemented capability, meaning this
implementation, so the method can pass itself to a callback.

The check runs on the core form, where every call is a node, including those
desugaring introduces, so a `for` loop needs what its collection's `each`
uses, and an interpolation what each value's `display` uses.

- **A cursor's `next` needs its method's `uses`,** and so does making the
  cursor. This also prevents a use after free: a cursor that kept the
  implementation it was made with could run after its `provide` ended.
- **A trait method's `uses` is taken for the type it is called on,** so
  `Self.Uses` is the `impl`'s set, the method's `uses` for a yielding method's
  cursor, and `Source.Uses`, available only where declared, for a generic
  parameter.
- **A call of an intrinsic needs what `Intrinsic.uses` lists,** except in a
  method of a capability's `impl`, which callers reach only through a
  capability call their signatures declare. A lambda, a branch, or a helper
  inside such a method is not exempt.
- **A capability parameter's set is inferred at each call,** as the least set
  that satisfies its constraints: the capabilities each function converted to
  its type uses beyond the type's `uses`, and those a lambda's body needs.
  After `let delayed = later(tick)`, `delayed` uses `Clock` when `tick` does.
  Only a function or method takes one
  (`types.misplaced_capability_parameter`), since no argument could be
  written for a type's.
- **The sets are solved after the whole definition is checked,** since a
  constraint can be anywhere in it; until then a set is a variable that
  affects nothing else about its types.
- **A function's own capability parameter is rigid in its body.**
- **A specification has no capabilities at all; a `parallel` branch has only
  `Panic`; a test without `uses` has `Panic` and what it provides; and
  `concurrent` code needs `Tasks`.**
- **An unused `uses` is not an error,** since a later version may use it and
  callers already provide it.

### `provide`

Each implementation is checked like an argument, and provides every capability
its type implements, found among the `impl`s of the type's package and of the
visible capabilities' packages. A place is marked `mut` exactly when one of
those `impl`s has a `mut self` method.

Where the body can use `Tasks`, an implementation provided `mut` is a monitor.

- **The body can use `Tasks`** when it contains `concurrent` code, or a call
  that uses `Tasks` or a capability parameter. `Core_walk.can_use_tasks`
  decides this after capability sets are solved, and code generation calls
  the same function, so the two agree on which implementations are monitors.
- **A monitor needs `Tasks` at its `provide`**
  (`capabilities.monitor_needs_tasks`), since code generation locks through
  that `Tasks`. If the only `Tasks` is in a nested `provide`, two tasks could
  run a `mut self` method at once, a data race. A body that can use `Tasks`
  only through a capability parameter is accepted, since each instance has
  `Tasks` at the `provide` exactly when it needs a lock.
- **A monitor's capability has no method with a callback parameter that can
  use a capability** (`capabilities.callback_may_deadlock`), counting function
  types with `uses`, `any` types and bounded parameters whose traits have such
  methods, and types that contain them. Such a callback could enter a nested
  monitor while this one is held, and two tasks could deadlock.

### Dependency grants

Grants (see [PACKAGES.md](PACKAGES.md#grants)) are checked from the
signatures of a dependency's code, never its bodies, except for capabilities
that come from a capability parameter. A dependency's code is referenced by a
call, including the `impl` method it resolves to; a function value of its
function; its `impl` satisfying a bound, checked in the one function that
resolves bounds, recursively through the `impl`'s own bounds; and a
`provide` of its type.

- **A grant is one query,** keyed by package and dependency, each capability
  resolved to a definition.
- **A package the manifest does not list is granted nothing,** which catches
  an `impl` in a transitive dependency.
- **The error names the code and the capability,** with no fix.

### The manifest

Each definition's result lists the packages it uses, and the union over a
package's definitions, without its tests, is what `truss publish` publishes.
Two package checks are reported at the manifest: a grant that names no
capability, so a misspelling is not silently never granted, and an unused
dependency, checked only when all of a package's code checks, since an
unresolved call may hide a use. Its fix deletes the entry.

## Traits and `impl`s across a package

These checks look at more than one definition, so each is a package query.

- **Overlap.** Two `impl`s of one trait for one type constructor overlap when
  their trait arguments unify, with each `impl`'s generic parameters as
  variables.
- **Finding an `impl`** searches only the packages the orphan rule allows,
  each lookup one query, such as the `impl`s of `Add` for `Instant` in the
  package of `Duration`, so adding an `impl` re-checks only the definitions
  that made that lookup.
- **An associated type is read from the `impl` whose head matches,** whether or
  not its bounds hold, since `impl`s do not overlap. So normalizing reads
  nothing about the type's arguments, which is why a property of a type can
  depend on an associated type without a query cycle.
- **Method names.** The rule of SPECIFICATION.md's "Method lookup" is
  reported at the `impl`, wherever it is. A trait's method cannot share a name
  with a constant of the type either.
- **Object safety** is decided by one function, which code generation also uses
  to give an `any` value's method table a slot for exactly those methods. An
  associated type of `Self` is allowed, since `any` fixes it, but `Self` at any
  depth is not, so `Cursor.skip`, which returns `Skip[Self]`, is not
  object-safe. `any value` is `types.no_impl` when the value's `impl` defines
  a capability set that is not empty, or its type is a generic parameter.
- **Instantiation cycles.** Each checked body records its instantiation edges:
  each generic definition it calls, with arguments in terms of its own
  parameters. A package check reports a cycle in which an edge puts a
  parameter inside a type constructor, as Go does. Calls cannot cycle between
  packages, so the graph is one package's.

## Specifications

Specifications are checked like code, except:

- **Integer arithmetic is on `Integer`,** and an `Integer` where a built-in
  integer is expected records an obligation that it fits. A literal nothing
  else decides is an `Integer`.
- **A function whose signature mentions a type of specifications, or a method
  of `Model`,** is callable only from specifications and never compiled.
- **A quantifier over a type and `==>` in a compiled body** are errors here,
  since only the signature says whether a body is compiled. In code, a
  quantifier borrows its collection for its body, so the body cannot mutate
  it.
- **Every callee is pure and has a `time` clause,** both facts of its
  interface.

## Constants

Whether an expression is constant is read from the types, resolutions, and
calls the checker records, not from its spelling: an operator on built-in
numbers and `Bool` is arithmetic, but `==` on a `String` is a call; a name is
constant when it means a definition; and a call is constant only when it
builds a record or a variant.

The checker evaluates a constant only where it needs the value: a `USize` in a
type argument, and a constant used as a pattern. It evaluates exactly with no
code run: integers are Zarith's, and floats use OCaml's exact IEEE operations,
with a `Float32` computed in 64 bits and rounded, which is correctly rounded
for `+`, `-`, `*`, `/`, and `sqrt` because 53 bits is more than twice 24 plus
2. Each step of integer arithmetic must fit its type, so
`let small: UInt8 = 200 + 100 - 100` is an error at `200 + 100`. Every other
constant is built by code generation (see CODEGEN.md). A result that used a
constant's value reads that value, so an edit that keeps the value re-checks
nothing.

## The tables

The published tables, keyed by syntax node id, answer questions about the
source as written, including code with errors: each expression's and
binding's type, each name's and member's resolution, and each call's callee.
Tools and the usage check read them. Every other check, the prover, and code
generation read the core form, which exists only for a definition without
errors.

While checking a body the checker fills private tables (`Tables` in
`stage0/infer`), such as each call in full with its `impl` and argument modes,
from which it builds the core form.

### The core form

The core form is a typed, desugared tree of one definition, and no stage that
reads it repeats a decision the type checker made. Its types are in
`stage0/core/core.mli`. It records:

- **Resolved calls,** with one argument per parameter in parameter order, the
  receiver first, and omitted arguments marked as defaults. A yielding
  method's cursor has a compiler-generated `impl` of `Cursor`, identified by
  the method, so a provided method such as `count` is called on it like any
  trait method.
- **Places and values.** Every expression is one or the other, an index is a
  lending call of `Index.at`, and reading a value out of a place has its own
  node, which copies a `Plain` value and moves any other. Code that only
  borrows a place never has that node.
- **Lent fields only in a yielded constructor,** so a yielded value that lends
  a place owns nothing and nothing drops it.
- **Resolved operators.** An operation on built-in types is one node however
  it was written; for any other type `==` is a call of `equal` and an
  ordering operator a call of `compare` and a test.
- **The tasks an early exit terminates,** listed innermost first on each
  `return`, `break`, or `continue` that leaves `concurrent` code.
- **Desugared syntax,** each into the calls it costs, so every call has the
  obligations of any call: `?` as a `match`, a `for` loop as a loop over
  `each`, a collection literal as calls that allocate with capacity and
  insert, a map literal with an insertion that requires an absent key, an
  owned collection passed as its view as a call of `slice`, a tagged string
  as `from_template` with its literal texts kept for the prover, and an
  interpolated string as calls of `TextBuilder` and each value's `display`.
- **Whether a condition is executable,** which a `requires` or an `assert` is
  when it has no quantifier, `Integer`, `old`, `result`, or call of a
  specification-only function.
- **A type on every node,** with no inference variable or hole.

Every core node has an id, and an origin: the syntax node it was built from,
which a diagnostic uses to quote source. Core nodes hold no spans, so
reformatting changes no core form.

**The core form is built after the whole definition is checked,** by functions
registered while checking, since only then is every type final. The
capability check runs on it and solves capability variables, and if there
were any, the core form is built again with the solutions.

**A hole is `Never`.** Evaluating a `todo` never returns, so a use of a hole is
a `todo`, a pattern on one is a wildcard, and an expression with a hole operand
evaluates its operands and ends in a `todo`. So the core form holds no
operation the checker did not resolve.

**A test checks the core form's invariants** on the standard library and every
program the type checker's, ownership's, and prover's tests accept: unique ids,
no inference variable, hole, or error in a type, generic parameters declared by
the definition or its container, `mut` parameters given places and `own`
parameters values, mutable places where assigned, and alternatives that bind
the same locals.

**A derived method's core form is generated** from the type, as the body it
would have if written by hand, once per method, not per instantiation:
`equal` stops at the first difference, `hash` writes the variant's index and
then each field, and `compare` is the only method that reads the declaration
order of fields.

**The core form of a path** is a written body, a derived method's generated
body, or, for a method an `impl` inherits, the trait's provided body with a
substitution for `Self` and the trait's parameters.

### Obligations the type checker creates

| Obligation | From |
|---|---|
| Two indexes or ranges of one collection do not overlap | Loans of `items[i]` and `items[j]` that would otherwise conflict, listed in the ownership check's result |
| An `Integer` fits the built-in integer type expected | A conversion node, as for `items[i + 1]` in a specification |
| A guarded `match` is covered | Its last arm, `_ => unreachable` |

## Dependencies

A result depends on exactly the queries it demanded:

| Dependency | Example |
|---|---|
| A resolved form, or a part of it | The body of `parse_config` |
| An interface | The interface of `List.push` |
| A type's shape, or a fact of its definition | The shape of `Point`; when `Option` is `Plain` |
| A constant's value | `digest_size` |
| The definitions of one name in a file | Those named `count` in `report.truss` |
| A module | Whether `standard::json` exists, and its names `parse` |
| The members of a type with one name | `List`'s members named `length` |
| A package's traits that declare a method name | `standard`'s traits with `compare` |
| One field of a manifest | `weather`'s modules |
| The `impl`s of a trait for a type constructor, in one package | `Add` for `Instant`, in `Duration`'s package |
| A type's capability `impl`s | What `MemoryFiles` implements |
| A body fact | Whether `Tree.each` can be pulled |
| A manifest entry | The capabilities granted to `http` |

- **A package's declarations are listed once,** and each index, such as methods
  by owner and name or `impl`s by trait and type, is one pass over that list.
- **Each lookup in an index is a result of its own,** so a definition is
  re-checked only when its answer changes, though the index is rebuilt
  whenever the package declares something new.
- **A checked body never depends on another body,** except through a callee's
  two body facts.

So a body edit re-checks that body; an `ensures` edit re-checks no caller's
types; a method added to `List` re-checks the definitions that looked up
that name on `List`; and a definition moved to another module re-checks its
users' names, while their test results stay valid, since a test's key holds
no names.

## Diagnostics

Diagnostics use the lexer's `Diagnostic` type. The checker attaches an exact
fix wherever the intent is unambiguous.

- **One error per cause.** A wrong expression becomes `Error`, which holds its
  report and unifies with everything, and a definition the parser could not
  read is reported by the parser alone.
- **An error in `f[X]` says which reading applied.**
- **Habits of other languages that need types,** such as `pair.0`, get
  messages that point to the standard library's records.
- **Holes are not errors;** each is reported to the tools with its type and the
  names in scope.

## Interfaces to other stages

- **The prover** reads core forms, its callees' interfaces and contracts, the
  bodies it uses as definitions, and the obligations above.
- **Code generation** reads core forms, shapes, and which methods can be
  pulled. Instantiation cycles are already rejected.
- **The build** finds the definitions `main` can reach from core forms, and
  rejects a program that reaches a `todo` or an `echo`.
- **Tools** read the tables.

## The prelude

Built-in types are declared by the compiler in `standard::intrinsic`, with
two types the collections are made of:

- **`Storage[Element]`,** owned heap storage with a buffer, a length, and a
  capacity, whose drop and copy the compiler generates, so `List` and
  `String` need no destructor. It holds its elements off the stack, so a type
  that contains itself through one needs no `indirect`.
- **`View[Element]`,** a pointer and a length, which `Slice` and
  `StringSlice` hold. It is a view and `Plain`, so `Option[Slice[Int64]]`
  copies implicitly.

The intrinsic module's operations are one type that the type checker and code
generation each match exhaustively. Everything else in the prelude is ordinary
Truss in [`standard/`](standard), checked like any package.

**`Well_known` lists once each standard library definition the compiler names
by path,** such as `Add`'s method for an operator, and a test checks that each
exists, so renaming one fails the test.

**A call of a trait's yielding method that resolves to a known `impl` records
the `impl`'s method,** since the cursor's type and a loop's contract must come
from the method that defines them, such as `List`'s `each`.
