# Truss Type Checker

This document describes name resolution and type checking in stage0, in
[`stage0/`](stage0): every step between the parser's syntax trees and the core
form that the prover and code generation read. It follows the decisions in
[DESIGN.md](DESIGN.md), [SYNTAX.md](SYNTAX.md), and [GRAMMAR.md](GRAMMAR.md).
Its input is the trees described in [PARSER.md](PARSER.md). Its output is the
core form that [CODEGEN.md](CODEGEN.md) and [PROVER.md](PROVER.md) consume. Its
queries run on the code database, which [DATABASE.md](DATABASE.md) describes.

## What the type checker does

The type checker's inputs are the syntax tree of each definition, the package's
manifest, and the manifests of the package's dependencies. For each definition
it produces four results:

- a *resolved form*: the definition with its names resolved;
- an *interface*: the part of the definition that other definitions can depend
  on;
- a *core form*: the desugared and fully typed definition, which the pattern
  check, the ownership check, the package checks, the prover, and code
  generation read;
- *tables* by syntax node: the type of each expression and binding, the
  resolution of each name and member, and the callee of each call, which the
  usage check and the tools read.

The database records the dependencies of each result and caches each result
under them, as DATABASE.md describes.

The type checker:

- resolves every name, and disambiguates the constructs that the parser left
  ambiguous: `name[...]`, a bare name in a pattern, and a place after `mut` or
  `own`
- separates a definition's interface from its body, so that a change to a body
  re-checks no caller
- checks every signature, type definition, trait, `impl`, and capability
  independently
- infers the type of every expression in a body, and selects the method, field,
  variant, `impl`, and associated type that each name refers to
- checks ownership within each function: modes, moves, and views
- checks that every `match` is exhaustive and has no unreachable arm, and that
  every pattern in a `let`, a `for`, or a lambda is irrefutable
- checks usage: every value, variable, and import is used, and no code is
  unreachable
- checks capabilities: the capabilities that each piece of code uses, the
  capabilities that each `provide` provides, and the capabilities that each
  dependency was granted
- checks the package-wide rules: where an `impl` may be defined (the orphan
  rule), that `impl`s do not overlap, that recursive types are marked
  `indirect` and are strictly positive, and that generic code has no
  instantiation cycle

It does not:

- prove anything. Every fact that needs the solver goes to the prover: an index
  in bounds, an addition that cannot overflow, a `requires` at a call, a type
  invariant, a cost, termination, and two index ranges that are disjoint. The
  core form marks the few obligations that the type checker itself creates (see
  [Obligations the type checker
  creates](#obligations-the-type-checker-creates)).
- run code. Constants are evaluated exactly, from literals alone (see
  [Constants](#constants)). The checks of a tagged template are `requires`
  clauses, which the prover discharges by running compiled code.
- decide layouts, drops, or any other property of the compiled program

## Structure

```text
syntax tree ──▶ Resolve ──▶ Interface ──▶ Body ──▶ core form, tables
   (per definition)  │            │             │
                     └─────▶ diagnostics ◀──────┘
                                  ▲
        Package checks ───────────┘   (impls, cycles, instantiation)
```

### One definition at a time, through queries

The type checker reads another definition only through a query of the code
database. The database keeps each result up to date and finds the results that
a change invalidates, as [DATABASE.md](DATABASE.md) describes. The type checker
defines the queries and their dependencies:

- **Each check is a query** with a key: the resolved form of a definition, its
  interface, its checked body, the shape of a type, the members of a type with
  a given name, and so on (see [Dependencies](#dependencies)).
- **Checking a body demands the interfaces of its callees.** That checks the
  callees' signatures if they have not been checked yet, but never their
  bodies. A check of a package demands the checked body of every definition in
  the package.
- **Each query belongs to one phase of the compiler:** a file's trees, a file's
  declarations, name resolution, interfaces, bodies, the package-wide rules,
  and diagnostics. A query reads its own phase and earlier phases.
- **A cycle between queries is an error, or the design rules it out.** A
  signature depends only on other signatures and on type shapes, never on a
  body, so mutual recursion between functions never makes a query cycle. Each
  of the few real cycles has a rule: constants that refer to each other,
  mutually recursive types (a package check requires `indirect`, and one result
  computes the facts of the whole group), and traits that require each other.

### Deterministic results

Every result is canonical, as DATABASE.md requires of a query:

- inference variables are numbered in creation order within one statement, and
  none remains in a stored result
- every list in a result is in source order, or sorted by a stable key such as
  a definition's path
- the checker never iterates over a hash table to build a result
- diagnostics are sorted by position, then by code

### Node identity

Every node that the parser builds has an *id*: a small integer, unique within
its definition, assigned in the order in which the parser builds the
definition's nodes. Later stages never rebuild or copy a tree. Each stage
records its decisions in tables keyed by node id: resolution's table gives the
referent of each name, and the checker's tables give each expression's type,
each call's argument binding, each pattern's variants, and so on.

- **A span cannot be the key.** Spans are not unique: a node that the lexer or
  the parser creates during error recovery has zero width, and a node that the
  parser synthesizes for a habit, such as the `from` in the call that `x as
  Int64` is parsed as, shares its span with another node.
- **Side tables are better than a tree that is parameterized by its
  annotations,** as in OCaml's separate typed tree or the "trees that grow"
  pattern. With such a tree, each stage builds and stores another copy, and
  each stage's tree has a different type. With side tables, the tree is stored
  once and shared by every stage and tool, a stage that records a new fact adds
  a table, and a stored result holds only that stage's decisions. rustc
  identifies its nodes the same way, by the owning item and a number within it
  (`HirId`), so that a change to one item renumbers nothing in another.
- **The program's semantics are one more tree, built once.** The syntax tree is
  the program as written, which tools and diagnostics need. The stages that run
  or prove the program need its semantics: the callee of each call, the
  desugaring of each `?`, the place of each value. That is [the core
  form](#the-core-form). The type checker builds it while it makes these
  decisions, so no later stage makes them again. Its nodes refer to the syntax
  nodes that they came from, and hold no positions.
- **Ids are deterministic.** The same tokens give the same nodes with the same
  ids. So a definition that only moved keeps its ids, as it keeps its tree, and
  every table keyed by them stays valid.
- **An id is meaningful only within its definition.** A result never refers to
  a node in another definition. It refers to the definition, by path, as every
  cross-definition reference does.
- **A method is a definition wherever it is written.** A method written inside
  a trait, an `impl`, or a capability has its own tree, its own ids, and its
  own results, exactly as a method written `fn Type.name` has. So an edit to
  one method of an `impl` re-checks only that method. Its path consists of its
  enclosing declaration, its own name, and its receiver mode.
- **A generic parameter is identified by its declaring definition and its
  name,** not by a node. Resolution records a use of `Element` as the parameter
  `Element` of `List.push`, or of the method's enclosing `impl`, which is the
  same pair that a type uses. So a parameter has one identity in every tree
  that can see it, and no table maps a node to it.
- **Tables are dense arrays** indexed by id, stored like every other result. A
  node that a stage records nothing for has an empty entry.

## Name resolution

`Resolve` produces a definition's resolved form: a table, keyed by the tree's
node ids, of the referent of every name. The tree itself is unchanged (see
[Node identity](#node-identity)). `Resolve` reads the definition's own tree,
the file's `use` lines, and the names that other files and packages export,
each through a query.

### What a name can refer to

Names are in separate namespaces, which the case rules distinguish:

| Namespace | Written | Holds |
|---|---|---|
| Modules | before `::` only | packages and modules |
| Types | `UpperCamelCase` | types, traits, capabilities, generic type parameters, and capability parameters |
| Values | `lower_snake_case` | locals, parameters, functions, constants, value generic parameters, theorems |
| Members | after `.` | fields, methods, variants, constants under a type, associated types |

- **An unqualified name** is looked up among the locals in scope, then the
  generic parameters, then the definitions in the same file, then the prelude.
  Exactly one can match, because shadowing is not allowed.
- **A qualified name** `module::name` is looked up in that module. The module
  is either imported by a `use` or written as a full path from its package. A
  full path starts with the name of a package that the file can name: its own
  package, `standard`, or a package that its manifest lists. That name takes
  two segments of the path when the package has an owner:
  `acme::geometry::vector` is the module `vector` of the package
  `acme::geometry` if the manifest lists that package, and otherwise a module
  of a package `acme`.
- **A member,** after `.`, is not resolved here. Its meaning depends on the
  type of the expression before the dot, which only type checking knows. The
  one exception is a name before the dot that resolution already knows to be a
  type, as in `Shape.Circle`, `UInt8.maximum`, or `List[String].with_capacity`:
  the resolved form records the type, and the type checker looks the member up
  in it.

**The referent of a name is one closed sum type.** The resolved form records
each name as one of: a local; a generic parameter that is a type, a capability,
or a `USize` value; a definition, with its kind; a prelude variant; a module; a
field; a specification word; or an unresolved name, with its diagnostic. A
later stage matches on these cases exhaustively. It never derives the kind
again, from the spelling of the name or by looking the definition up, so
resolution and checking cannot disagree about the kind of a name.

**One function decides how an expression is read as a name.** `parse`,
`(parse)`, `parse[Int64]`, and `(parse)[Int64]` all name `parse`, the last two
with type arguments. Resolution, checking a name as a value, checking it as a
callee, and reading a type that is written in an expression all call that
function, so each treats parentheses and type arguments the same way.

The resolved form identifies a definition by package, module path, and name,
never by a hash, as DESIGN.md requires. It identifies a method by its type, its
name, and its receiver mode, because one name can have a version for each mode.

### Scopes

- **Every `use` line imports one module.** Two imported modules with the same
  last name are an error at the second `use`. An imported module that no name
  in the file uses is an error, as in Go, with a fix that deletes the line.
  Only the `standard` package can import `standard::intrinsic`. That error is
  reported at the `use` line only: names written through the import resolve as
  usual.
- **Locals are block-scoped.** A `let` or a `var` is in scope for the rest of
  its block. A name bound by `is` is in scope in the rest of its `&&` chain, in
  the block of the `if` or `while` whose condition contains it at the top level
  of its `&&` chain, and in the body of a `match` arm whose guard contains it
  in the same way. It is not in scope after `||`, under `!`, or in an `else`. A
  name bound by `let ... else` is in scope for the rest of the enclosing block.
  A `let` in a branch of a `parallel` or `concurrent` block is in scope after
  the block, and not in the other branches.
- **Shadowing is an error.** Binding a name that is already visible in the
  values namespace, whether a local of an enclosing scope, a parameter, or a
  definition in the same file, is an error that names both bindings. The
  prelude holds only `UpperCamelCase` names and values are `lower_snake_case`,
  so only types can clash with the prelude. Generic parameters are checked the
  same way against the file's types and the prelude.
- **A specification word has its special meaning only in certain positions:**
  - `result` is the return value, inside `ensures` and `cost`.
  - `old(...)` is the value on entry, inside specifications and proofs.
  - `log(...)` and `power(...)` are functions on `Integer`, inside any
    specification, unless a local or a definition of the file has the name.
  - `time(...)` and `calls(...)` are the cost of a call and the number of
    calls, inside a `cost` bound.
  - `identical(a, b)` is identity of two values of one type, inside
    specifications.
  - `yielded` and `finished` are the sequence of values that a lending or
    yielding method has yielded and whether the method ran to completion,
    inside its `ensures`. `yielded` is also the sequence of values that the
    earlier iterations of a `for` loop received, inside its `invariant`.

  Anywhere else, these are ordinary names. Where a word has its special
  meaning, a visible variable with the same name would be shadowed, which is an
  error as everywhere else.

### Decisions the parser left open

| Construct | Resolved as |
|---|---|
| `name[...]` | Type arguments if `name` is a generic function, a type, or a trait. An index if it is a local, a parameter, or a constant. For a method, as in `items.map[String]`, type checking decides from the receiver's type. |
| A bare `LOWER_NAME` in a pattern | The constant, if a constant with that name is visible. Otherwise a new binding. |
| A place after `mut` or `own` | The expression must start with a local, a parameter, `self`, or a constant, followed by field accesses and indexes. `mut parse[Int64](text)` starts with a function, so it is an error with a fix that removes `mut`. |
| A `LOWER_NAME` in a type argument | A value generic parameter or a constant of type `USize`, as in `Array[UInt8, digest_size]` |

Binding a bare argument to a parameter needs the callee's signature, and for a
method the receiver's type, so type checking does it (see [Calls and
arguments](#calls-and-arguments)).

### Errors and habits

Resolution reports each unresolved name, with a fix to the closest visible name
when one is similar. It also reports the habits from other languages that are
names, with exact fixes: `null` and `nil` become `None`, and `Shape::Circle`
becomes `Shape.Circle`.

### Broken definitions

A definition that has a parse error is still registered and checked as far as
possible. Its error is then reported once, by the parser, and no use of the
definition reports a second error. PARSER.md states what the parser keeps:

- **A definition whose header did not parse** keeps only its keyword and name,
  if the parser could read them.
- **Any other broken definition** keeps its whole tree, with an `Error` node
  for each part that failed. It keeps its signature as written when every
  diagnostic is in its body.
- **The members of a trait, an `impl`, or a capability recover independently.**
  A broken associated type or law is an `Error` member, and the other members
  are as written. A method is a definition of its own, so an error in it
  affects only that method.
- **Nodes synthesized for a habit** are in the same signature or body as the
  habit's diagnostic.

**A part is broken only if its tree differs from its source.** A part is one
signature, one body, or one type definition, either of a definition or of a
member that a trait or an `impl` holds directly: an associated type or a law.
The parser lists, on each definition, the *recovered spans*: the spans where
the tree is not the source as written, because the parser built an `Error` node
or a node for a habit, or consumed a closing delimiter that the lexer inserted.
A part is broken if one of its definition's recovered spans is within the
part's span:

- a signature extends from the start of the definition or member to the start
  of its body;
- a body is its block;
- a member is its line;
- a type is its definition.

A recovered span with nonzero width is within every part that it overlaps. A
zero-width recovered span at position `p` is within the part that starts at
`p`, if there is one, even if that part is itself zero-width, and otherwise
within the part with `start <= p < stop`. So a missing body breaks the body and
not the signature, and the function keeps its interface: the missing body is
recorded as a zero-width span at the end of the signature, which is also where
its `Error` body starts.

Some parser diagnostics only enforce a rule on code that was parsed exactly as
written: a misplaced `assert`, `yield`, `break`, or `echo`, a `forall` outside
a specification, a parameter named `result`, `lends own`, a repeated clause, or
a misplaced `public` or `opaque`. Such a diagnostic does not break its part.
The part is checked as usual, because checking it cannot report on synthesized
code, and an agent then sees its type errors in the same build as the parser's.
The parser classifies each of its diagnostic codes as a recovery or not, in one
exhaustive match, so a new code does not compile until it is classified, and
the type checker never classifies codes.

The type checker uses the broken parts as follows:

- **Every broken definition that has a name is registered,** as a definition of
  its kind, so uses of it resolve. A definition whose name could not be read
  registers nothing, and a use of the name that it was meant to define is an
  unresolved name.
- **A broken part is never checked.** A definition whose header or signature is
  broken gets the `Error` interface, and a type whose fields or variants are
  broken gets the `Error` shape. A broken body is not checked. A broken member
  of a trait, an `impl`, or a capability affects only that member: a trait with
  one broken method keeps the interface of every other method, so uses of those
  are checked as usual, and only uses of the broken method get `Error`. No
  member of a trait, an `impl`, or a capability whose own header is broken is
  checked, because its enclosing declaration is unknown. Nodes synthesized for
  a habit are in a broken part, so synthesized code is never checked.
- **Any use of an `Error` interface or shape is accepted silently.** A call of
  such a function accepts any arguments and has the type `Error`. Constructing
  such a type, reading its fields, matching on it, and looking up its members
  all give `Error`. A trait with the `Error` interface satisfies every bound
  that names it, and a constant with it has the type `Error`. The interface or
  shape holds the parser's diagnostic, and every `Error` derived from it
  carries that diagnostic (see [Errors carry their
  report](#errors-carry-their-report)).
- **A part that is not broken is checked as usual.** A function whose body is
  broken keeps its interface, so its callers are checked against its signature
  as written, as for any function.
- **A broken definition is a dependency like any other.** A result that used
  its `Error` interface depends on that interface as on any other. So when the
  definition is fixed, exactly those results are re-checked.
- **Builds and tests skip code that cannot run.** A build rejects a program
  that can reach a definition with any error, broken or not. A test that can
  reach such a definition does not run, and is reported as blocked by it. Every
  other test runs as usual. An obligation that the prover has not proven, or
  could not prove, does not block a test: a test build checks at run time every
  operation that could fail, as CODEGEN.md describes, so tests run without
  waiting for proofs. A build of a program still needs every proof.

## Parts of a definition

A definition is not one result. The part that the checks of other definitions
read is separate from the rest. A change to the rest leaves that part equal, so
the change invalidates nothing beyond the definition:

| Definition | Read by the checks of other definitions | Read only by its own check |
|---|---|---|
| Function or method | Its *signature*: generic parameters and bounds, the receiver, parameter names, types, and modes, which parameters have defaults, the result or the `yields` or `lends` clause, `uses`, and whether it has a `time` clause | Its body, each default, and its `requires`, `ensures`, `decreases`, and `cost` clauses |
| Type | Its *shape*: generic parameters, fields and variants with their types, which fields have defaults, `indirect` marks, `opaque`, and `derives` | Its invariants, its potential, and the defaults of its fields |
| Trait | Its *interface*: parameters, required traits, associated types, the signature of each method, and the parameters of each law | The `requires` and the body of each law |
| `impl` | Its *interface*: generic parameters, the trait, the type, `uses`, and the signature of each method | Nothing |
| A method written inside a trait, an `impl`, or a capability | Its signature, as for a function, interpreted with the `Self`, the associated types, and the generic parameters of the enclosing declaration | Its body, if it has one, and its clauses |
| Constant | Its type, and its value where the checker needs the value | Its expression |
| Test, theorem | Nothing | Its body |
| Law proof | Its subject: the trait, the law, and the type | Its body |

- **Type checking a caller reads only the callee's signature.** A change to a
  body, a default, or an `ensures` re-checks that definition and no caller.
  PROVER.md states what the prover reads of a callee.
- **A function's specification is separate from its body.** The specification
  is the core form of the parameters and the contract. It has the body only
  when a caller's proof can read the body: the body of a function in the
  logic, which is the function's definition, and the body that a trait
  provides for a method, which an `impl`'s method that replaces it is compared
  with. The parameters and the contract are built before the body, so their
  nodes are numbered the same whatever the body is. Editing a body that the
  specification leaves out leaves the specification equal. A second result,
  the exported specification, is what a proof in another package reads. It has
  the body of a function only when the function is `public transparent`, so
  editing any other body re-proves nothing in a package that depends on this
  one. `transparent` is part of the signature, and it is an error on a function
  whose body cannot be a definition.
- **What another package's proofs read names only what is public.** Those
  proofs read the `requires`, `ensures`, and `cost` of every definition that
  the package can call, and the body of a `transparent` function. A function
  or a constant that such a clause or body names must be public
  (`types.private_in_public`). The contract of a function that other packages
  cannot see is not compared between releases, so a change to it would break
  their proofs with no change reported. A definition that other packages can
  call is a public function, method, or theorem, a method of a public trait
  or capability, and a method of an `impl` of a public trait for a public
  type. A `transparent` body can read a hidden field, because a change to
  the field changes the body. Type invariants, laws, and the `requires` of a
  function-typed parameter are not checked yet.
- **A default is separate from the signature,** as DESIGN.md requires: callers
  read only whether a parameter has a default.
- **A type's invariants are separate from its shape.** Strengthening an
  invariant re-checks the type, and no user of the type.
- **The declaration order of a type's fields is separate from its shape,** as
  DESIGN.md requires. A shape has its fields in the order of their names, so
  reordering the fields in the source leaves the shape equal and re-checks no
  reader of it. The declaration order is a result of its own, which only a
  derived `Ordered` reads. The order of a sum type's variants is part of its
  shape.

## Types

### Representation

```ocaml
type ty =
  | Named of { definition : definition; arguments : argument list }
  | Parameter of parameter                  (* Element, inside its definition *)
  | Projection of { base : ty; trait : trait_reference; name : string }   (* Items.Element *)
  | Function of function_type
  | Any of trait_reference                  (* with every associated type fixed *)
  | Cursor of yielding_instance             (* the nameless type of a pulled method *)
  | Never
  | Integer                                 (* specifications only *)
  | Variable of int                         (* while checking one statement *)
  | Literal of literal_kind * int           (* an integer or float literal not yet decided *)
  | Hole                                    (* the type of a todo with nothing expected *)
  | Error of reported                       (* after an error, to stop cascades, with its report *)

and argument = Type of ty | Value of value  (* USize generic arguments *)
and value = Known of Z.t | Value_parameter of parameter

and function_type = {
  parameters : (mode * ty) list;
  result : result;                          (* Returns ty, or Yields / Lends with a mode and ty *)
  uses : capability_set;                    (* capabilities, parameters, and associated sets, sorted *)
  costs : cost list;
}
```

- **A built-in type is a `Named` type** whose definition the compiler provides
  in the prelude, such as `Int64`, `Bool`, `Unit`, and `Array`. Only `Never`
  and `Integer` have constructors of their own, because each has rules that no
  definition could state: `Never` converts to every type, and `Integer` exists
  only in specifications.
- **Types are nominal.** Two `Named` types are equal when they have the same
  definition and equal arguments. Function types are compared structurally,
  including the subject of each cost clause: a `calls` clause of a function
  type counts the calls of a capability or of one of its methods, and that
  capability or method is part of the type, so `(fn() cost calls(FileRead) <=
  1)` is not a `(fn() cost calls(Clock) <= 1)`. A function type cannot name a
  parameter: only a function's own clauses count the calls of a parameter.
  Value arguments are compared by value, after constants are evaluated, so
  `Array[UInt8, digest_size]` equals `Array[UInt8, 32]` when `digest_size` is
  32.
- **Associated types are normalized** whenever their base is known. There are
  no blanket `impl`s, so `Projection { base = Named ...; ... }` has at most one
  candidate `impl`. A projection on a generic parameter stays a projection. It
  equals only itself, or the type that a bound fixes it to, as in
  `Iterable[Element = Int64]`.
- **Associated capability sets are normalized** in the same way.
  `Capability_projection { base; trait; name }` in a set of capabilities is
  replaced by the set that the `impl` for `base` defines, which is empty when
  the `impl` leaves it out, and by the empty set when `base` is an `any` type.
  A projection on a generic parameter stays, and is a capability that is
  available only where a `uses` clause declares it. Its trait reference fixes
  no associated type, so that two projections of one set are equal. `uses`
  clauses are normalized where a call is recorded, where a function type is
  normalized, and where an `impl`'s method is compared with its trait's.
- **`Variable` and `Literal` exist only during checking.** A stored checked
  form contains neither. A `Hole` stays where the type of a `todo` was never
  decided: a `todo` is not an error, so a `Hole` never becomes an `Error`.

### Errors carry their report

`Error` unifies with every type, so that one mistake is reported once. That is
sound only if the mistake was reported. So an `Error` cannot be constructed
without a report: it holds a value that only a report produces, as rustc's
`ErrorGuaranteed` does.

- **A report is one of two things:** a diagnostic that a stage emitted, or a
  recovered span of the parser, which exists only where the parser or the lexer
  reported an error.
- **Every representation of an error holds a report:** the `Error` type, the
  `Error` interface and shape of a broken definition, a broken member of a
  trait, and an unresolved name.
- **A report is propagated, never invented.** A call of a broken function has
  the `Error` with that function's report, and a use of an unresolved name has
  the `Error` with the name's report. A use can meet an error that the check of
  another definition reported, as with an `impl` that omits an associated type.
  It then reads that definition's diagnostics and takes the first as the
  report.
- **Code that has no report to propagate either reports, or keeps the type
  unresolved.** A function that cannot report returns no `Error`. An associated
  type that no `impl` defines stays a projection, which equals only itself, so
  code that depends on it is rejected, not accepted.
- **A pattern that does not match the type of its scrutinee still binds its
  names,** each with the `Error` of the pattern's report, so every use of a
  local has a type.
- **An internal inconsistency stops the compiler.** Resolution, the interfaces,
  and checking must agree, for example that every local has a type and that
  every expression of a checked body has one. A disagreement is a compiler bug
  and raises an exception. Continuing would accept code that no stage checked.

### No subtyping

Types are invariant, and there is no subtyping relation. Two types are equal or
they are not, and function types with different `uses` or different costs are
different types. Exactly four conversions exist. All are decided in the one
function that checks a value against its expected type, which wraps the
value's core node in the conversion:

| Conversion | Where |
|---|---|
| `Never` to any type | Wherever an expression of type `Never` meets an expected type, such as `None => return Err(error)` in a `match` whose value is an `Int64` |
| `List[Element]` to `Slice[Element]`, `String` to `StringSlice` | An argument passed to a parameter of the view type, and the key of an index, which is the argument of `at`. This is DESIGN.md's only implicit conversion. |
| A function value to a function type with more `uses` or weaker costs | Where a value is passed, bound, returned, assigned, or stored, and where it is the tail expression of a branch of an `if` or a `match`. A pure function can be passed as `(fn(Item) uses Clock)`, and a `cost time O(1)` function as `cost time finite`. |
| A built-in integer to `Integer`, and back | An argument or the key of an index, in specifications only (see [Specifications](#specifications)) |

The function-value conversion applies only to a whole expression, not inside a
type argument, so `List[fn(Item)]` and `List[(fn(Item) uses Clock)]` stay
different types, as in Rust.

- **The expected type must list every capability that the function uses.** A
  function that `uses Clock` is never a `fn()`, in an argument, a `let`, a
  `return`, a field, or an assignment. Where the expected type lists a
  capability parameter of the callee, the parameter is instantiated with the
  capabilities that the function uses, as [What code may
  call](#what-code-may-call) describes.
- **The checker accepts weaker costs that the constants of the two types
  show:** an exact count is within any bound that it does not exceed, a count
  is `O(...)`, and every bound is `finite`. The type of a named function has
  `time finite` exactly when the function has a `time` clause. Any other cost
  implication is an obligation for the prover. For a function that is passed to
  a call, the prover reads the argument, as PROVER.md's "Lambdas and function
  values" describes. Anywhere else the core form marks the conversion with a
  `Widen` node.

### Properties of types

Five properties of a type decide what code can do with a value of it. Each is
derived from the type's shape, as a condition on its type parameters:
`Option[Value]` is `Plain` exactly when `Value` is.

| Property | Holds for | Allows a value to |
|---|---|---|
| `Copyable` | every type except the standard library's handles and types that hold a handle | be copied with `copy()` |
| `Plain` | integers, floats, `Bool`, `Character`, `Unit`, arrays, records, and sum types that consist only of `Plain` parts, with no heap data and no handle | be copied implicitly. `Plain` requires `Copyable`. |
| View | `Slice`, `StringSlice`, a cursor from a `self` method, every function type, every `any` type whose trait does not require `Storable`, and every type that holds a view anywhere: in a field, a variant, an element, or a type argument | nothing more. A value of a view type cannot escape its function (see [Views](#views)). |
| `Storable` | every type that is not a view type for every instantiation of its type parameters. A type parameter is `Storable` only when it is bounded by `Storable`. | be stored where the ownership check cannot track a view, such as a channel's queue. A generic type that stores a value there bounds it, as in `Channel[Message: Storable]`. |
| Structural equality | the built-in integers, `Bool`, `Character`, `Unit`, `String`, the types of specifications, and a type that derives `Equal` and whose fields all have structural equality. Never floats, a type with a hand-written `Equal`, or, outside its package, an opaque type. | be a constant in a pattern. The prover substitutes equals for equals through `==`. |

- **`Copyable`, `Plain`, and `Storable` are prelude traits that the compiler
  implements.** No `impl` of them can be written. A generic parameter has one
  of them only when it is bounded by it, as in `[Element: Copyable]`, so an
  unbounded `[Element]` accepts every type, including handles and views.
- **`Storable` is derived from the fields of every type,** opaque or not, as
  the view property is. It states that no instance of the type can hold a view:
  `List[Element]` is `Storable` where `Element` is, and no function type is.
- **`any Trait` is `Storable` only when `Trait` requires `Storable`,** as with
  `Copyable`. Every type that implements such a trait holds no view, so the
  value inside the `any` holds none.
- **An opaque type is `Copyable` or `Plain` only when it declares so** with
  `derives Copyable` or `derives Plain`. The checker verifies the declaration
  against the fields. Other packages rely on the declaration, so adding a field
  that cannot be copied is an error at the type, and never a surprise in
  another package. Every other type has the two properties by inference.
  Declaring them on a type that is not opaque is an error with a fix that
  removes the declaration, because the fields already determine them.
- **A generic opaque type has the properties under the conditions that its
  fields give,** as any other generic type does. `Slice[Element]` holds a view
  of its elements, so it is `Plain` for every `Element`. `List[Element]` owns
  its elements, so it is `Copyable` when `Element` is. A type parameter that no
  field uses, as in `opaque type Id[Entity](value: UInt64)`, adds no condition.
  Swift checks a declared `BitwiseCopyable` against the fields in the same way.
  Rust's `derive` instead requires the property of every type parameter, which
  is why a `Copy` type with an unused parameter needs a hand-written `impl` in
  Rust. The cost is that a change to the fields of a generic opaque type can
  change which of its type arguments must have the property.
- **`copy()` is always the compiler's.** It is the method of `Copyable`. No
  type can give copying a cost or a side effect, as no type can define a
  destructor.
- **`any Trait` is `Copyable` only when `Trait` requires `Copyable`,** because
  the concrete type inside it is unknown.
- **The view property is part of a type's shape.** Adding a view to a type
  changes how every use of the type is checked. Like any other change of shape,
  it invalidates every result that read the shape.

`Copyable`, `Plain`, the view property, whether a value can hold a function,
and the types that a type contains (see [Recursive types](#recursive-types))
are *facts of the type's definition*. They are computed once per definition and stored as a result of
their own:

- **A fact is a list of conditions.** For `Copyable` and `Plain`, the
  conditions are the types that must have the property for the type to have it,
  or the fact is that the type never has it. For the view property, the
  conditions are the types of which any one makes the type a view, or the fact
  is that the type always is one. `Option` is `Plain` on the condition `Value`,
  and a view on the condition `Value`. The types that a type contains are
  conditions too, each with its occurrence.
- **A query about a type instantiates its definition's conditions with its
  arguments.** Whether `Option[Option[List[Int64]]]` is `Plain` is `Option`'s
  condition for `Option[List[Int64]]`, then for `List[Int64]`, which is never
  `Plain`. No query traverses a type's fields, so a type nested in itself
  cannot be mistaken for a recursive type.
- **Mutually recursive types are computed together.** Such a type is `Copyable`
  and `Plain` unless a part of it prevents that, and it is a view, or contains
  a type, only if a part of it does. So the computation is a fixed
  point: it starts from the facts of the types without fields, and recomputes
  each member's facts from the others' until none changes.
- **An associated type is a condition too.** In `type Kept[Source: Shown](part:
  Source.Part)` nothing is known about `Source.Part`, so `Kept` is a view on
  the condition `Source.Part`. For `Kept[Numbers]`, the condition is
  `Numbers`'s `Part`, which the `impl` of `Shown` for `Numbers` defines. Inside
  generic code, an associated type of a parameter has a property only when its
  trait bounds it, as for a parameter. An associated type that no `impl`
  defines is assumed not to be `Copyable` or `Plain`, and to be a view.

## Checking signatures and definitions

`Interface` checks the externally visible part of each definition
independently, from its resolved form and from the shapes and interfaces of the
definitions that it names. Its result is the definition's interface: the types
of its parameters and result, its `uses`, its bounds, and the facts derived
from them.

### Functions and methods

- **`Self`** is the type in a method's head, the type that is being defined,
  the implementing type of a trait, or the type of an `impl`. Anywhere else, as
  in a function that is not a method or in a capability, `Self` is an error.
  `Self.Name` is an associated type, so it can be written only in a trait or in
  an `impl` of a trait. Only the lowering of a written type knows the meaning
  of `Self`, so only the lowering reports this error.
- **Every type is well-formed:** it has the right number of arguments, its
  value arguments are `USize` constants or value parameters, and every bound
  that the type requires holds. `SortedList[Element]` in a signature needs
  `Element: Ordered` from the signature's own bounds, as in Rust.
- **`self`** can only be the first parameter of a method, and a type can have
  at most one method of each name for each receiver mode. A function that is
  not a method has no receiver even if it declares a `self` parameter, and
  `self` in its body is an error. The type of a method must be defined in the
  same package, and a method of a type that is private to its file must be in
  that file.
- **A default** is a constant expression of the parameter's type that names no
  parameter. A parameter named `result`, or a function named `old`, is an
  error.
- **An `own` parameter of a function type** accepts only functions that capture
  nothing. The interface records these parameters, and the ownership check of
  each caller reads them.
- **The `requires` of a function-typed parameter** is a specification: a `Bool`
  over the named inputs of the function type, with their types, and over the
  parameters before it. It is not part of the parameter's type: two function
  types that differ only in it are the same type. The prover reads it from the
  signature, both to show that the function satisfies it at each call through
  the parameter, and to give its facts to a lambda that is passed for the
  parameter.
- **A private type in a public signature is an error,** and so is a private or
  `internal` type in a visible field of a public type, as in Rust and Swift.
  Callers in other packages could not name the type.
- **Clauses are checked in source order,** each with the earlier clauses in
  scope, as SYNTAX.md describes. `requires`, `ensures`, and `decreases` are
  specifications (see [Specifications](#specifications)). `uses` names
  capabilities or capability parameters. The bound of each `cost` clause is an
  `Integer` expression. `calls(target)` names a parameter of a function type, a
  capability, or a method of a capability; any other target is an error.
  `time(visit)` names a function-typed parameter. `time(Element.equal)` names a
  method of a trait that bounds a type parameter of the definition, or that
  bounds `Self` in a trait. It is a bound on the time of any one call of that
  method. If the bounds have several versions of the method, the term names the
  read-only version.
- **`lends` and `yields`** state how the method lends parts of `self`: `lends`
  exactly once, `yields` any number of times. A lent part still belongs to
  `self`, so `lends` takes no mode or `mut`, and `lends own` is an error. The
  body is checked against the clause (see [Yielding and
  lending](#yielding-and-lending)).
- **`main`,** in a package's `main` module, must have exactly the signature `fn
  main(arguments: List[String]) -> ExitCode`, with any `uses`. A function named
  `main` in another module is an ordinary function.

### Types

- **Fields and variants** are checked like parameters: well-formed types,
  constant defaults, and no two fields or variants with the same name.
- **Invariants and the potential** are specifications, in which `self` is the
  value and the fields of a record are in scope by name. An invariant is a
  `Bool`. A potential is an `Integer`.
- **`derives`** is checked against the shape. Every field must already
  implement the trait, under the same conditions on the type parameters as the
  derived `impl` has, so `Option[Value]` derives `Equal` as `impl Equal for
  Option[Value: Equal]`. Deriving `Ordered` or `Hash` requires `Equal` to be
  derived too. Only a record can derive `Default`, which is the default of each
  field. No variant of a sum type is its default, so that `impl` must be
  written by hand; Rust asks for a variant to be marked instead. Each derived
  `impl` is a definition of its own, as DESIGN.md says, identified by the type
  and the trait.
- **`= todo`** declares a type that can be named and passed, but whose contents
  cannot be used. It has none of the properties above, so it cannot be copied
  and is not a view, until it is defined.

### Traits, `impl`s, and capabilities

A trait, an `impl`, or a capability is checked separately from the methods
written inside it, and neither check depends on the other:

- **The header is lowered alone.** That gives its generic parameters and their
  bounds, the meaning of `Self`, the associated types, and for an `impl` its
  trait, its type, and its `uses`. The lowering reads only the header's own
  tree.
- **Each method is lowered with that header,** which gives the meaning of
  `Self`, of its associated types, and of the enclosing generic parameters. The
  result is a signature like that of any function. A method of an `impl` is
  generic over the `impl`'s parameters and then its own, and uses the
  capabilities that the `impl` uses, as a method written `fn
  List[Element].push` is generic over its head's parameters first. A method of
  a trait is generic over its own parameters only: `Self` and the trait's
  parameters are supplied at each call.
- **A method that an `impl` inherits from its trait has a signature too,**
  although it is not written in the `impl`, and so does a method of a derived
  `impl`. The signature is the trait method's, with `Self` and the trait's
  parameters substituted by the `impl`'s types, generic over the `impl`'s
  parameters and then its own. Code generation and the prover compile and prove
  a method per `impl`, so they demand this signature.
- **The interface is assembled** from the header and the signature of each
  method written inside. A method of a trait is *provided* when it has a body.
  A method whose own signature is broken is listed as broken.
- **Each method is checked against its enclosing declaration as a definition of
  its own:** a method of an `impl` against the method that its trait declares,
  and a method of a trait against the traits that the trait requires. The
  `impl` itself is checked for the members that it must define and does not.

- **The members of a trait** are checked like functions, with `Self` as the
  implementing type and `Self.Name` as its associated types. A trait cannot
  redeclare a method of a trait that it requires, although it can add a version
  with another receiver mode. Traits cannot require each other in a cycle.
- **An `impl` conforms to its trait.** It defines every method without a body
  and every associated type, and nothing else. It may define each associated
  capability set that the trait declares, once, and a set that it leaves out
  is empty. A set is defined from capabilities, capability parameters, the
  sets of the `impl`'s generic parameters, and the sets that the `impl`
  defines before it; a set defined from itself is
  `types.unknown_associated_capability`. Each method has the trait's
  parameter names, modes, and types, with `Self` and the associated types
  substituted; the same result clause; generic parameters with bounds that are
  no stronger; and `uses` that are a subset of the trait method's, in which
  `Self.Uses` is the set that the `impl` defines. Parameter
  names must match because they are part of how a method is called, as Swift
  requires of protocol requirements. Defaults are written only in the trait. A
  method can add `ensures` and `cost` clauses, and can state a `requires`. The
  prover shows that its clauses are no weaker than the trait's, as DESIGN.md
  describes. The `impl`'s clauses are part of its contract, on which a call
  that resolves to the `impl` depends.
- **The traits that a trait requires** must be implemented for the same type,
  under conditions that are no stronger than the `impl`'s.
- **The methods of a capability's `impl`** take the capability's parameters and
  a receiver, `self` or `mut self`. Only a capability's `impl` can have a
  `uses` clause, and its methods use the capabilities that it declares and no
  others: a caller of a capability holds only that capability, so a method of
  the `impl` cannot add `uses` of its own. The methods of a trait's `impl` can
  use only the capabilities that the trait's methods declare. An `impl` of
  `Panic` is an error.
- **A law's proof** names a law of its trait and a type that implements the
  trait. Its body is checked with the law's parameters in scope, as read-only
  locals. Their types are the law's, with `Self` and the trait's parameters
  replaced by the proof's type and trait arguments. The core form of the proof
  has those parameters, so that the prover binds them to the law's values. The
  proof names its type as an `impl` does, with generic parameters of its own,
  which its interface has. The prover checks a law once for every
  instantiation of the `impl`, so the proof's parameters must have exactly the
  `impl`'s bounds: with fewer, the type would not implement the trait, and
  with a bound that the `impl` lacks, the law would be taken as proven for
  types that the proof's reasoning does not cover.
- **A method that overrides a provided method** must have exactly the provided
  method's signature. The provided method must be pure, have a `time` clause,
  and mutate none of its arguments, so that its body can serve as its
  definition. The prover shows that the body is functional and that the
  override returns the same result.

### Recursive types

A type must not contain itself in either of two ways:

| The type contains itself | Failure that the rule prevents | Diagnostic |
|---|---|---|
| in place | The type would have infinite size. | `package.needs_indirect`, with a fix that adds `indirect` to the variant where the cycle starts |
| in the input of a function type that has a `time` clause | A function stored in a value could be called on the value and call itself through it. No call in its code names it, so the prover would accept a `time` clause on a function that does not terminate. | `package.not_strictly_positive`, on the field |

The second rule is strict positivity, applied only to function types that
promise termination. `type Button(on_click: fn(Button))` is legal, because a
function with a `time` clause cannot call a function value whose type has
none. `type Lazy(next: (fn() -> Lazy cost time finite))` is legal, because the
type is in the output. A trait's method may take the type that holds an `any`
of the trait: a call through `any Trait` is a call of the trait's method,
which is an edge of the prover's call graph.

Each type that a value contains has an *occurrence*:

| Occurrence | Where the type is |
|---|---|
| in place | In a field of a variant that is not `indirect`, or in an array |
| indirect | Behind a pointer: in an `indirect` variant, a collection's storage, an `any`, or the output of a function type |
| function input | At any depth in the input of a function type that has a `time` clause |

A type that is contained through another type is a function input if either
occurrence is, in place if both are, and indirect otherwise. The checker
finds every cycle of type definitions that contain each other. A cycle
whose occurrences are all in place is the first error. A cycle with a
function input is the second.

How a generic type contains a type argument is a fact of the generic type's
definition (see [Properties of types](#properties-of-types)). `Option`
contains its `Value` in place. `List` contains its elements indirectly,
through a `Storage`. `type Callback[Input](run: (fn(Input) -> Bool cost time
finite))` contains `Input` as a function input, so `type Wrap(next:
Callback[Wrap])` is an error. A type that contains an associated type of a
parameter, as `type Kept[Source: Shown](part: Source.Part)` does, contains the
type that the `impl` defines for each argument. So `type Tree(kept:
Kept[Marker])` is recursive when `Marker`'s `Part` is `Tree`.

An `impl` can make a type contain itself though no type definition's fields
do. With `type Part = Kept[Marker]` in `impl Shown for Marker`, `Kept[Marker]`
contains itself in place. So the checker also reads the definition of each
associated type, and reports a type that contains itself through that
definition on the `impl`.

These are package checks, over the type definitions and `impl`s of one
package: packages cannot depend on each other in a cycle, so their types
cannot either. They cover the types that only a function names, such as a
parameter of type `Kept[Marker]`. An `impl`'s generic parameters are the
arguments of its type, so the definition of an associated type can use only
the arguments of the type that it is defined for. A type that contains itself
through an `impl` selects that `impl` by a type constructor, and a field or
an associated type's definition on the cycle names that constructor.

A generic type that contains itself with different arguments, as in `type
Nested[Element] = Leaf(value: Element) | indirect Node(inner:
Nested[List[Element]])`, is `package.growing_type`, as DESIGN.md requires:
the type has no fixed set of instances, and generic code is compiled once
for each. A traversal of its own finds it, as in Go's check. Its graph has
the parameters of generic types as nodes. An edge goes from a parameter to
each argument position of a field's type that mentions the parameter, and
the edge grows when the argument is more than the parameter. A type is
growing when a cycle through its parameters has a growing edge.

## Checking bodies

### Bidirectional, one statement at a time

Bodies are checked bidirectionally: an expression is either *checked*
against an expected type, which flows inward from annotations, parameters,
and operators, or has its type *inferred*. Unknown types inside one
statement are inference variables, solved by unification.

**Type inference is local to a statement.** When a statement ends, every
inference variable in it must be solved. A literal whose type is still
undetermined takes its default type, and any other unsolved variable is an
error that asks for an annotation, with a fix that adds one to the `let`. The
type of a local is then fixed for the rest of the body. This is local type
inference, as in Swift, Kotlin, Scala, and C#, in contrast to inference across
a whole body, as in Rust, OCaml, and Haskell:

- **The type of a variable is determined by its declaration,** which is the
  line that a reader, an LLM, and a hover in the language server see. An error
  is reported at the statement that caused it, never at a distant use that
  happened to fix the type of a variable.
- **Checking is local and fast.** Unification never spans more than one
  statement, so its cost follows the size of the statement.
- **The cost is a few annotations.** `var names = []` needs
  `var names: List[String] = []`, and `var best = None` needs a type, as in
  Swift and Kotlin. SYNTAX.md already writes them this way, and
  `var best = 0` is an `Int64`, as SYNTAX.md says.

A statement here is the innermost statement. The statements inside a block that
is part of a larger expression are inferred separately, and the block's tail
expression is checked against the block's expected type.

The scrutinee of a `match` or an `is` is inferred before the patterns are
checked, as if it were a statement of its own, because a pattern needs the type
of its scrutinee. So in `second / 0 is None`, the `0` takes its default type
and the operator's `impl` is selected before `None` is looked up.

### Literals

An integer literal has a literal type that only an integer type can fill, and
a float literal one that only a float type can fill. Literal types are
decided in this order:

1. **By the expected type,** as in `let small: UInt8 = 3` or an argument
   passed to a `UInt8` parameter.
2. **By the other operand,** for arithmetic operators, comparisons, and
   ranges, following Go's rule for untyped constants: in `count + 1`, the
   `1` takes the type of `count` if it can be that type. In `duration * 2`,
   `Duration` is not an integer type, so the `2` is decided by its default.
   An expression made only of literals waits for the same decision as a
   whole, so `count + (60 * 60)` works.
3. **By the default,** `Int64` or `Float64`, at the end of the statement.
   A literal shift amount is a `USize`, as Go's is a `uint`.

This never looks at which `impl`s exist, so adding an `impl` never changes
what an existing call means, as DESIGN.md requires. Once a literal's type is
known:

- **An integer literal must fit** its type, after negation: a `-` applied
  directly to a literal negates the value, so `-128` fits an `Int8`. Negating
  a literal of an unsigned type is an error. A type parameter or associated
  type that an integer trait bounds is an integer type here, and a literal of
  it must fit every built-in type that implements the trait. A `USize` or `ISize` literal
  must fit in 32 bits unless the package's manifest says
  `usize_bits = 64`, as DESIGN.md requires. The standard library, which
  holds the code for each platform, is checked with its target's width.
- **A float literal is rounded once,** from its exact decimal value to its
  type, with ties to even. A literal that rounds to infinity is an error, as
  in Rust.
- **An integer literal is never a float.** `let ratio: Float64 = 1` is an
  error, with a fix that writes `1.0`.

**A character or byte is a tagged string,** `Character"a"` or `UInt8"\n"`,
of type `Character` or `UInt8`. It must hold exactly one Unicode scalar
value, or one ASCII character, with no `${...}`, and the checker records its
value, as for an integer literal. In a pattern it matches
that value, and a range of them, `Character"a"..=Character"z"`, matches the
values between. A range pattern's type must be an integer type or
`Character`.

### Operators

Each operator desugars to a call, so the checker has no operator-specific
rules. The recorded call is the call of the trait method, and its result type
is the method's, which for a comparison is not the operator's `Bool`:

| Operators | Checked as |
|---|---|
| `+ - * / %`, and `-` for negation | The trait method, such as `Add[Right].add`. The `impl` is chosen by the type of the left operand and the type of the right operand, once both are known, and the result is the `impl`'s `Output`. |
| `==` `!=` | `Equal.equal`, whose `Bool` `!=` negates. Both sides have one type. |
| `<` `<=` `>` `>=` | `Ordered.compare`, whose `Ordering` the operator tests. Both sides have one type. |
| `&&` `\|\|` `!` | Built in, on `Bool` |
| `& \| ^ ~` | Built in, on one built-in integer type |
| `<< >>` | Built in. The left side is a built-in integer, and the amount any unsigned integer type. |
| `..` `..=` | A `Range` of one type, an integer type or `Character` for a `for` loop |
| `is` | The pattern is checked against the left side's type, and the result is a `Bool` |
| `==>` | Built in, on `Bool`, in specifications only |

- **Compound assignment** `place += value` checks `place` as an assignable
  place, then `place + value` as above, and records that the operator receives
  the old value as an owned value. If the trait has a version of the method
  that takes `own self`, that version is selected.
- **`+` on strings** is an error, with a fix that rewrites it as
  interpolation.
- **Mismatched integer types,** as in `count == length` with a `UInt32` and a
  `USize`, are an error with fixes that convert one side with `From`, or
  with `TryFrom` when the conversion can lose information.

### Calls and arguments

A call is one of four kinds, decided by its callee:

| Callee | Example | Arguments |
|---|---|---|
| A named function or method | `copy(original, destination: backup)` | Labeled, as below |
| A type or variant before `(` | `Point(x: 0.0, y: 0.0)`, `Some(3)` | Labeled, in any order |
| A function value | `visit(item)`, `compare(left, right)` | By position, with no labels |
| A trait or type name, then a method | `Ordered.compare(first, second)`, `List.length(names)` | Labeled; the first argument is the receiver |

For a named function, arguments are matched to parameters in one pass:

1. An argument `label: value` goes to the parameter named `label`.
2. A bare name, with an optional mode, that matches a parameter's name goes
   to that parameter.
3. Any other first argument goes to the first parameter.
4. Every other argument is an error, with a fix that adds the label when one
   parameter of a matching type is still open.

The arguments must then appear in parameter order; otherwise the call is an
error with a fix that reorders them. An argument for a parameter with a default
can be omitted, and the core form passes `Default` for each omitted parameter,
for the default-presence mask that CODEGEN.md describes. Records and variants differ in
two ways, as SYNTAX.md says: their arguments can come in any order, and only a
record or a variant with exactly one field takes a bare value.

**Lambda arguments are checked last.** The other arguments of a call are
checked first, in order, and unified with the parameters. Each lambda is then
checked against the type of its parameter, which by then determines the types
and modes of the lambda's parameters. Its result type may still be unsolved, as
`Output` is in `items.map(fn(item) { item.name.copy() })`, and the body
determines it. A lambda whose parameter types are still unknown is an error
that asks for type arguments or an annotation. The type of a lambda's parameter
is never inferred from its uses in the body.

**Generic arguments** are inference variables, solved from the arguments
and from the expected type, so `let digest: Array[UInt8, 32] = Array.filled(0)`
takes its length from the annotation. Explicit type arguments, as in
`parse[Int64](text)`, are unified first.

**Bounds are checked wherever generic parameters are instantiated,** whether
the type arguments are written or inferred: at a call, where a function or a
method is used as a value, where a `for` loop calls `each`, and where a generic
type is named or constructed. So `Holder(5)` is an error when `Holder[Value:
Shape]` and `Int64` does not implement `Shape`. Each bound is checked once the
statement has inferred the type that it constrains:

- **The type must implement the trait.**
- **Each associated type that the bound fixes must equal the `impl`'s
  definition of it.** The two are unified, so a bound can determine a type:
  with `fn first_of[Input: Source[Item = Output], Output](input: Input) ->
  Output`, the call `first_of(numbers)` takes `Output` from `Numbers`'s `Item`.
- **A statement reports a bound once,** however many of its parts need it.
  `Holder[Int64].area(Holder(5))` names `Holder[Int64]` twice and calls a
  method that needs `Int64: Shape`, and is one error.

**An `impl` is never chosen from the expected type.** A trait method's
`impl` is chosen by `Self` and by the trait's type arguments, and those come
from the receiver, a type name, or the arguments, as DESIGN.md requires.
`Int64.from(count)` chooses `From[UInt32]` by the type of `count`. Type
arguments written after the trait, as in `Add[Int64].add(left, right)`,
are the ones the call uses.

### Modes at calls

The keyword at a call site must agree with the parameter:

| Parameter | Argument |
|---|---|
| read-only | a place, unmarked, which the callee views; a part that is lent; or a temporary |
| `mut` | `mut place`, or a part that is lent `mut`. A missing mark is an error with a fix that adds it. |
| `own` | `own place`, which moves it; `place.copy()`; a temporary, unmarked; or a `Plain` place or lent part, unmarked, which is copied |

- **Marks are never redundant.** An argument marked `own` that is a `Plain`
  place, or any mark on a temporary, is an error with a fix that removes the
  mark, so each argument has one way to be written. On a receiver, a mark
  also chooses the method's version, as below, so it is never redundant
  there.
- **A mark covers the longest place it can,** and the first method call
  after it takes that place as its receiver, as SYNTAX.md describes.
- **A `mut` mark needs a mutable place.** The place in `mut place`, the
  receiver of a `mut self` method, and the collection of a `for` loop over
  `mut place` must be mutable, by the rule for the left side of an
  assignment in [Statements and blocks](#statements-and-blocks). A `mut`
  mark on any other place is an error.
- **The receiver's mark selects the version of the method.** No mark selects
  the read-only version, and `mut` and `own` select theirs. On a temporary, the
  `own` version is selected if it exists, and the read-only version otherwise.
  A missing version is an error that lists the existing versions.
- **A lent part is neither a place nor a temporary.** The result of a call of a
  lending method, and each field and element of that result, is lent read-only
  or `mut`, according to the method's signature. It takes no mark: the mark
  that selected the method's `mut` version is the mark before the receiver. A
  part lent `mut` can be passed to a `mut` parameter, selects `mut self`
  methods, and can be assigned to; a part lent read-only cannot. Neither can be
  moved to an `own` parameter or an `own self` method, unless it is `Plain` and
  therefore copied.

### Members

`receiver.name(...)` and `receiver.name` are looked up in the receiver's
type:

- **Fields** of a record, when the record's fields are visible here. The
  fields of an opaque type are visible only in its package.
- **The type's own methods,** defined in its package, including those with
  bounds on the type head, such as `List[Element: Ordered].sort`, which
  exist only when the bound holds. A method whose bound fails is an error
  that names the bound, rather than a missing method.
- **Trait methods,** from every `impl` of a trait from the standard
  library, the calling package, or the packages its manifest lists, for the
  receiver's type. For a generic parameter, the methods of its bounds and of
  the traits they require.
- **The prelude's `copy()`,** when the type is `Copyable`.

All versions of a member name are looked up together: the type's own methods
with that name, and the methods with that name of the traits that the type
implements, each with its receiver mode. One function does this lookup for a
method call, a fully qualified call, the `each` of a `for` loop, and the `each`
of a quantifier, and the receiver's mark then selects one version. The traits
must form one family, in which each is required, directly or transitively, by
another. Two unrelated traits with a method of the same name are an error at
the call, whatever their receiver modes, with one fix per trait that writes the
fully qualified call. A method of the type and a method of a trait with the
same name and receiver mode are reported by a package check, at the `impl`. A
name with no member is an error with a fix to the closest member.

`Type.name` is looked up the same way among the type's static members:
variants, constants under the type, methods without `self` such as
`List.with_capacity`, and every method written in full, as in
`List.length(names)`. In a type position, `Items.Element` is an associated
type of a bound.

### Statements and blocks

- **`let` and `var`** check their expression against the annotation, if
  there is one, and then the pattern against the expression's type. The
  pattern must be irrefutable unless there is an `else`, whose block must
  have type `Never`.
- **An assignment's left side must be a mutable place.** A mutable place is
  a `var`, a `mut` parameter, the variable of a `mut` loop, `self` in a
  `mut self` method, a field or an element of one of these, or a part that
  a call lends `mut`. A constant, a `let`, a read-only or `own` parameter,
  and a local that a lambda captures are not mutable.
- **An assignment through an index can insert a key.** For `collection[key] =
  value`, if the collection's type implements the prelude trait `IndexAssign`,
  the statement is a call of its `assign(mut self, key: own Self.Key, value:
  own Self.Output)`, as Swift's subscript setter and Kotlin's `set` are. `Map`
  implements it, so `ports[own name] = 8080` inserts `name` or replaces its
  value. The collection takes ownership of the key, so the key is checked as an
  `own` argument: a place that is not `Plain` must be moved with `own` or
  copied. For any other type, the statement assigns to the place that
  `collection[key]` denotes, which must exist: `scores[i] = 0` needs `i` in
  bounds. A compound assignment such as `ports[name] += 1` reads the place
  first, so it never goes through `assign`.
- **A block's value is its last expression.** Every other statement must
  have type `Unit` or `Never`; any other value is an error with a fix that
  writes `let _ =`, as DESIGN.md requires. An `if` without an `else` has type
  `Unit`. The arms of an `if` or `match` are unified, ignoring arms of type
  `Never`.
- **Loop clauses** are specifications: an `invariant` is a `Bool`, and a
  `decreases` measure and a `cost` bound are integers, as in a signature.
- **`while`** takes a `Bool`. A `while` whose condition is the literal
  `true`, and which no `break` leaves, has type `Never`, as Java and Kotlin
  treat it. Any other loop is a statement of type `Unit`.
- **`for pattern in expression`** has three forms, as SYNTAX.md describes.
  If the expression is a call of a `yields` method, the loop iterates over
  that call, and the loop variable has the mode that the method yields
  with. If it is a cursor, the loop advances the cursor until it is
  exhausted. For any other value, the loop calls the value's `each` with
  the loop's mode; `each` must be a `yields` method. The pattern is checked
  against the yielded type.
- **`return`, `?`, `break`, and `continue`** have type `Never`. `return` and
  `?` belong to the innermost function or lambda: `return` checks its value
  against that result type, and `?` takes a `Result` whose error type is the
  result's error type, or an `Option` when the result is an `Option`.
- **`provide`** is checked as in [Capabilities](#capabilities), and `parallel`
  as in [Ownership](#ownership-moves-loans-and-views).

### Unreachable code

A statement after an expression of type `Never` in the same block can never
run, and is an error with a fix that deletes it, as in Java. This uses types
alone: `return`, `break`, `continue`, `unreachable`, a call that returns
`Never`, an `if` or `match` whose branches all have type `Never`, and a
`while true` that is never left. Nothing is decided from values, so
`if false { ... }` is not reported. A `parallel` or `concurrent` block never
finishes when one of its branches never does, since the block ends only
when every branch has.

### `todo`, `echo`, and `unreachable`

- **`todo` takes the expected type,** and the hole is reported with that type
  and the names in scope, as SYNTAX.md describes. With no expected type, as in
  `let body = todo`, it has the `Hole` type. Every operation on a `Hole` is
  accepted, and its result is a `Hole`, so the rest of the body is still
  checked as far as possible. Its diagnostic states that the type is
  undetermined and lists the uses of the value. `todo` does not make the code
  after it unreachable.
- **`echo expression`** has the type of its expression.
- **`unreachable`** has type `Never`, and the prover must show it is never
  reached.

### Tagged templates and collection literals

- **A tagged template** `Tag"..."` is checked as
  `Tag.from_template(template)`. `Tag` must implement `FromTemplate`, with
  generic arguments inferred from the expected type. Each interpolated value
  is converted to the `impl`'s `Part` through `From`, chosen by the value's
  type. An untagged string's parts must implement `Display`.
- **A `[...]` literal** is an `Array`, a `Set`, or a `List`, by the expected
  type, and a `List` when nothing is expected. Its elements are checked
  against the element type. An `Array` literal must have exactly as many
  elements as its type's length. `[]` and `[:]` need an expected type.
- **`any value`** needs an expected type `any Trait`. The value is owned and
  its type must implement `Trait`, fixing the same associated types.

## Patterns

### Typing patterns

A pattern is checked against the type of the value it matches:

- **A variant** is looked up in the matched type, as SYNTAX.md describes,
  and a record pattern takes the matched type's only shape. The fields of an
  opaque type from another package cannot be matched.
- **Fields** are matched by name: `field: pattern`, a bare name that is a
  field, the only field of a single-field record or variant, and `..` for the
  rest.
- **A literal or constant** must have the matched type. A constant used as a
  pattern must have a type with structural equality (see
  [Properties of types](#properties-of-types)), so that matching it and `==`
  agree, as Rust requires for constants in patterns. A hand-written `Equal`,
  or a derived one over floats, could disagree with matching.
- **A range** has two ends of the matched type, an integer type or
  `Character`.
- **Every alternative of an or-pattern** binds the same names with the same
  types.

**The mode of a pattern's bindings follows the mode of the scrutinee.** A
pattern on a read-only place binds views of its parts. A pattern on a `mut`
place, as in a `mut` loop, binds `mut` borrows of its parts for the arm or the
iteration. A pattern on an owned value binds its parts as owned values. A
`Plain` part is always copied.

### Exhaustiveness and reachability

`Patterns` uses Maranget's usefulness algorithm ("Warnings for pattern
matching", 2007), which OCaml and Rust use, on the vector of scrutinees, so a
`match` on several scrutinees is checked as one. It reads the [core
form](#the-core-form), so it checks the patterns that the prover and code
generation read, including the patterns that `?` desugars to:

- **Constructors** are the variants of a sum type, `true` and `false`, the
  intervals of an integer or `Character` type, which ranges and literals split,
  and constants, which are expanded into the patterns of their values. A string
  type has infinitely many values, so a `match` on a string needs an
  irrefutable pattern. A value that is not evaluated at compile time, such as a
  constant whose value is a call or a value generic parameter, covers only
  itself.
- **An arm with a guard never covers its pattern.** When the guards cover
  everything, the `match` ends with `_ => unreachable`, which the prover
  checks.
- **A missing case** is an error that names one, such as "`Some(Urgent(_))`
  is not covered", with a fix that adds an arm for each missing case with
  `todo` as its body.
- **An arm that earlier arms already cover** is an error, and so is an
  alternative of an or-pattern that the alternatives before it cover. Both
  have fixes that delete them.
- **A pattern in a `let`, a `for`, or a lambda's parameters** must cover its
  type alone.

## Ownership: moves, loans, and views

`Ownership` enforces DESIGN.md's rules on modes, moves, and views within each
function. It prevents use after move, dangling views, mutation of a borrowed
place, and data races. It reads the definition's [core form](#the-core-form)
and the interfaces of the definition's callees.

The check builds a control-flow graph of the body. Each point of the graph
performs one action on one place: a read, a move, a `mut` borrow, an
assignment, or a binding of new locals. The edges follow evaluation order, and
a loop has a back edge. The right operand of `&&` is reached only from where
the left operand is true, and the right operand of `||` only from where it is
false, so each operand has an edge to the operand after it and an edge to the
code after the expression. A lambda's body is a separate entry point, because
it runs when the lambda is called. Three dataflow analyses run on the graph:

- forward: the places that may have been moved before each point;
- forward: the views that each holder may store at each point, where a holder
  is a local or a `mut` parameter that stores a value of a view type;
- backward: the locals that are live after each point.

A specification-only function is not checked. It is never executed, so it has
no moves or borrows.

### Places

A place is a local, a parameter, `self`, or a constant, followed by field
accesses and by indexes of a `List`, a `Slice`, or an `Array`. A constant that
a type declares, such as `UInt8.maximum`, is a place like any other constant.
The checker does not compare index values, so `items[i]` denotes an unknown
element of `items`. An index of any other collection is not a place: it is a
call of the collection's `at`, a lending method (see [Yielding and
lending](#yielding-and-lending)).

Two places *overlap* when one is a prefix of the other. `config.servers` and
`config.clients` are disjoint. `items[i]` and `items[j]` may overlap, and so
may two slices of one collection. Where that matters, the checker reports no
error. It emits a `Disjoint` obligation instead, which the prover discharges,
as DESIGN.md requires for `sort(mut items[..middle])` next to `sort(mut
items[middle..])`.

### Moves

These move a place: `own place`, a `for` loop over `own place`, a `match` on an
owned value, `own base with (...)`, and returning the place. A `Plain` value is
copied instead.

- **Use after move is an error.** A moved place cannot be used until it is
  assigned again, on any path that reaches the use. The error has a note at the
  move, and a fix that inserts `.copy()` at the move when the type is
  `Copyable`.
- **A field can be moved out by itself.** The other fields stay usable, and the
  whole record is usable again once the field is assigned, as DESIGN.md
  describes. The checker tracks moved places by field path.
- **Only an owned place can be moved.** Moving out of a read-only parameter, a
  view, a constant, or an element, as in `own items[i]`, is an error, as in
  Rust. The fixes offer `copy()`, and for an element a method such as `remove`.
- **A place can be moved out of a `mut` borrow if it is reinitialized before
  the borrow ends.** A `mut` parameter, `mut self`, the variable of a `mut`
  loop, a `mut` binding of a `match`, and a lambda's `mut` parameter are
  borrowed from an owner that uses them afterwards. Such a place, or a field of
  it, can be moved with `own` if every path assigns it again before the borrow
  ends:
  - before the function returns;
  - before the loop iteration, the `match` arm, or the lambda ends;
  - in a yielding method, before each `yield`, because the caller's loop may
    `break` there, and the method then never resumes. A lending method always
    resumes after its `yield`, so it may yield while the place is moved out.

  Until the place is assigned, using it is a use after move. So `Option.take`
  is `let taken = own self`, then `self = None`, then `taken`. This is sound
  because a panic ends the program: no code can observe the place while it is
  uninitialized. Rust unwinds, so it forbids the move and offers `mem::replace`
  instead.
- **A local that a value is moved into owns the value.** After `let taken = own
  items`, `taken` has no views, and `items` can be assigned again while `taken`
  is live.
- **Returning a place that is not owned is an error,** with a fix that copies
  it. This applies to the function's tail expression, and to the tail
  expressions of a block, an `if`, or a `match` in tail position.
- **Inside a lambda, a captured local is borrowed,** so it cannot be moved
  there.
- **The result records every move,** by the id of the core node that moves the
  value.

### Loans

A *loan* is a borrow of a place, together with the region of code in which the
borrow is live. A loan is shared or `mut`:

| Loan | Kind | Live during |
|---|---|---|
| A read-only argument | shared | the call |
| A `mut` argument or receiver | `mut` | the call |
| A `let` of a place | shared | the liveness of the binding |
| A value of a view type, such as a slice, a cursor, or a capturing lambda | shared | the liveness of the value |
| The receiver of a lending call | shared, or `mut` when the method takes `mut self` | the rest of the statement |
| A `for` loop's variable | shared or `mut` | the iteration |
| A `provide` of a place | shared or `mut` | the `provide` block |
| An evaluated operand | shared | until its operation runs |

A loan that a value holds is live while the value is live, which a liveness
analysis computes, as in Rust's non-lexical lifetimes. While a shared loan of a
place is live, no code can assign, move, or `mut`-borrow an overlapping place.
While a `mut` loan is live, no other code can use an overlapping place at all.
So `swap(mut first, second: mut first)` is an error, and `mut items.push(9)` is
allowed once `middle` is dead, as in SYNTAX.md's example. A loan of a view is
also a loan of the places that the view views.

The operands of one operation are evaluated in the order written, and a later
operand cannot mutate what an earlier operand evaluated to. The operands are
the arguments of a call, the fields of a constructor, the elements of a literal,
the scrutinees of a `match`, the collection and then the keys of an index, and
the value of an assignment and then the keys of its target.

- **An evaluated operand stays borrowed until its operation runs.** An operand
  that is a place borrows the place, and an operand of a view type borrows the
  places that it views. A later operand can read them, but cannot assign, move,
  or `mut`-borrow them. So `show(items[0], count: grow(mut items))` is an
  error, as in Rust: the call would receive an element of a list that `grow`
  has since mutated. An operand that is a copy borrows nothing.
- **The scrutinee of a `match` stays borrowed while a guard is evaluated.** If
  the guard is false, the later arms are matched against the same value. So a
  guard can read the scrutinee and cannot mutate it: `0 if bump(mut n) => 1` in
  `match n` is an error, as in Rust. An arm's body can mutate it, because the
  arm has been selected.
- **An argument's `mut` borrow starts at the call,** after every argument is
  evaluated. So `mut items.push(items.length())` is allowed, as Rust's
  two-phase borrows allow it. At the call, two places that the call borrows
  cannot overlap if either is borrowed `mut`.

### Views

DESIGN.md's views are second-class: a view never outlives the function that
created it. The checker enforces this without annotations. Every rule below
uses one definition of the places that a value views, `Graph.views_of`.

- **A call's result views every argument that it could borrow from.** A result
  of a view type holds the loan of every argument that the call borrows,
  read-only or `mut`, and that is not `Plain`, and of every argument of a view
  type. So `found.unwrap_or(default: backup[..])` views `backup`, and `mut
  backup.push(9)` is rejected while the result is live. A `Plain` argument,
  such as an index, contributes no loan, so the rule is rarely more
  conservative than necessary.
- **A `mut` argument that can hold views may store the call's view arguments.**
  The callee may store them there, so the place takes on the loans of the
  call's other arguments of a view type. After `mut views.push(data[0..2])`,
  `views` views `data`, and `mut data.push(4)` is rejected while `views` is
  live. A borrowed argument that is not a view, such as the buffer in `mut
  reader.read(mut buffer, limit: 2)`, is not stored: the callee's own check
  rejects that, by the rule on stored views below. So `reader` does not view
  `buffer` afterwards, and the next read into the same buffer is accepted. A
  function argument whose result is not a view is the exception: the callee
  can get no view from it but the function itself, so only a `mut` argument
  whose type can hold a function may store it. A slice is a view, but it holds
  a function only if its elements do, so `mut items.sort_by(fn(first, second)
  { key(first) < key(second) })` is accepted where `items` is a `mut` slice
  parameter.
- **The value of an `if`, a `match`, or a block views what any of its tail
  expressions views.** After `let part = if first { items[..1] } else {
  items[1..] }`, `part` views `items`. A copy of a view has the same views, and
  a record built by `with` views what its base and its new fields view. The
  checker decides this for every kind of expression, with no default case.
- **A place that is assigned a view has the value's views.** After `holder.view
  = data[0..2]`, `holder` views `data`. A variable that is assigned again also
  keeps its earlier views, because the analysis is a may-analysis over all
  paths.
- **A value copied out of a place has the views that the place's root stores. A
  value that borrows a place also views the place.** A value is copied out when
  it is copied or moved: after `let part = items[0..2]`, a value read from
  `part` views `items` and not `part`, so a function can return it when `items`
  is a parameter. A value borrows a place when it is a borrow of the place or a
  slice of an owning collection. So for a value that both owns data and stores
  a view, such as a record with a `String` and a `Slice`, a borrow of the
  record and a slice of its string both view the record, and the record cannot
  be mutated while they are live.
- **A binding of a `match` or an `is` on a place aliases the place,** because
  the binding refers to a part of it. `slot = None` inside the `Some(inner)`
  arm of `match slot` is an error while `inner` is live.
- **A view of an alias is a view of the aliased place.** A local that a `let`
  binds to a place, that a pattern binds to a part of a place, or that a loop
  binds to an element is an alias: it has no storage of its own. So in `match
  self.user { Some(found) => Some(found.slice()) ... }`, the slice views
  `self.user`, and a method can return it, as it can return
  `self.scheme.slice()`. The same `match` on a local gives a view of the local,
  which cannot be returned.
- **A `for` loop's pattern variables view the collection that the loop iterates
  over:** the places that the yielding call's arguments are borrowed from, or
  the places that the cursor views. A variable of a `Plain` type is a copy, so
  it has only the element's own views. After `for part in parts { kept = part
  }`, where `parts` stores slices of `data`, `kept` views `data`.
- **A function can return a view only of its parameters.** A returned value of
  a view type can hold loans only of the function's parameters and of what they
  view. It cannot hold a loan of a place that is dropped when the function
  returns: a local, or a parameter or `self` taken `own`. Such a view would
  dangle. A view that is copied out of an `own` parameter, such as a slice that
  the parameter stored, borrows the caller's data, so it can be returned. A
  borrow of the parameter itself cannot. A method that returns
  `self.items[1..4]` and `Option.unwrap_or` both satisfy this rule.
- **A view stored in a `mut` parameter must not dangle.** A `mut` parameter,
  and `self` in a `mut self` method, outlive the function. So a view that is
  stored in one, by an assignment or by a call that borrows it `mut`, cannot be
  a view of a place that is dropped when the function returns. The caller keeps
  using the parameter, so the places that it views cannot be mutated in the
  rest of the function either.
- **A function stores only the views that it receives as view arguments.** A
  view that is stored in a `mut` parameter must come from a parameter of a view
  type, such as a `Slice` or a function. Storing a view of a parameter that is
  borrowed but is not a view is an error, so `self.view = data[0..2]` needs
  `data: Slice[Int64]`, not `data: List[Int64]`. Callers do not change, because
  a `List` that is passed to a `Slice` parameter converts to a view of it. The
  signature therefore states which arguments the callee may store, and the
  caller assumes nothing more. Rust has the same default: two borrowed
  parameters do not capture each other unless the signature ties their
  lifetimes.
- **A value cannot be self-referential.** `self.recent = self.items[0..1]` is
  an error, because the caller would not know that mutating `items` invalidates
  `recent`.
- **No view crosses the boundary of a capability's implementation.** Code that
  calls `Journal.write(line)` reaches the implementation through the capability
  and cannot see it, so the caller's check cannot track a view there. In a
  method of an `impl` of a capability, two things are errors: storing in `self`
  a view that the method receives, because the caller could drop the borrowed
  data, and returning a view of `self`'s own state, because the next call could
  mutate that state. The implementation stores a copy and returns a copy. A
  view that the implementation was constructed with can be returned unchanged,
  because the code that constructed the implementation keeps the borrowed data
  alive for as long as the implementation is provided.

- **Writing through a slice requires every place that it views to be mutable.**
  A `var` that stores a `Slice` or a `StringSlice` can be passed `mut`, or
  assigned through, only if every place that it views is mutable: a `var`, a
  `mut` parameter, the variable of a `mut` loop, or `mut self`. A slice that is
  stored in a field is read-only whatever the mode of the record, because the
  record's mode does not say whether the viewed place is mutable. A slice
  parameter is writable if its mode is `mut`. The rule applies to the two slice
  types only: a `var` of another view type, such as a cursor, can be passed
  `mut` over a read-only source.

- **A view argument cannot alias a `mut` argument.** A call that takes a view
  and also borrows `mut`, as another argument, a place that the view views is
  an error in either order: the callee could mutate the place while it reads
  the view. The intrinsics that return a view to its owner are exempt.

- **A stored view cannot view a temporary.** A temporary is dropped at the end
  of its statement. So it is an error for a `let` or a `var` to bind a view, or
  a cursor, of an owned temporary that was passed read-only to the call that
  produced the view. The error asks to bind the temporary to a name first, as
  Rust's E0716 does. The same holds for a view of a temporary that is assigned
  to a place, or that is passed to a call together with a `mut` argument that
  can hold views. A cursor views what its call's read-only arguments view, as a
  view would. A string literal without interpolation has static storage, so a
  view of one is accepted.

A value of a view type can be bound by `let` or `var`, stored in local records
and collections, and passed as an argument. It cannot be returned except by the
rule above, and it cannot be used where a `Storable` value is required. A
record or a list that stores a view is itself of a view type, so "a view cannot
escape its function" holds by construction.

An `any Trait` type does not name the type of the value that it holds, so it is
a view type unless `Trait` requires `Storable`. A conversion to `any` has the
views of the converted value. So a record that stores a slice of a local cannot
be returned inside an `any`, and an `any` made from owned data has no views.

A function type does not state whether the function captures, so every function
type is a view type, and the views depend on the value. A conversion to a
function type with more `uses` or weaker costs has the views of the converted
function:

- **A named function, or a lambda that captures nothing, has no views.** It can
  be returned and stored like any `Plain` value.
- **A capturing lambda views each captured variable and its environment
  record.** The environment record stores the lambda's captures. It is a local
  of the enclosing function, whatever the lambda captures, even a parameter. So
  a capturing lambda cannot be returned, alone or inside a record or a
  collection, and cannot be stored in a `mut` parameter. It can be passed to a
  call, and stored in a local record or list. DESIGN.md's replacement for a
  `make_adder` is a record with a method.
- **A function value that is passed to an `own` parameter of a function type
  must capture nothing,** because the callee may store it, and it could then
  outlive its captures. A capturing lambda is rejected there. So is a function
  value that the caller does not own, such as a read-only function-typed
  parameter, because it may be a capturing lambda. The rule applies to a
  parameter that the callee declares with a function type. A generic `own`
  parameter that is instantiated with a function type is not one: the callee
  handles its value as it handles any view, so the view rules above track it.
  That is why a capturing lambda can be pushed onto a local list.

A lambda cannot mutate a captured variable, which is a type error: captured
variables are read-only inside the lambda.

### Owned values where they are required

The initializer of a `var`, the value of an assignment, an `own` argument, a
field, a collection element, a part of a tagged string, and a returned value
must be owned. A place in one of these positions must be marked `own` or copied
with `copy()`, unless its type is `Plain`. Otherwise the error offers both
fixes.

- **The type checker reports a missing mark.** The rule depends on the marks,
  which only the syntax tree records. In the core form, reading a value that is
  not `Plain` out of a place is always a move that the source permits.
- **A returned place needs no mark.** Returning an owned local moves it.
  Returning a place that is not owned, such as a read-only parameter, is an
  error with a fix that copies it.
- **A constant expression is exempt.** The compiler evaluates the value of a
  constant and of a default at compile time, so a constant that is used inside
  one is not moved at run time.
- **A tagged string moves its parts,** because each part is stored in the
  template that the tag receives. A plain string only reads the values that it
  interpolates.
- **A yielded constructor lends its places instead.** In `yield
  Some(self[index])` the field is lent, not moved, so it needs no mark (see
  [Yielding and lending](#yielding-and-lending)).

### Yielding and lending

- **A `lends` method yields exactly once on every path,** as Swift checks its
  `_read` and `_modify` accessors. The checker reports a path that has no
  `yield` or more than one. Every branch of a `parallel` block runs, so the
  yields of its branches are added. A loop is counted by its paths: those that
  reach the end of the body or a `continue` start another iteration, and those
  that `break` or `return` do not, so a body that yields and then returns
  yields once. The yielded part has the mode that the
  signature states, and can be a part of `self` or a value that the method
  created. A `lends` method cannot drive a `for` loop or be pulled.
- **A lending call borrows its whole receiver,** for the rest of the caller's
  statement, read-only or `mut` according to how the method takes `self`. The
  condition of a `while` loop counts as a statement of its own, so a loan that
  the condition starts ends before the body runs. While the loan is live, using
  a `mut`-borrowed place or mutating a place that is borrowed read-only is an
  error. So is passing a place to a call together with a part that it lends,
  when either is `mut`. An index of a collection other than a `List`, a
  `Slice`, or an `Array` is a lending call. So two indexes of a user-defined
  collection are never lent `mut` in one statement, and `grid[a] = grid[b]`
  needs the right side in a `let` first.
- **A yielded constructor lends the places among its fields.** A lookup that
  can fail lends an `Option`, as in `yield Some(self[index])`, and the element
  stays in the collection. So in the constructor directly after `yield`, and in
  a constructor that is a field of it, a field that is a place is lent to the
  constructed value, and needs no `own` and no copy. The place can be anything
  that the method could yield directly: a part of `self`, a parameter, or a
  local.
  - A method that yields or lends read-only lends every place read-only. A
    `Plain` place is copied instead, as in any constructor.
  - A method that yields or lends `mut` lends the places that are marked `mut`,
    as in `yield Indexed(index: index, value: mut self[index])`. When the loan
    ends, such a place has the value that the caller left in the field. A field
    without the mark is an owned value, as in any constructor, so `index` is a
    copy, and a place there that is not `Plain` is an error whose fix adds the
    mark. Two places that are lent `mut` to one value cannot overlap: the same
    place twice is an error, and two indexes produce a `Disjoint` obligation,
    as for two `mut` arguments.
  - A yielded value that lends a place owns nothing. Each of its other fields
    is a constructor or a `Plain` value, such as an index or a slice. An owned
    value there is an error (`ownership.owned_beside_lent`) that asks to bind
    it to a name first: the name is a place, and is lent like the others. A
    yielded constructor that lends no place is an ordinary owned value.
  - A slice is a value, so `rest: self[1..]` is copied, not lent.
  - A method that yields such a value yields places, so it can be pulled only
    where the element is `Plain`.
- **A lent part cannot outlive its loan.** Returning it, storing it, or passing
  it to an `own` parameter is an error unless it is `Plain`. So is binding it
  with `let`, because the binding would outlive the statement. A `match` on a
  lent part binds views of its fields, or `mut` borrows of them when the part
  is lent `mut`.
- **A method can yield a view only of its parameters,** as a function can
  return one. The caller receives a copy of a yielded value of a view type, and
  may store it after the loop or the statement. So `yield buffer[..]`, where
  `buffer` is a local of the method, is an error. The method can yield `buffer`
  itself, which the caller cannot store, or a slice of `self`.
- **A loop that borrows its collection `mut` may mutate it on every
  iteration.** In `for chunk in mut reader.chunks()`, the method may mutate
  `reader` between two yields. So a view of `reader` that the body copied out
  of `chunk` cannot be used in a later iteration or after the loop.
- **A `yields` method may yield any number of times.** A call of it as the
  iteration of a `for` loop drives the loop. A call anywhere else creates a
  cursor. The cursor is a view of the receiver when the method takes `self`,
  and owns the receiver when the method takes `own self`. A method that yields
  `mut` cannot create a cursor, because the cursor would store a `mut` borrow
  between pulls.
- **Whether a cursor can be created is checked where it is created.** Every
  holder of a cursor may pull it: a `next()` call, a `for` loop over it, one of
  the `Cursor` trait's own methods such as `count`, and generic code that
  receives it, as in `List.collect(names.each())`. Generic code is checked
  without knowing its type arguments, so the rule cannot be checked at the
  pull.
- **A pull returns an owned value.** `next()` returns `Option[Element]`. So a
  method that yields read-only views of places, as `List.each` yields
  `self[index]`, can create a cursor only where its element is `Plain`, which
  is copied implicitly in any case. Any named place counts: a field, an
  element, a parameter, or a local. An element of any other type would be
  copied implicitly, which DESIGN.md rules out, so creating the cursor is an
  error that suggests a `for` loop or a method that yields owned values. A
  method that yields only temporaries, such as the results of calls, yields
  owned values, which a pull moves.
- **Whether a method can be pulled is derived from its body,** as DESIGN.md
  says. A `yields` method cannot be pulled if it yields recursively: through a
  `for` loop over a method in its own call cycle. Whether a method yields views
  of places is derived from the body too. Callers read two facts from a
  callee's body: this one, and the task hazard of a method that a `concurrent
  for` iterates over. Each is stored separately from the interface, and a
  caller reads it only when the caller pulls the method or iterates over it in
  a `concurrent for`.

### `parallel`

Each branch of a `parallel` block, and each iteration of a `parallel for`, is
checked as if it ran at the same time as the others, to prevent data races. A
place that one branch mutates, by an assignment, a `mut` borrow, or a move,
must not overlap a place that another branch uses. Two indexes of one
collection produce a `Disjoint` obligation, as above. A use of a view uses the
places that it views, and a write through a slice mutates the places that the
slice views, so one branch cannot push to a list while another reads a slice of
it. The body of a `parallel for` can mutate only its own element and its own
locals.

### `concurrent`

The branches of a `concurrent` block and the iterations of a `concurrent for`
follow the same data race rule as `parallel`. They differ in two ways: `?`,
`return`, `break`, and `continue` can exit a branch early, and a task of a
`concurrent for` outlives the `yield` that started it. That adds these rules:

- **A branch reinitializes every place that it moves out of a `mut` borrow.**
  When a branch exits early, the other branches finish along their own paths,
  and the code after the block does not run. So a branch that moves a value out
  of a `mut`-borrowed place must assign the place again before the branch ends.
  Under `parallel`, the code after the block could do that. A place that is
  moved out before the block must be reinitialized at every `return` in a
  branch, as at any `return`.
- **An early exit from a branch transfers control to the same target as outside
  `concurrent` code,** for this check: a `return` ends the function, and a
  `break` or a `continue` goes to its loop. By then each other branch has
  either not started or run to one of its ends, and each end is checked.
- **A task can keep a borrow or a view only of a place that the yielding method
  cannot mutate or drop.** Each iteration of a `concurrent for` runs as a task,
  and the task outlives the `yield` that started it: the yielding method
  resumes while the task still runs. A place inside a read-only parameter of
  the method cannot change or be dropped while the call runs, so a task can
  borrow it or keep a view of it. A local of the method, and a place inside a
  `mut` or `own` parameter, can change, so a borrow or a view of one would be a
  use after free. A `concurrent for` over a yielding method is therefore
  rejected (`ownership.task_outlives_yield`) when one of the method's `yield`s
  - yields `mut`;
  - lends a place that is not inside a read-only parameter;
  - yields a value that views a place that is not inside a read-only parameter
    or a constant.

  Three cases are decided differently:
  - A method that yields by position is accepted. Its body is a single `for`
    loop over a range of integers, and the loop body is a single `yield`. The
    tasks run as the iterations of that loop, and the method does nothing after
    the loop. `Core_walk.yields_by_position` decides this.
  - An element of a `Plain` type that is not a view is copied to the task. It
    is accepted whatever it was borrowed from, unless the method yields `mut`.
  - For a callee without a known body, such as a trait method that is called
    through a bound, and for a loop over a cursor, the task needs an owned
    element that is not a view, or a `Plain` copy of a read-only one.

  The fact about a method's `yield`s is `Views.task_hazard`. The method's own
  dataflow analysis computes it, and the check of the `concurrent for` reads
  it. A `parallel for` needs no such rule: over a method that does not yield by
  position, the method runs sequentially and each loop body runs inline at its
  `yield`.

## Capabilities

### What code may call

At each point of a body, a set of capabilities is *available*: the function's
`uses`, its capability parameters, and the capabilities that each enclosing
`provide` provides. In a method of a capability's `impl`, the available set is
the `impl`'s `uses`, which apply to each of its methods. An indirect call in
such a method can also use the implemented capability itself, meaning this
implementation, so that the method can pass its own implementation on to a
callback; code generation passes the implementation's own evidence. A direct
call of the capability from the method would call the implementation itself, so
it needs the capability among the `impl`'s `uses`, provided from outside.

The check runs on [the core form](#the-core-form), where every call is a node,
including the calls that desugaring introduces. So a `for` loop over a
collection needs the capabilities that the collection's `each` uses, and an
interpolated string needs the capabilities that the `display` of each value
uses. A definition with an error has no core form, so it is not checked until
the error is fixed.

- **A capability call,** such as `Clock.now()`, needs its capability to be
  available.
- **A call of a function with a `uses` clause** needs every capability in the
  clause to be available, after its capability parameters are substituted.
- **An indirect call** needs the capabilities in the `uses` of the function
  value's type.
- **The `next` of a yielding method's cursor needs the capabilities in the
  method's `uses`,** at each call of `next` and at a `for` loop over the
  cursor, because `next` runs the method's code. Making the cursor needs them
  as well. This prevents a function without a `uses` clause from running the
  method's code, and it prevents a use after free: a cursor that kept the
  implementation it was made with could run after the `provide` block of that
  implementation had ended.
- **A call of a trait's method needs the method's `uses` for the type that it
  is called on.** `Cursor.next` declares `uses Self.Uses`. For a type whose
  `impl` is known, `Self.Uses` is the set that the `impl` defines, and for the
  cursor of a yielding method it is the method's `uses`. For a generic
  parameter `Source`, it is `Source.Uses`, which is available only where the
  enclosing function declares it. So a generic function that advances a cursor
  declares `uses Source.Uses`, a call of the function needs the capabilities
  of the cursor that it passes, and no function without a `uses` clause runs
  code that uses a capability.
- **A call of an intrinsic needs the capabilities that `Intrinsic.uses` lists
  for the operation.** An intrinsic has no signature with a `uses` clause. A
  method of an `impl` of a capability is exempt: it can call an intrinsic
  without those capabilities. Its callers reach it only through a capability
  call, which their signatures declare, so no code without capabilities can
  observe what the intrinsic does. A capability is not a trait, so the method
  cannot be called on the value, through a bound, or through `any`. A lambda, a
  `parallel` branch, and a helper function inside the method are not exempt.
- **A lambda's body can use the capabilities in the `uses` of the lambda's
  type,** which is the function type that the lambda is checked against.
- **A capability parameter is instantiated with a set of capabilities, which is
  inferred at each call of its function or method.** A call of
  `for_each[capability Granted]` has its own set for `Granted`, as it has its
  own type for a type parameter. Only a function or a method takes a
  capability parameter: a type argument is a type or a `USize` value, so no
  argument could be written for a capability parameter of a type or of a
  trait, and no signature or field could name the type
  (`types.misplaced_capability_parameter`). The set appears in every type
  that was instantiated from that use: the function type that a lambda is checked against, the type
  of the call's result, and the type of a local that stores the result. It is
  the least set that satisfies the constraints on it: the capabilities that
  each function converted to such a type uses beyond the `uses` of the type,
  and the capabilities that a lambda's body needs beyond the `uses` of its
  type. So `for_each(3, visit: tick)` needs `Clock` when `tick` uses it and
  `visit` is a `(fn(Int64) uses Granted)`. After `let kept = later(tick)`,
  where `later` returns its argument, `kept` is a `(fn() -> Instant uses
  Clock)`, and calling it needs `Clock`.
- **The sets are solved after the whole definition is checked,** because a
  constraint on a set can be anywhere in the definition: a `var` that stores a
  call's result may be assigned another function later. Until then a set is a
  capability variable in the types that contain it, and it affects nothing else
  about those types. Where a type with a capability variable is checked against
  a type that lists capabilities, the solved set must be a subset of them, or,
  where the two types must be equal, equal to them. Every type that the checker
  outputs has the solved set in place of the variable, and the type arguments
  of each call have the solved set for the capability parameter.
- **A function's own capability parameter is rigid in its body:** it equals
  only itself. Inside `for_each`, a `(fn(Int64) uses Granted)` accepts only
  functions that use `Granted` or nothing. A recursive call of `for_each` is a
  call like any other, with its own set, which is `Granted` when it passes its
  own callback on.
- **A specification has no capabilities at all, not even `Panic`,** because a
  specification must denote a value. This applies to the clauses of a contract,
  the `requires` of a function-typed parameter, the clauses of a loop, the
  invariant and the potential of a type, a law, a proof, and the body of a
  quantifier, whatever the enclosing function declares. **A `parallel` branch
  and the body of a `parallel for`** have only `Panic` available. A test
  without `uses` has only `Panic` and the capabilities that it provides.
- **`concurrent` code needs `Tasks`,** at a `concurrent` block and at a
  `concurrent for`, as a call needs the capabilities that its callee uses. Its
  branches and iterations have the capabilities that are available at the block
  or the loop.
- **An unused `uses` clause is not an error,** because a function may declare a
  capability that a later version will use, and callers already provide it.

### `provide`

`provide implementation, ... { body }` checks each implementation like an
argument: a temporary is owned, a place is borrowed read-only, and `mut place`
is borrowed `mut`. The provided capabilities are all the capabilities that the
implementation's type implements. They are found by looking up the capability
`impl`s for the type in the type's own package and in the packages of the
capabilities that are visible here. A place must be marked `mut` exactly when
one of those `impl`s has a method that takes `mut self`, with a fix that adds
or removes the mark. The capabilities that each `impl` uses must be available
at the `provide`. No value can provide `Panic`, because no type can implement
it.

Where the body of a `provide` can use `Tasks`, an implementation that is
provided `mut` is a monitor, as DESIGN.md describes: each call of its methods
runs to completion before the next call starts.

- **The body can use `Tasks`** when it contains `concurrent` code, or when a
  call in it uses `Tasks` or a capability parameter, which may be instantiated
  with `Tasks`. `Core_walk.can_use_tasks` decides this from the core form,
  after the capability sets are solved. Code generation calls the same
  function, so the two stages agree on which implementations are monitors.
- **A monitor needs `Tasks` at its `provide`**
  (`capabilities.monitor_needs_tasks`). Code generation locks each method of a
  monitor through `Tasks`, using the implementation of `Tasks` in the same
  `provide`, or else the one that is available at the `provide`. If the body
  uses `Tasks` itself, in `concurrent` code or in a call that uses `Tasks`, and
  neither exists, then the only implementation of `Tasks` is in a nested
  `provide`. The methods would have no lock, and two tasks could run a `mut
  self` method at the same time, which is a data race. So that case is an
  error. A body that can use `Tasks` only through a capability parameter is
  accepted: each instance of the function has evidence for `Tasks` at the
  `provide` exactly when the parameter is instantiated with `Tasks`, and code
  generation adds the lock in those instances. An implementation of `Tasks`
  itself is not a monitor.
- **A capability that a monitor implements has no method with a callback
  parameter that can use a capability** (`capabilities.callback_may_deadlock`).
  A parameter's type counts when it is a function type with a `uses` clause, an
  `any` type or a bounded type parameter whose trait has a method with one, or
  a type that contains one of these at any depth. Called while the monitor is
  held, such a callback could enter the monitor of a nested `provide`, and two
  tasks could deadlock. The error is reported at the implementation in the
  `provide`.

### Dependency grants

DESIGN.md says that a dependency can use only the capabilities that its
manifest entry grants, and that a grant is checked wherever the dependency's
code is referenced. The type checker enforces this from the signatures of the
dependency's code, never from its bodies. Every capability in those `uses`
clauses must be granted, except a capability that comes from a capability
parameter, which is the caller's own. A dependency's code is referenced by:

- **A call** of its function or method, or of a method of its trait, and of the
  `impl` method that the call resolves to, when the `impl` is known.
- **A function value of its function,** because any holder of the value can
  call it.
- **Its `impl` satisfying a bound.** This is checked in the one function that
  resolves a bound: for the type arguments of a call, for the arguments of a
  written type, for `any value`, and for the bounds that an `impl` must itself
  satisfy. The check covers the resolved `impl` and, recursively, the `impl`s
  that satisfy its own bounds, as the `impl` of `Source` for `List[Timer]` is
  satisfied through the `impl` for `Timer`. The methods of an `impl` can use
  only the capabilities that their trait declares, so only a trait whose
  methods have `uses`, or an `impl` of a capability, ever needs a grant here.
- **A `provide`** of its type, for the capabilities that its `impl`s use.

Inside the dependency, its bodies are checked against its own signatures, so
its code cannot use more than its signatures declare.

- **A grant is one query,** keyed by the package and the dependency: the
  capabilities that the manifest entry names, each resolved to a definition. A
  prelude capability is named by its name and any other capability by its full
  path, so two capabilities with the same name are never confused.
- **A package that the manifest does not list is granted nothing.** That
  catches an `impl` in a transitive dependency.
- **The error names the code and the capability,** and states which entry needs
  which grant. It has no fix: by DESIGN.md, a grant is always a deliberate
  choice. A dependency that offers both a client and a server needs only the
  grants for the part that the program references.

### The manifest

The result of each definition lists the packages that it uses. The union over a
package's definitions, excluding its tests, is the dependency list that `truss
publish` publishes. Two rules about a package's manifest need the package's
code too, so they are package checks, reported at the manifest's file and not
in a module:

- **A grant that names no capability** is an error, so that a misspelled
  capability is not silently never granted.
- **An unused dependency** is an error, like an unused `use`. A package uses a
  dependency by naming it in a path, by calling a method of one of its traits
  with a dot, or through an `impl` of it that a call resolves to or that
  satisfies a bound. The check takes the union of the packages that each
  definition's result lists. It runs only on a package whose code all checks,
  because a call in a body with an error may not have been resolved. The fix
  deletes the entry.

## Traits and `impl`s across a package

These checks look at more than one definition, so they are package checks,
each its own query.

### Where an `impl` may live

An `impl` must be in the package of the trait, of the implementing type, or
of the outermost type of one of the trait's arguments. So
`impl Multiply[Vector] for Float64` can live with `Vector`, and
`impl From[UserId] for Int64` with `UserId`. Packages cannot depend on each
other in a cycle, so for any pairing only one package can name every type
involved, and there is never more than one place an `impl` could be.

### Overlap

A type constructor has at most one `impl` of a trait for each list of trait
arguments, for all of its own type arguments. Two `impl`s of one trait for one
type constructor overlap when their trait arguments unify, where each `impl`'s
generic parameters are unification variables. So `impl Add[Element] for
Vector[Element]` and `impl Add[Int64] for Vector[Element]` together are an
error. A blanket `impl`, for a bare generic parameter, would cover every type
that satisfies a bound, and is not allowed, as DESIGN.md says.

### Finding an `impl`

To resolve the `impl` of a trait for a type, the checker searches only the
packages that the orphan rule allows: the trait's package, the type's package,
and the packages of the outermost types of the trait arguments. Each lookup is
one query, such as "the `impl`s of `Add` for `Instant` in the package of
`Duration`", so adding an `impl` re-checks only the definitions that made that
lookup.

An associated type is read from the `impl` whose head matches the type, whether
or not the bounds on that `impl`'s parameters hold. `impl`s do not overlap, so
no other `impl` could define it, and a bound that does not hold is reported
where the trait is required. Normalizing the associated type therefore reads
nothing about the type's arguments. That is why a property of a type can depend
on an associated type without a query cycle.

### Method names

A method is its name and how it takes `self`. A type's own method and a
method of a trait the type implements cannot be the same one. A trait's
method may be another version of a type's own only when an `impl` in the
type's package writes it: one left to the trait's provided body, or given
by an `impl` in another package, cannot use a name the type's methods have
at all, as DESIGN.md says. Neither can share a name with a constant of the
type. The error is reported at the `impl`, wherever it is.

### `any`

- **`any Trait` fixes every associated type** of the trait, as Rust requires
  of `dyn`, since a method mentioning one could not otherwise be called.
- **`any Trait` fixes every associated capability set to the empty set.** A
  call through `any` therefore needs no capability for `Self.Uses`, and
  `any value` is `types.no_impl` when the `impl` for the value's type defines
  a set that is not empty, or when the type is a generic parameter, whose set
  is not known. Otherwise a function without a `uses` clause could call the
  method through `any` and run code that uses a capability.
- **A method is object-safe,** and can be called through `any`, when it has a
  receiver (`self`, `mut self`, or `own self`), has no generic parameters, and
  names `Self` in no parameter type and not in its result type, at any depth.
  So `Cursor.skip`, which returns `Skip[Self]`, is not object-safe. An
  associated type of `Self`, such as `Self.Element`, is allowed, because the
  `any` type fixes it. A call of any other method through `any` is an error at
  the call. Code generation uses the same function to give the method table of
  an `any` value a slot for exactly these methods.

### Instantiation cycles

Generic code is compiled once for each set of type arguments, so generic
code may not instantiate itself with growing arguments, as DESIGN.md says.
Each checked body records its *instantiation edges*: each generic definition
it calls, with type arguments written in terms of its own type parameters.
A package check builds the graph of these edges and reports a cycle in which
some edge's arguments put a parameter inside a type constructor, as
`f[Element]` calling `g[Option[Element]]` calling `f[Element]` does. This is
Go's check. Calls cannot cycle between packages, so the graph is one
package's.

## Specifications

Specifications are `requires`, `ensures`, invariants, laws, `decreases`,
`cost`, theorems, `proof` blocks, and `proof` definitions. The checker
checks them like code, with these differences:

- **Integer arithmetic is exact,** through the prelude type `Integer`, as in
  Dafny. Every built-in integer type is a subset of `Integer`: arithmetic on
  built-in integers gives an `Integer`, and comparisons may mix any integer
  types. An `Integer` may stand where a built-in integer type is expected, as
  in `items[i + 1]`, and the checker records an obligation that it fits. A
  literal that nothing else decides is an `Integer`. Float arithmetic keeps
  its types, since it follows IEEE 754 in specifications too.
- **The types of specifications** are `Integer`, `Sequence`, `FiniteSet`,
  `FiniteMap`, and `Multiset`, which the compiler declares. A function that
  mentions one in its signature, or a method of `Model`, can be called only
  from specifications, and is never compiled. Its body is a specification.
  That is how a specification function such as
  `fn sum(items: Slice[Int64]) -> Integer` is written. A `[...]` literal is
  a `Sequence`, a `FiniteSet`, or a `FiniteMap` where one is expected.
- **Everything is pure.** No capability is available, not even `Panic`, and
  `echo` is not allowed.
- **Every function called must be pure and have a `time` clause,** so that
  it is known to terminate, as DESIGN.md requires. Both are facts of the
  callee's interface.
- **`forall` and `exists`** bind a pattern over a range or a collection, or a
  name over a type. Their bodies, and `==>`, are `Bool`. A quantifier over a
  range or a collection is an expression in code as well; one over a type, and
  `==>`, are errors in a body that is compiled, which the parser leaves to this
  stage since only the signature's types say whether a body is. In executable
  code, a quantifier is a loop for the ownership check too: it borrows the
  collection for its body, so the body cannot mutate the collection that it
  iterates over.
- **`log` and `power` are specification functions.** A call of `log(n)` or
  `power(base, exponent)` by bare name is the function on `Integer` that a
  `cost` bound uses. In a `cost` bound the names always mean these
  functions. In any other specification, a local or a definition of the
  file with the same name takes precedence. `time` and `calls` are cost
  functions only.
- **Theorems** are called only from proofs, and a call makes their `ensures`
  available. `assert` is only in tests, theorems, and proofs.

## Constants

A constant's type is written, and its value is checked against it as a
constant expression: literals, arithmetic, other constants, and records,
variants, lists, maps, arrays, sets, strings, and tagged templates without
interpolation, built from constant parts. A call is an error. A default of
a parameter or of a field follows the same rules, and names no parameter.

Whether an expression is constant is read from the types, resolutions, and
calls that the checker records, not from how it is spelled:

- **Arithmetic is an operator on built-in integers, floats, and `Bool`:**
  the arithmetic, comparison, logical, and bitwise operators, and shifts. An
  operator that a type's `impl` defines, such as `==` on a `String`, is a
  call.
- **A name is constant when it means a definition:** another constant, a
  variant, or a function taken as a value. A field of a constant record is
  constant.
- **A call is constant only when it builds a record or a variant.** An
  index is a call of `at`.
- **Anything else is not:** a branch, a block, a lambda, a string with
  interpolation.

So a constant uses no capability and always ends, and every build works it
out alike.

The checker works out a constant's value only where it needs the value: a
`USize` in a type argument, as in `Array[UInt8, digest_size]`, and a constant
used as a pattern, for exhaustiveness. It does so exactly, and needs no code
to run: integers are Zarith's, and float operations are the exact IEEE ones,
which OCaml computes bit for bit. A `Float32` is computed in 64 bits and
rounded to 32, which gives the correctly rounded 32-bit result for `+`, `-`,
`*`, `/`, and `sqrt`, because 53 bits is more than twice 24 plus 2. Overflow
in a constant's arithmetic is an error, and so is dividing by zero: each
step of `+`, `-`, `*`, `/`, `%`, and negation on built-in integers must fit
its type, so `let small: UInt8 = 200 + 100 - 100` is an error at
`200 + 100`. Constants that refer to each other
in a cycle are an error. Every other constant is built by code generation,
which runs compiled code for one whose value cannot be folded, such as a
`Map` or a `Set`, as CODEGEN.md describes. A result that used a constant's
value reads that value, so changing the constant's expression in a way that
keeps its value checks nothing again.

## Tests

A test's body is checked like a function's that returns `Unit`, with the
capabilities it declares in `uses` and `Panic`. A capability its code uses
that it neither declares nor provides is an error. Two tests with the same
name in one package are an error.

## The tables

The checker publishes four tables of each definition, keyed by the tree's node
ids (see [Node identity](#node-identity)). Tools read them, because they answer
questions about the source as it is written, including code with errors: the
type at a position, the resolution of a name, the holes. The usage check reads
them to find the statements that diverge. Every other check, the prover, and
code generation read [the core form](#the-core-form) instead, which exists
only for a definition without errors. The tables record:

- **the type of every expression and of every binding,** with no inference
  variables
- **the resolution of each name and member:** the definition and its type
  arguments, the field or variant, and each normalized associated type
- **the callee of each call of a named function or a type's own method**

While it checks a body, the checker fills more tables, which are private to it
(`Tables` in `stage0/infer`): each call in full, with the `impl` chosen for a
trait method, the parameter and mode of each argument, the omitted defaults,
and the capability set; the value of each literal; the variant or record of
each pattern and the type of its scrutinee; the iteration of each `for` loop;
the conversions of each template; and the mode of each lending call. The
checker builds the core form from them. What a `provide` provides, and the
obligations that the type checker creates, are in the core form only.

The tables are canonical, so that two checks of the same definition give equal
results, and the database saves them with the graph, as DATABASE.md describes.

### The core form

The core form is the type checker's output for one definition: a typed,
desugared tree. Ownership checking, the prover, and code generation read it
instead of the syntax tree, and none of them repeats a decision that the
type checker made.

A definition has a core form if it parsed completely and has no error. A
definition with an error has none, and no later stage runs on it.

The core form records these decisions:

- **Calls are resolved.** Every call names its callee and has one argument per
  parameter, in parameter order. The receiver of a method is the first
  argument. An omitted argument is marked as a default, and the default
  expression is in the callee's own core form. A callee is a function or a
  method of a type with its type arguments, a trait method with the evidence
  that selects its `impl`, a capability method, an operation of
  `standard::intrinsic`, or a function value (an indirect call). The cursor of
  a yielding method has a compiler-generated `impl` of `Cursor`, identified by
  the method, as a derived `impl` is identified by its type. So a provided
  method of `Cursor`, such as `count`, is called on such a cursor like any
  trait method, with that `impl` as its evidence. The cursor's `next` runs the
  method's own code, and has its own kind of node, as `copy` has.
- **Every expression is a place or a value.** A place is a local, a
  constant, a field of a place, the result of a lending call, or a
  temporary that holds a value for the enclosing statement. An index
  expression is a lending call of `Index.at`. Every place carries its type.
- **An operand is a borrowed place or a value.** The operands are: an argument,
  the scrutinee of a `match`, a `let`, or an `is`, the operand of a `yield`, a
  field of a constructor, an implementation in a `provide`, an indirect callee,
  an interpolated value, and the cursor of a loop. Reading a value out of a
  place has its own kind of node. It copies the value if the type is `Plain`
  and moves it otherwise. Code that only borrows a place never has that node.
- **A field of a constructor is a place only in a yielded constructor.** A
  field that is a value is moved into the constructed value. A field that
  is a place is lent to it, with the mode of the `yield`: the constructed
  value holds the place's value and does not own it. Only the constructor
  that is the operand of a `yield`, and a constructor that is a field of
  one, has such a field. If it has one at any depth, each of its other
  fields is a place, a constructor, or a value of a `Plain` type, so the
  yielded value owns nothing and nothing drops it.
- **Operators are resolved.** An arithmetic, bitwise, or shift operator on
  built-in types is one node that holds the operation, whether it was
  written `left + right` or `left.add(right)`. A comparison of built-in
  values is a comparison node. For any other type, `==` is a call of
  `equal`, `!=` is the negation of that call, and an ordering operator is a
  call of `compare` followed by a test of the resulting `Ordering`. In a
  specification, arithmetic and comparisons work on `Integer`, so built-in
  integer operands are converted first.
- **`concurrent` code lists the tasks that an early exit terminates.** A
  `concurrent` block has its own kind of statement, next to `parallel`, and a
  `for` loop records whether its iterations run sequentially, in parallel, or
  as tasks. A `return`, a `break`, or a `continue` that exits a branch or an
  iteration is wrapped in a node that lists the tasks that it terminates,
  innermost first: the branch of a block, by the block and the branch's index,
  or an iteration of a loop. A `?` in a task is the `match` it always is, with
  its `return` inside that node. A `continue` of a `concurrent for` itself only
  ends its own iteration, so it is not marked. An exit inside a lambda leaves
  no task.
- **Syntactic sugar is desugared.**
  - `?` is a `match` that evaluates to the success value or returns the
    failure.
  - A compound assignment such as `total += step` evaluates its target
    once, and assigns the result of the operator applied to the target's
    current value.
  - A `for` loop over a collection is a loop over a call of the
    collection's `each`.
  - A quantifier over a collection, in code that runs, holds the same call
    of `each`, read-only, so it runs as that loop does and stops at the
    first answer. In a specification it holds the collection and no call.
  - A range expression used as a value is a `Range` record.
  - A variant constructor used as a function is a lambda that constructs
    the variant.
  - `config with (port)` is `config with (port: port)`.
  - A list literal is a block that allocates storage with capacity for the
    elements, pushes each element, and converts the storage to a list.
  - A set or map literal is a block that creates the collection with
    capacity for its entries and inserts each entry. A map literal inserts
    with a method that requires the key to be absent, so the prover checks
    that the keys are distinct as it checks any `requires`. An empty
    literal is the call that creates the collection.
  - An owned collection passed where its view is expected, such as a
    `String` passed as a `StringSlice`, is a call of `slice`.
  - A tagged string is a call of the tag type's `from_template` on a
    `Template` record. The node also keeps the literal text segments,
    because the prover evaluates the tag's `requires` clauses on them.
- **Some constructs keep a node of their own.** A slice expression such as
  `items[1..3]` names the place it views, and holds the call of the base
  type's `slice_range` that creates the view. The bounds of that call are
  already computed: a missing start is `0`, a missing stop is the length of
  the base, and an inclusive stop is `stop + 1`. An array literal is
  constructed in place. A specification's sequence, set, or map is never
  constructed at run time. An interpolated string is a block of calls: of
  `TextBuilder.new`, of `TextBuilder.write` for each piece of text, of the
  `display` of each value, and of `TextBuilder.finish`. So each call has the
  termination and cost obligations of any call. Widening a function value, and
  converting between a built-in integer and `Integer`, are explicit
  conversion nodes.
- **A cost term over a bound names the trait method.** `time(Element.equal)`
  in a cost bound is a node that holds the trait method, with the type
  parameter as its self type.
- **Every node has a type.** The type is fully inferred and normalized. It
  contains no inference variable and no hole.
- **A condition records whether it is executable.** A `requires` clause or an
  `assert` is executable if it can be evaluated at run time: it contains no
  quantifier, no `Integer` value, no `old` or `result`, and no call of a
  specification-only function.
- **A block records whether it diverges.** A block diverges if control never
  reaches its end. The code after a `return`, or after a loop without an exit,
  is then known to be unreachable without inspecting types.
- **A definition's core form holds its checked parts.** For a function:
  the parameters, with their defaults and the `requires` clauses of a
  function-typed parameter, the contract, and the body. For a type: the
  field defaults, the invariants, and the potential. For a trait: its laws.
  For a constant: its value. For a test or a law proof: its body.

#### Ids and origins

Every node has an id that is unique within the definition. Later results
are keyed by it. Every node also has an origin: the id of the syntax node
it was built from. A diagnostic uses the origin to find the source text to
quote. Several core nodes can share one origin: `total += step` produces
both a call and an assignment.

Core nodes hold no source spans, so reformatting a definition does not change
its core form. The span of each syntax node, by id, is a separate result, which
only code that displays source text demands.

#### How the core form is built

When the type checker checks an expression, a statement, or a pattern, it
registers a function that builds the core node. These functions run after
the whole definition is checked. Only then is every type final, and some
choices, such as the `impl` an operator resolves to, are made at the end of
a statement.

The check described in [What code may call](#what-code-may-call) runs on
the core form, and it solves the capability variables, because only the
core form has every call. If the definition has capability variables, the
core form is built again after they are solved, so that its types contain
the solutions.

#### Holes

A `todo` with no expected type has a hole type, and so does everything
computed from it. The type checker accepts any operation on a hole without
resolving it. Evaluating a hole never returns, because the `todo` it comes
from stops the program. The core form relies on that, so that it holds no
operation that the checker did not resolve:

- A hole type is `Never`.
- A use of a local whose type is a hole is a `todo`.
- A pattern that matches a hole is a wildcard.
- An expression with an operand whose type is a hole is a block that
  evaluates the operands in order and ends in a `todo`.
- A `for` loop over a hole, or an assignment to one, only evaluates the
  hole.

#### Invariants

A test checks the following on the core form of every definition in the
standard library, and of every program that a test of the type checker, of
ownership, or of the prover accepts:

- Node ids are unique.
- No type contains an inference variable, a hole, or an error.
- Every generic parameter that appears is declared by the definition or by
  its enclosing type, trait, or `impl`, and never by a callee.
- A `mut` parameter receives a place or a slice, and an `own` parameter
  receives a value.
- A place that is assigned, passed `mut`, or advanced as a cursor is
  mutable: it is not a constant, and every lent place in it is lent `mut`.
- A `let`, a `match`, or an `is` on a value binds every name `own`. A `let`
  that binds a mutable local receives a value.
- The alternatives of a pattern bind the same locals, with the same types
  and modes.
- Every use of a local has the type of the parameter or pattern that binds
  it.
- A loop over a call iterates over a call of a yielding method.

#### Derived methods

A method of a derived `impl` has no source, so its core form is generated
from the type's definition. It is the body that the method would have if it
were written by hand:

- **`equal`** tests that the other value is the same variant, and then
  compares each pair of fields with `&&`, so it stops at the first
  difference.
- **`hash`** writes the variant's index, counted from 0 in declaration
  order, and then hashes each field.
- **`compare`** orders by variant index. For two values of the same
  variant, it compares the fields in declaration order, and the first pair
  that is not equal decides. It is the only method that reads the
  declaration order of fields.
- **`default`** constructs the record from the default of each field.

For a sum type, the method matches on `self`, and inside each arm it
matches on the other value, with patterns that bind the variant's fields.
The fields of a variant are reachable only through a pattern, in a derived
method as anywhere else. Each field's method is a call of the trait method
on the field's type, with the `impl` for that type, or with a bound if the
type is a generic parameter.

The core form is generated once per method, not once per instantiation. A
method that the trait defines with a default body, such as `not_equal`,
uses the trait's core form, as in any `impl` that inherits it. A type whose
definition is still `todo` has no derived core forms.

#### The core form of a path

Code generation and the prover ask for the core form of a function or
method by its path. There are three cases:

- A function or method with a written body has its own core form.
- A method of a derived `impl` has the generated core form.
- A method that an `impl` inherits from its trait has the core form of the
  trait's default method, together with a substitution that maps `Self` and
  the trait's generic parameters to the types of the `impl`.

### Obligations the type checker creates

Most proof obligations come from the program itself: every index, every
arithmetic operation, every `requires` at a call, every invariant. The
prover finds those in the core form. A few come from decisions the type
checker made. The core form marks the second with a conversion node and the
third with a flag on the `match`, and the ownership check's result lists
the first:

| Obligation | From |
|---|---|
| Two indexes or ranges of one collection do not overlap | Loans of `items[i]` and `items[j]`, or two slices, that would otherwise conflict |
| An `Integer` fits the built-in integer type expected | `items[i + 1]` in a specification |
| A guarded `match` is covered | `_ => unreachable` after guards |

## Dependencies

A result depends on exactly the queries that it demanded through `Query`. The
database propagates a change in any of them to the results that read it:

| Dependency | Example |
|---|---|
| The resolved form of a definition, or a part of it | The body of `parse_config` |
| The interface of a definition | The interface of `List.push` |
| The shape of a type | The shape of `Point` |
| The facts of a type's definition | The conditions under which `Option` is `Plain` |
| The value of a constant | `digest_size` |
| The definitions of one name in a file | The definitions named `count` in `report.truss` |
| A module | Whether `standard::json` exists, and its visible names named `parse` |
| The members of a type with one name | The members of `List` named `length` |
| The traits of a package that declare a method with one name | The traits of `standard` with a method `compare` |
| One field of a package's manifest | The modules of `weather`, or its dependencies, or the width of its `USize` |
| The `impl`s of a trait for a type constructor, in one package | `Add` for `Instant`, in the package of `Duration` |
| The capability `impl`s of a type | The capabilities that `MemoryFiles` implements |
| A body fact | Whether `Tree.each` can be pulled |
| A manifest entry | The capabilities granted to `http`, each resolved to a definition |

A lookup across a package is a lookup in an index that is built from the
declarations of the package's files, and from nothing else:

- **A package's declarations are listed once,** and each index is one pass over
  that list: its methods and member constants by owner and name, its traits by
  the names of their methods, its `impl`s by trait and type, and its types by
  group of mutually recursive types. A method written inside a trait is
  declared as that trait's method, so finding the traits with a method
  `compare` reads no trait's interface.
- **Each lookup in an index is a result of its own.** A definition that looked
  up the members of `List` named `length` is re-checked only when that answer
  changes, although the index is rebuilt whenever the package declares
  something new.
- **A manifest is read one field at a time.** A result that reads a package's
  modules is not recomputed when the package's dependencies change.

The dependencies of each kind of result:

- **A resolved form** depends on its own tree, the file's `use` lines, and the
  name lookups that it made.
- **An interface** depends on the resolved signature and on the shapes and
  interfaces of the types and traits that it names.
- **A checked body** depends on its own resolved form and interface, and on the
  interfaces, shapes, and lookups that it used. It never depends on another
  body, except through two body facts of a callee: whether a method can be
  pulled, and the task hazard of a method that a `concurrent for` iterates
  over.

So the cost of each common edit follows from the dependencies:

| Edit | Re-checked |
|---|---|
| A function's body | That body. Its interface is unchanged, so nothing else. |
| A local's name | That body |
| A function's `ensures` | That function's clauses, and no caller's types. PROVER.md describes the effect on callers' proofs. |
| A function's parameter type | That function, and every definition that read its interface |
| A method added to `List` | The definitions that looked up a member of `List` with that name |
| An `impl` added | The definitions that looked up `impl`s of that trait for that type in that package |
| A definition added to a file | The definitions in that file that looked up that name, including bindings that were checked for shadowing |
| A field added to a type | The definitions that used its shape, and those that read a fact of it that changed |
| A definition moved to another module | The names in its users, which re-checks their types. Their test results stay valid, because a test's key contains no names, as CODEGEN.md describes. |

## Diagnostics

Diagnostics use the shared `Diagnostic` type from [LEXER.md](LEXER.md), with
codes such as `resolve.unknown_name`, `types.mismatch`, `types.missing_label`,
`patterns.not_covered`, and `ownership.use_after_move`. Every diagnostic is an
error, since Truss has no warnings, and the checker attaches an exact fix
whenever the intent is unambiguous:

| Error | Fix |
|---|---|
| A second argument without a label | Adds the label |
| Arguments out of order | Reorders them |
| A missing `mut` or `own` at a call | Adds it |
| A redundant mark | Removes it |
| A use after a move | `.copy()` at the move |
| An unused variable | Renames it `_` |
| An unused value | `let _ =` |
| An unused import | Deletes the `use` |
| Unreachable code | Deletes it |
| A `match` that misses cases | Adds an arm for each, with `todo` |
| A type that cannot be inferred | Adds an annotation, or type arguments to the call |
| Two traits' methods with one name | The call written in full, one fix for each trait |
| Mismatched integer types | `From` or `TryFrom` on one side |
| A recursive type without `indirect` | Adds `indirect` |
| An unknown name, member, or label | The closest visible one, when one is near |

- **One error per cause.** An expression whose type is wrong becomes `Error`,
  which holds its report, unifies with everything, and is never reported
  again, so one mistake is reported once. A definition the parser could not read is reported by the
  parser alone (see [Broken definitions](#broken-definitions)).
- **The interpretation of `f[X]` is stated.** An error in `f[X]` states which
  interpretation applied, such as "`parse` is a generic function, and `[Int64]`
  is its type argument", as DESIGN.md asks.
- **Habits from other languages** that need types are reported with fixes,
  such as `pair.0` and a tuple `(a, b)`, which say that Truss has no tuples
  and point to the record types in the standard library.
- **Holes are not errors.** A `todo` is reported to the tools with its type
  and the names in scope, as SYNTAX.md describes, and builds refuse programs
  that can reach one.

## Interfaces to other stages

- **The parser** produces one syntax tree per definition, with positions
  relative to the definition and an id on every node. Later stages record their
  decisions in tables keyed by those ids, and never change the tree. For a
  broken definition, the parser keeps what PARSER.md states, and the type
  checker relies on it as [Broken definitions](#broken-definitions) describes.
- **The prover** reads core forms, the interfaces and contracts of their
  callees, the functional bodies that it uses as definitions, and the type
  checker's obligations, as [PROVER.md](PROVER.md) describes. It discharges
  every `requires` and invariant, every operation that could fail, every cost,
  termination, and every obligation above.
- **Code generation** reads core forms, the shapes of types, and which methods
  can be pulled, as CODEGEN.md describes. Instantiation cycles have already
  been rejected.
- **The build** uses core forms to find the definitions that `main` can reach,
  and rejects a program that can reach a `todo` or an `echo`.
- **Tools** show the type of an expression and the definition of a name from
  the tables, and list every hole with its type, the names in scope, and the
  definitions that it blocks.

## The prelude

The type checker needs the prelude before it can check anything. Built-in
types such as `Int64`, `Bool`, `Unit`, `Never`, `Integer`, and `Array` are
declared by the compiler, in `standard::intrinsic`, as are two types the
standard library's collections are made of:

- **`Storage[Element]`** is owned storage on the heap: a buffer, a length,
  and a capacity, with the elements below the length live. The compiler
  generates its drop and copy, so `List` and `String`, which each hold one,
  need no destructor. It is `Copyable` when its elements are, never
  `Plain`, and holds its elements off the stack, so a type that contains
  itself through one needs no `indirect`.
- **`View[Element]`** is a read-only view of elements, a pointer and a
  length, which `Slice` and `StringSlice` hold. It is a view, and `Plain`,
  since copying it copies no element, so `Option[Slice[Int64]]` copies
  implicitly.

The intrinsic module also declares the operations the standard library is
written on, such as arithmetic on built-in numbers and growing a
`Storage`, as one type that the type checker and code generation each
match on exhaustively.

Everything else in the prelude is ordinary Truss in the `standard` package,
in [`standard/`](standard), checked like any other package and built into
the compiler. The prelude holds:

- the built-in types
- `Option`, with `Some` and `None` written bare, and `Result`, with `Ok` and
  `Err`
- `List`, `Slice`, `String`, `StringSlice`, `Map`, and `Set`
- `Equal`, `Ordered`, `Ordering`, `Hash`, `Hasher`, `Default`, `Display`,
  `TextBuilder`, `From`, `TryFrom`, `Copyable`, `Plain`, `Add`, `Subtract`,
  `Multiply`, `Divide`, `Remainder`, `Negate`, `Index`, `Model`, `Iterable`,
  `Cursor`, `Range`, `FromTemplate`, `Template`, and `ExitCode`
- `Sequence`, `FiniteSet`, `FiniteMap`, and `Multiset`
- the standard capabilities, `Console`, `FileRead`, `FileWrite`,
  `NetworkClient`, `NetworkServer`, `Handles`, `Clock`, `Random`,
  `Environment`, `Processes`, `Signals`, `Tasks`, `Log`, and `Panic`, and
  the types signatures everywhere are written with: `Instant`, `Duration`,
  `Path`, and `SystemError`

`Storage`, `View`, and the descriptor type `Handle` are not in the prelude.
The standard library names them through `standard::intrinsic`, so another
package may have a type called `View`.

The compiler names some of the standard library's definitions by path: an
operator is a call of `Add`'s method, a `for` loop pulls a `Cursor`, and
`main` returns an `ExitCode`. The module `Well_known` lists each such
definition once, with its path, and every stage names a definition through
that list. A test checks that each listed definition exists in the standard
library, so renaming one there fails the test.

When a call to a trait's yielding method resolves to a known `impl` that
defines the method, the checker records the callee as the `impl`'s method,
not the trait's. `List` gets `each(self)` from `impl Iterable`. The type of
the cursor and the contract of a loop over a list must then come from the
list's `each`, which only the `impl`'s method has.
