# Truss Type Checker

This document describes stage0's name resolution and type checking, in
[`stage0/`](stage0): everything between the parser's trees and the checked
form that the prover and code generation read. It follows the decisions in
[DESIGN.md](DESIGN.md), [SYNTAX.md](SYNTAX.md), and
[GRAMMAR.md](GRAMMAR.md), reads the trees described in
[PARSER.md](PARSER.md), and produces what [CODEGEN.md](CODEGEN.md) expects
and what the prover in [PROVER.md](PROVER.md) reads. Its queries run on the
code database, which [DATABASE.md](DATABASE.md) describes.

## What the type checker does

The type checker takes the syntax tree of each definition, the package's
manifest, and the manifests of its dependencies. For each definition it
produces a *resolved form*; an *interface*, which is what other definitions
may depend on; a *core form*, which is what the pattern check, ownership
checking, the package checks, the prover, and code generation read; and a
*checked form*, a set of tables that the usage check and the tools read. The
database records what each result read, and keeps each result under what it
read, as DATABASE.md describes.

The type checker:

- resolves every name to what it means, and decides the constructs the
  parser left open: `name[...]`, a bare name in a pattern, and a place after
  `mut` or `own`
- keeps what other definitions read of a definition apart from the rest of
  it, so that a change to a body re-checks no caller
- checks every signature, type definition, trait, `impl`, and capability on
  its own
- infers the types of every expression in a body, and chooses the method,
  field, variant, `impl`, and associated type each name means
- checks the rules on modes, moves, and views, within each function
- checks that every `match` covers every case and has no unreachable arm,
  and that every pattern in a `let`, `for`, or lambda cannot fail
- checks the rules on use: every value, variable, and import is used, and no
  code is unreachable
- checks capabilities: what each piece of code may call, what each `provide`
  provides, and what each dependency was granted
- checks the rules that span a package: where `impl`s live, that they do not
  overlap, that recursive types are marked `indirect`, and that generic code
  has no instantiation cycles

It does not:

- prove anything. Every fact that needs the solver, such as an index in
  bounds, an addition that cannot overflow, a `requires` at a call, a type
  invariant, a cost, termination, or two index ranges that do not overlap,
  goes to the prover. The core form marks the few obligations that the
  type checker creates itself (see
  [Obligations the type checker creates](#obligations-the-type-checker-creates)).
- run code. Constants are worked out exactly, from literals alone (see
  [Constants](#constants)). Tagged-template checks are `requires` clauses,
  which the prover discharges by running compiled code.
- decide layouts, drops, or anything else about the compiled program

## Structure

```text
syntax tree ──▶ Resolve ──▶ Interface ──▶ Body ──▶ core form, checked form
   (per definition)  │            │             │
                     └─────▶ diagnostics ◀──────┘
                                  ▲
        Package checks ───────────┘   (impls, cycles, instantiation)
```

### One definition at a time, through queries

The type checker never reads anything about another definition except
through a query of the code database, which keeps each result current and
finds what a change reaches, as [DATABASE.md](DATABASE.md) describes. What
the type checker adds is which results there are, and what each reads:

- **Each check is a query** with a key: the resolved form of a definition,
  its interface, its checked body, the shape of a type, the members of a type
  with a given name, and so on (see [Dependencies](#dependencies)).
- **Checking a body asks for the interfaces of what it calls,** which checks
  those signatures if they have not been checked yet, but never their
  bodies. A check of a package asks for the checked body of every definition
  in it.
- **Each query is of the compiler's phase it belongs to:** a file's trees,
  what files declare, what names mean, interfaces, bodies, the rules that
  span a package, and diagnostics. A query reads its own phase and earlier
  ones.
- **Cycles between queries are errors or are designed away.** Signatures
  depend only on other signatures and type shapes, never on bodies, so
  ordinary mutual recursion between functions never makes a query cycle. The
  few real cycles are the subject of a rule: constants that refer to each
  other, types that contain each other (checked for `indirect` by a package
  check, and with their facts worked out for the whole group in one
  result), and traits that require each other.

### Deterministic results

Every result is canonical, as DATABASE.md requires of a query:

- inference variables are numbered in the order they are created within one
  statement, and none survive into a stored result
- every list in a result is in source order, or sorted by a stable key such
  as a definition's path
- the checker never iterates over a hash table to build a result
- diagnostics are sorted by position, then by code

### Node identity

Every node the parser builds has an *id*: a small integer, unique within its
definition, given in the order the parser builds the definition's nodes.
Later stages never rebuild or copy a tree. Each records what it decided in
tables keyed by node id: resolution's table says what each name means, and
the checked form's tables give each expression's type, each call's argument
binding, each pattern's variants, and so on.

- **Spans cannot be the key.** They are not unique: a node the lexer or
  parser made in recovery is zero-width, and a node built for a habit, such
  as the `from` in the call that `x as Int64` is parsed as, shares its span
  with another node.
- **Tables are better than a tree parameterized by its annotations,** as in
  OCaml's separate typed tree or the "trees that grow" pattern. With such a
  tree, each stage builds and stores another copy, and every stage's tree
  has a different type. With tables, the tree is stored once and shared by
  every stage and tool, a stage that records a new fact adds a table, and a
  stored result is only what that stage decided. rustc names its nodes the
  same way, by the item that owns them and a number within it (`HirId`), so
  that a change to one item renumbers nothing in another.
- **What the program means is one more tree, built once.** The syntax tree
  is the program as written, which is what tools and diagnostics need. The
  stages that run or prove the program need what it means: which method a
  call calls, what a `?` does, where a value is. That is
  [the core form](#the-core-form), which the type checker builds as it
  decides, so that no later stage decides it again. Its nodes name the
  syntax nodes they came from, and hold no positions.
- **Ids are deterministic.** The same tokens give the same nodes with the
  same ids, so a definition that only moved keeps its ids, as it keeps its
  tree, and every table keyed by them stays valid.
- **An id means something only within its definition.** A result never
  names a node in another definition. It names the definition, by path, as
  every reference across definitions does.
- **A method is a definition wherever it is written.** One written inside a
  trait, an `impl`, or a capability has its own tree, its own ids, and its
  own results, exactly as one written `fn Type.name` has, so editing one
  method of an `impl` checks only that method again. Its path names what it
  is written inside, its own name, and how it takes `self`.
- **A generic parameter is named by what declares it and its name,** not by
  a node. Resolution records a use of `Element` as the parameter `Element` of
  `List.push`, or of the `impl` the method is in, which is the same pair a
  type names it by. So a parameter means the same thing in every tree that
  can see it, and nothing maps a node to it.
- **Tables are dense arrays** indexed by id, kept like every other result. A
  node a stage says nothing about has an empty entry.

## Name resolution

`Resolve` turns a definition's syntax tree into its resolved form: a table,
keyed by the tree's node ids, of what every name refers to. The tree itself is
unchanged (see [Node identity](#node-identity)). It reads the
definition's own tree, the file's `use` lines, and the names other files and
packages make visible, each through a query.

### What a name can refer to

Names live in separate namespaces, which the case rules keep apart:

| Namespace | Written | Holds |
|---|---|---|
| Modules | before `::` only | packages and modules |
| Types | `UpperCamelCase` | types, traits, capabilities, generic type parameters, and capability parameters |
| Values | `lower_snake_case` | locals, parameters, functions, constants, value generic parameters, theorems |
| Members | after `.` | fields, methods, variants, constants under a type, associated types |

- **An unqualified name** is looked up among the locals in scope, then the
  generic parameters, then the definitions in the same file, then the
  prelude. Exactly one can match, because no name may hide another.
- **A qualified name** `module::name` is looked up in that module. Its
  module is either imported by a `use` or written in full from its package.
  A full path starts with the name of a package the file may name, its own,
  `standard`, or one its manifest lists, and that name is two of the path's
  names when the package has an owner: `acme::geometry::vector` is the
  module `vector` of `acme::geometry` where the manifest lists that package,
  and otherwise names a module of a package `acme`.
- **A member,** after `.`, is not resolved here. Its meaning depends on the
  type before the dot, which only type checking knows. The one exception is
  a name before the dot that resolution already knows is a type, as in
  `Shape.Circle`, `UInt8.maximum`, or `List[String].with_capacity`: the
  resolved form records the type, and the type checker looks the member up
  in it.

**What a name refers to is one closed set of cases.** The resolved form
records each name as a local, a generic parameter that is a type, a
capability, or a `USize` value, a definition with the kind of definition it
is, a prelude variant, a module, a field, a specification word, or a name
that nothing answers, with its report. A later stage matches on those cases
in full. It never works a kind out again, from how a name is spelled or by
looking the definition up, so resolution and checking cannot disagree about
what a name is.

**An expression is read as a name in one way.** `parse`, `(parse)`,
`parse[Int64]`, and `(parse)[Int64]` all name `parse`, the last two with
type arguments. That reading is made in one place, which resolution,
checking a name as a value, checking it as a callee, and reading a type
written in an expression all use, so each takes parentheses and type
arguments alike.

Definitions are named in the resolved form by package, module path, and
name, never by a hash, as DESIGN.md requires. A method is named
by its type and its name, together with its receiver mode, since one name
can have a version for each mode.

### Scopes

- **Every `use` line imports one module.** Two imported modules with the same
  last name are an error at the second `use`. A module that no name in the
  file uses is an error, as in Go, with a fix that deletes the line.
  `standard::intrinsic` can be imported only by the `standard` package. That
  error is at the `use` line alone: names written through the import
  resolve as usual.
- **Locals follow blocks.** A `let` or `var` is in scope for the rest of its
  block. A name bound by `is` is in scope in the rest of its `&&` chain, in
  the block of the `if` or `while` whose condition contains it at the top
  level of its `&&` chain, and in the body of a `match` arm whose guard
  contains it that way. It is not in scope after `||`, under `!`, or in an
  `else`. A name bound by `let ... else` is in scope for the rest of the
  enclosing block. A `let` in a `parallel` branch is in scope after the
  `parallel` block, not in the other branches.
- **No name hides another.** Binding a name that is already visible in the
  values namespace, whether a local of an enclosing scope, a parameter, or a
  definition in the same file, is an error that names both. The prelude
  holds only `UpperCamelCase` names and values are `lower_snake_case`, so
  only types can clash with the prelude. Generic parameters are checked the
  same way against the file's types and the prelude.
- **Specification words** get their meaning by where they are. `result`
  names the return value inside `ensures` and `cost`; `old(...)` is the
  value on entry inside specifications and proofs; `log`, `power`,
  `time(...)`, and `calls(...)` are the cost functions inside a `cost` bound;
  `identical(a, b)` is identity, for two values of one type, inside
  specifications;
  `yielded` and `finished` are what a lending or yielding method has handed
  out and whether it ran to its end, inside its `ensures`, and `yielded` is
  what a `for` loop's earlier iterations received, inside its `invariant`.
  Anywhere else, they are ordinary names. Where one has its meaning, a
  visible variable with the same name would be hidden, which is an error as
  everywhere else.

### Decisions the parser left open

| Construct | Resolved as |
|---|---|
| `name[...]` | Type arguments if `name` is a generic function, a type, or a trait; an index if it is a local, a parameter, or a constant. For a method, as in `items.map[String]`, type checking decides from the receiver's type. |
| A bare `LOWER_NAME` in a pattern | The constant, if one with that name is visible. Otherwise a new binding. |
| A place after `mut` or `own` | The expression must start with a local, a parameter, `self`, or a constant, followed by fields and indexes. `mut parse[Int64](text)` starts with a function, so it is an error with a fix that removes `mut`. |
| A `LOWER_NAME` in a type argument | A value generic parameter or a constant of type `USize`, as in `Array[UInt8, digest_size]` |

Matching a bare argument to a parameter needs the callee's signature, and
for a method the receiver's type, so it is done by type checking (see
[Calls and arguments](#calls-and-arguments)).

### Errors and habits

Resolution reports names that refer to nothing, with a fix to the closest
visible name when one is near. It also reports the habits from other
languages that are names, with exact fixes: `null` and `nil` become `None`,
and `Shape::Circle` becomes `Shape.Circle`.

### Broken definitions

A definition the parser could not read as written is still registered and
checked as far as it can be, so that its error is reported once, by the
parser, and nothing that uses it reports another. PARSER.md states what the
parser keeps:

- **A definition whose header did not parse** keeps only its keyword and
  name, when those could be read.
- **Any other broken definition** keeps its whole tree, with an `Error` node
  for each part that failed, and its signature as written when every
  diagnostic lies in its body.
- **The members of a trait, an `impl`, or a capability recover one by one.**
  A broken associated type or law is an `Error` member, and the members
  around it are as written. A method is a definition of its own, so what
  breaks in it is its own.
- **Nodes built for a habit** lie in the same signature or body as the
  habit's diagnostic.

**A part is broken only when its tree differs from its source.** The unit is
one signature, one body, or one type's definition, whether of a definition or
of a member that a trait or an `impl` holds itself, an associated type or a
law. The parser lists, on each definition, the spans where it built a
tree that is not the source as written: where it built an `Error` node or a
node for a habit, or consumed a closer the lexer inserted. A part is broken
when one of its definition's recovered spans lies in the part's span: a
signature runs from the definition's or member's start to its body's start,
a body is its block, a member is its line, and a type is its definition.
A recovered span with width lies in every part it overlaps. A zero-width
one at position `p` lies in the part that starts at `p`, if there is one, even
when that part is itself zero-width, and otherwise in the part with
`start <= p < stop`. So a missing body, recorded as a zero-width span at the
end of the signature, where its kept `Error` body also starts, breaks the
body and not the signature, and the function keeps its interface. A parser
diagnostic that only enforces a rule on code it read exactly as written,
such as a misplaced `assert`, `yield`, `break`, or `echo`, `forall` outside a
specification, a parameter named `result`, `lends own`, a repeated clause,
or a misplaced `public` or `opaque`, does not make its part broken. Such a
part is checked as usual, since checking it cannot report on invented code,
and an agent then sees its type errors in the same build as the parser's.
The parser decides which of its diagnostics are recoveries, in one
exhaustive match over its codes, so a new kind of diagnostic cannot compile
until it is put on one side, and the type checker never classifies codes.

The type checker uses that as follows:

- **Every broken definition that has a name is registered,** as a
  definition of its kind, so uses of it resolve. One whose name could not be
  read registers nothing, and a use of what it meant to define is an
  unknown name.
- **A broken part is never checked.** A definition whose header or
  signature is broken gets the `Error` interface, and a type whose fields or
  variants are broken gets the `Error` shape. A broken body is not checked.
  A broken member of a trait, an `impl`, or a capability affects only that
  member: a trait with one broken method keeps every other method's
  interface, so uses of those are checked as usual, and only uses of the
  broken method get `Error`. Nothing written inside a trait, an `impl`, or
  a capability whose own header is broken is checked, since what it is
  inside is not known. Since nodes built for a habit lie in a broken part,
  no invented code is ever checked.
- **Everything is accepted of an `Error` interface or shape, silently.** A
  call to such a function takes any arguments and has type `Error`. Building
  such a type, reading its fields, matching on it, and looking up its
  members all give `Error`. A trait with the `Error` interface satisfies
  every bound that names it, and a constant with it has type `Error`. The
  interface or shape holds the parser's report, which every `Error` made of
  it hands on (see [Errors carry their report](#errors-carry-their-report)).
- **A part that is not broken is checked as usual.** A function whose body
  is broken keeps its interface, so callers are checked against its
  signature as written, as for any function.
- **A broken definition is a dependency like any other.** Results that used
  its `Error` interface read it like any other interface, so when the definition is
  fixed, exactly they are checked again.
- **Builds and tests skip what cannot run.** A build refuses a program that
  can reach a definition with any error, broken or not. A test that can
  reach one does not run, and is reported as blocked by it; every other test
  runs as usual. An obligation the prover has not proven, or could not prove,
  is not an error of this kind for tests: a test build checks every
  operation that could fail as it runs, as CODEGEN.md describes, so tests run
  without waiting for proofs. A build of a program still needs every proof.

## Parts of a definition

A definition is not one result. What type checking another definition reads
of it is apart from the rest, so that a change to the rest comes out the
same there and goes no further:

| Definition | What checking others reads | What only its own check reads |
|---|---|---|
| Function or method | Its *signature*: generic parameters and bounds, the receiver, parameter names, types, and modes, which parameters have defaults, the result or `yields` or `lends` form, `uses`, and whether it has a `time` clause | Its body, each default, and its `requires`, `ensures`, `decreases`, and `cost` clauses |
| Type | Its *shape*: generic parameters, fields and variants with their types, which fields have defaults, `indirect` marks, `opaque`, and `derives` | Its invariants, its potential, and its fields' defaults |
| Trait | Its *interface*: parameters, required traits, associated types, and each method's signature | Its laws |
| `impl` | Its *interface*: generic parameters, the trait, the type, `uses`, and each method's signature | Nothing |
| A method written inside a trait, an `impl`, or a capability | Its signature, as a function's, read with what the one it is inside says of `Self`, its associated types, and its generic parameters | Its body, if it has one, and its clauses |
| Constant | Its type, and its value where the checker needs one | Its expression |
| Test, theorem | Nothing | Its body |
| Law proof | What it is of: the trait, the law, and the type | Its body |

- **Type checking a caller reads only the callee's signature.** Changing a
  body, a default, or an `ensures` type-checks that definition again and no
  caller. What the prover reads of a callee is PROVER.md's.
- **A default is apart from the signature,** as DESIGN.md requires: callers
  read only whether a parameter has one.
- **A type's invariants are apart from its shape.** Strengthening an
  invariant re-checks the type, and nothing that uses it.

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
  uses : capability_set;                    (* capabilities and capability parameters, sorted *)
  costs : cost list;
}
```

- **Built-in types are `Named`** after definitions the compiler provides in
  the prelude, such as `Int64`, `Bool`, `Unit`, and `Array`. Only `Never` and
  `Integer` have constructors of their own, because each has rules no
  definition could state: `Never` converts to every type, and `Integer`
  exists only in specifications.
- **Types are nominal.** Two `Named` types are equal when they name the same
  definition with equal arguments. Function types are compared by
  structure, what each cost clause counts included: a `calls` clause of a
  function type counts the calls of a capability or of one of its methods,
  which is part of the type, so `(fn() cost calls(FileRead) <= 1)` is not a
  `(fn() cost calls(Clock) <= 1)`. A type cannot name a parameter, whose
  calls a function's own clauses count. Value arguments are compared by
  value, after constants are worked out, so `Array[UInt8, digest_size]`
  equals `Array[UInt8, 32]` when `digest_size` is 32.
- **Associated types are normalized** whenever their base is known. With no
  blanket `impl`s, `Projection { base = Named ...; ... }` has at most one
  `impl` to look in. A projection on a generic parameter stays a projection,
  equal only to itself or to what a bound fixes, as in
  `Iterable[Element = Int64]`.
- **`Variable` and `Literal` exist only while checking.** A stored checked
  form contains neither. A `Hole` stays where a `todo`'s type was never
  decided: a `todo` is not an error, so a `Hole` is never turned into one.

### Errors carry their report

`Error` unifies with everything, so that one mistake is reported once. That
is safe only when the mistake was reported, so an `Error` cannot be made
without a report: it holds a value that only a report gives, as rustc's
`ErrorGuaranteed` does.

- **A report is one of two things:** a diagnostic a stage made, or a place
  where the parser recorded that it recovered, which it does only where it
  or the lexer reported an error.
- **Everything that stands for something wrong holds one:** the `Error`
  type, the `Error` interface and shape of a broken definition, a broken
  member of a trait, and a name that resolution found nothing by.
- **A report is handed on, never made up.** A call of a broken function has
  the `Error` of that function's report, and a use of an unknown name has
  the `Error` of the name's. Where a use meets an error that another
  definition's check reported, as with an `impl` that leaves out an
  associated type, it reads that definition's diagnostics and takes the
  first as the report.
- **Code with no report to hand on reports, or keeps what it cannot work
  out.** A function that cannot report returns no `Error`. An associated
  type that no `impl` answers stays a projection, which equals only itself,
  so code that depends on it is rejected, not accepted.
- **A pattern that does not fit its type still binds its names,** each with
  the `Error` of the pattern's report, so no use of a local is without a
  type.
- **What cannot happen stops the compiler.** Where resolution, the
  interfaces, and checking must agree, as that every local has a type and
  every expression of a checked body has one, a disagreement is a bug in
  the compiler and raises. Going on would accept code that nothing checked.

### No subtyping

Types are invariant, and there is no subtyping relation. Two types are
equal or they are not, and function types with other `uses` or other costs
are other types. Exactly four conversions happen, all decided in the one
place where a value meets the type expected of it. One made for an argument
is recorded with the argument in the checked form:

| Conversion | Where |
|---|---|
| `Never` to any type | Wherever an expression of type `Never` meets an expected type, such as `None => return Err(error)` in a `match` whose value is an `Int64` |
| `List[Element]` to `Slice[Element]`, `String` to `StringSlice` | An argument passed to a parameter of the view type, and the key of an index, which is the argument of `at`. This is DESIGN.md's only implicit conversion. |
| A function value to a function type with more `uses` or weaker costs | Where a value is passed, bound, returned, assigned, or stored, and where a branch of an `if` or a `match` ends with it. A pure function can be passed as `(fn(Item) uses Clock)`, and a `cost time O(1)` function as `cost time finite`. |
| A built-in integer to `Integer`, and back | An argument or an index's key, in specifications only (see [Specifications](#specifications)) |

The function-value conversion happens only at the top of an expression, not
inside a type argument, so `List[fn(Item)]` and
`List[(fn(Item) uses Clock)]` stay different types, as in Rust.

- **Every capability the function uses must be one the expected type
  lists.** A function that `uses Clock` is never a `fn()`, in an argument,
  a `let`, a `return`, a field, or an assignment. Where the expected type
  lists a capability parameter of what is being called or built, the
  parameter comes to stand for what the function uses, as
  [What code may call](#what-code-may-call) describes.
- **Costs are weaker when the types' constants show it:** an exact count is
  within any bound it does not exceed, a count is `O(...)`, and every bound
  is `finite`. A named function's type has `time finite` exactly when the
  function has a `time` clause. Costs that the constants do not show to be
  weaker are the prover's to show. For a function passed to a call the
  prover reads the argument, as PROVER.md's "Lambdas and function values"
  describes. Anywhere else the checker records the obligation, with the
  expression and both function types.

### Properties of types

Four facts about a type decide what code may do with it. Each is worked out
from the type's shape, as a condition on its type parameters: `Option[Value]`
is `Plain` exactly when `Value` is.

| Property | Holds for | Lets code |
|---|---|---|
| `Copyable` | every type except the standard library's handles and types that hold one | call `copy()` |
| `Plain` | integers, floats, `Bool`, `Character`, `Unit`, arrays, records, and sum types made only of `Plain` parts, with no heap data and no handle | copy implicitly. `Plain` requires `Copyable`. |
| View | `Slice`, `StringSlice`, a cursor from a `self` method, every function type, an `any` that holds a view, and anything holding a view anywhere, in a field, a variant, an element, or a type argument | nothing extra; values of view types stay within their function (see [Views](#views)) |
| Structural equality | the built-in integers, `Bool`, `Character`, `Unit`, `String`, the types of specifications, and a type that derives `Equal` whose fields all have it; never floats, a hand-written `Equal`, or, outside its package, an opaque type | be a constant in a pattern; the prover substitutes through `==` |

- **`Copyable` and `Plain` are prelude traits that the compiler implements.**
  No `impl` of them can be written. A generic parameter has them only when
  bounded, as in `[Element: Copyable]`, so a plain `[Element]` accepts
  everything, including handles.
- **An opaque type has them only when declared** with `derives Copyable` or
  `derives Plain`. The checker verifies that the fields allow it. Other
  packages rely on the declaration, so adding a field that cannot be copied
  is an error at the type and never a surprise elsewhere. Every other type
  has them by inference, and declaring them on a type that is not opaque is
  an error with a fix that removes the declaration, since its fields already
  say it.
- **A generic opaque type has them under the conditions its fields give,**
  as any other generic type does. `Slice[Element]` holds a view of its
  elements, so it is `Plain` whatever `Element` is. `List[Element]` holds
  its elements, so it is `Copyable` when `Element` is. A type parameter that
  no field holds, as in `opaque type Id[Entity](value: UInt64)`, is no
  condition. Swift checks a declared `BitwiseCopyable` against the fields
  the same way. Rust's `derive` instead requires the property of every type
  parameter, which is why a `Copy` type with an unused parameter needs a
  hand-written `impl` there. The cost is that changing a generic opaque
  type's fields can change which of its type arguments must have the
  property.
- **`copy()` is always the compiler's.** It is the method of `Copyable`, and
  no type can give copying a cost or an effect of its own, as no type can
  define a destructor.
- **`any Trait` is `Copyable` only when `Trait` requires `Copyable`,** since
  the concrete type behind it is unknown.
- **Whether a type is a view is part of its shape.** Making a type hold a
  view changes how every user of it is checked, which reaches every reader
  of the shape like any other change of shape.

The first three, and what a type holds in place (see
[Recursive types](#recursive-types)), are *facts of the type's definition*,
worked out once for each definition and kept as a result of their own:

- **A fact is a list of conditions.** For `Copyable` and `Plain` it is what
  must have the property for the type to have it, or that it never does. For
  a view it is what makes the type one when any of it is, or that it always
  is. `Option` is `Plain` on the condition `Value`, and a view on the
  condition `Value`.
- **A question about a type asks its definition's conditions of its
  arguments.** Whether `Option[Option[List[Int64]]]` is `Plain` is `Option`'s
  condition asked of `Option[List[Int64]]`, then of `List[Int64]`, which never
  is. No question walks a type's fields, so none can take a type nested in
  itself for a type that contains itself.
- **Types that contain each other are worked out together.** Such a type is
  `Copyable` and `Plain` when nothing in it says otherwise, and is a view, or
  holds something in place, only when something in it does. So a group
  starts with the facts of types that have no fields, and each member's
  facts are worked out from the others' until nothing changes.
- **An associated type is a condition too.** In
  `type Kept[Source: Shown](part: Source.Part)` nothing is known of
  `Source.Part`, so `Kept` is a view on the condition `Source.Part`. Where
  `Kept[Numbers]` is asked about, the condition is `Numbers`'s `Part`, which
  the `impl` of `Shown` for `Numbers` chooses. Inside generic code, an
  associated type of a parameter has a property only when its trait bounds
  it, as a parameter does. One that no `impl` answers is taken not to be
  `Copyable` or `Plain`, and to be a view.

## Checking signatures and definitions

`Interface` checks each definition's outward-facing part on its own, from its
resolved form and the shapes and interfaces of what it names. Its result is
the definition's interface: the types of its parameters and result, its
`uses`, its bounds, and the facts derived from them.

### Functions and methods

- **`Self`** is the type a method's head names, the type being defined, a
  trait's implementing type, or an `impl`'s type. Anywhere else, as in a
  function that is not a method or in a capability, it is an error.
  `Self.Name` is an associated type, so it is written only in a trait or in
  an `impl` of one. Only lowering a written type knows what `Self` stands
  for, so it alone reports this.
- **Every type is well-formed:** it has the right number of arguments, value
  arguments are `USize` constants or value parameters, and every bound the
  type requires holds. `SortedList[Element]` in a signature needs
  `Element: Ordered` from the signature's own bounds, as in Rust.
- **`self`** may only be the first parameter of a method, and a type can have
  at most one method of each name for each receiver mode. Where there is no
  method, a `self` parameter gives the function no receiver, and `self` in
  the body is an error. A method's type
  must be defined in the same package, and a method of a type private to its
  file must be in that file.
- **Defaults** are constant expressions of the parameter's type that name no
  parameter. A parameter named `result`, or a function named `old`, is an
  error.
- **An `own` function-typed parameter** accepts only functions that capture
  nothing. That is recorded in the interface, for checking callers.
- **A function-typed parameter's `requires`** is a specification, a `Bool`
  over the type's named inputs, with the types its inputs have, and the
  parameters before it. It is not part of the parameter's type: two function
  types that differ only in it are the same type, and the prover reads it
  from the signature, both to show the function meets it at each call
  through the parameter and to give a lambda passed there its facts.
- **A private type in a public signature is an error,** and so is a private
  or `internal` type in a public type's visible fields, as in Rust and
  Swift. Callers in other packages could never name the type.
- **Clauses are checked in the order written,** each with the clauses
  before it in scope, as SYNTAX.md describes. `requires`, `ensures`, and
  `decreases` are specifications (see [Specifications](#specifications)).
  `uses` names capabilities or capability parameters. Each `cost` clause's
  bound is an `Integer` expression; `calls(target)` names a parameter that
  is a function, a capability, or a method the capability has, and anything
  else is an error. `time(visit)` names a function-typed parameter.
  `time(Element.equal)` names a method of a trait that bounds a type
  parameter of the definition, or that bounds `Self` in a trait. It is a
  bound on the time of any one call of that method. If the bounds have
  several versions of the method, the term names the read-only version.
- **`lends` and `yields`** state how the method gives out parts of `self`:
  `lends` exactly once, `yields` any number of times. A lent part stays with
  `self`, so `lends` takes no mode or `mut`, and `lends own` is an error.
  The body is checked against the form (see
  [Yielding and lending](#yielding-and-lending)).
- **`main`,** in a package's `main` module, must have exactly the signature
  `fn main(arguments: List[String]) -> ExitCode`, with any `uses`. A
  function named `main` in another module is an ordinary function.

### Types

- **Fields and variants** are checked like parameters: well-formed types,
  constant defaults, no two fields or variants with one name.
- **Invariants and the potential** are specifications, in which `self` names
  the value and a record's fields are in scope by name. An invariant is a
  `Bool`; a potential is an `Integer`.
- **`derives`** is checked against the shape. Every field must already
  implement the trait, under the same conditions on the type parameters as
  the derived `impl`'s, so `Option[Value]` derives `Equal` as
  `impl Equal for Option[Value: Equal]`. Deriving `Ordered` or `Hash` needs
  `Equal` to be derived too. Only a record derives `Default`, which is each
  field's: no variant of a sum type is its default, so that `impl` is
  written, as Rust asks for a variant to be marked. Each derived `impl`
  becomes a definition of its own, as DESIGN.md says, named by the type and
  the trait.
- **`= todo`** makes a type that can be named and passed but whose contents
  cannot be used. It has none of the properties above, so it cannot be
  copied and is not a view, until it is defined.

### Traits, `impl`s, and capabilities

A trait, an `impl`, or a capability and the methods written inside it are
checked apart, and neither waits on the other:

- **Its header is its own.** Lowering it gives its generic parameters and
  their bounds, what `Self` is, the associated types, and for an `impl` its
  trait, its type, and its `uses`. This reads only its own tree.
- **Each method is lowered with that header,** which is what `Self`, its
  associated types, and the generic parameters around the method mean, and
  gives a signature as any function's. An `impl`'s method is generic over
  the `impl`'s parameters and then its own, and uses what the `impl` uses,
  as a method written `fn List[Element].push` is generic over its head's
  parameters first. A trait's method is generic over its own alone: `Self`
  and the trait's parameters are given where it is called.
- **A method an `impl` leaves to its trait has a signature too,** though it
  is written nowhere of its own, and so has one of a derived `impl`: the
  trait's method's, with `Self` and the trait's parameters replaced by what
  the `impl` gives them, generic over the `impl`'s parameters and then its
  own. Code generation and the prover compile and prove a method at an
  `impl`, so they ask for this one.
- **Its interface is put together** from the header and the signature of
  each method written inside it. A trait's method is provided when it has a
  body, and one whose own signature is broken is listed as broken.
- **Each method is checked against what it is inside as a definition of its
  own:** an `impl`'s against the method its trait declares, and a trait's
  against the traits it requires. The `impl` itself is checked for what it
  must give and does not.

- **A trait's members** are checked like functions, with `Self` standing for
  the implementing type and `Self.Name` for its associated types. A trait
  may not redeclare a method of a trait it requires, though it may add a
  version that takes `self` another way, and traits may not require each
  other in a cycle.
- **An `impl` conforms to its trait.** Every method without a body and every
  associated type is given, and nothing else is. Each method has the trait's
  parameter names, modes, and types, with `Self` and the associated types
  substituted; the same result form; generic parameters with no stronger
  bounds; and `uses` that are a subset of the trait method's. Parameter
  names must match because they are part of how a method is called, as
  Swift requires of protocol requirements. Defaults are written only in the
  trait. A method may add `ensures` and `cost` clauses, and may state a
  `requires`; the prover shows that its clauses are no weaker than the
  trait's, as DESIGN.md describes. The `impl`'s clauses are part of its
  contract, which a call resolved to the `impl` depends on.
- **The traits a trait requires** must be implemented for the same type,
  under conditions no stronger than the `impl`'s.
- **A capability `impl`'s methods** take the capability's parameters plus a
  receiver, `self` or `mut self`. Only a capability `impl` may have a
  `uses` clause, and its methods use what it declares and no more: whoever
  calls a capability holds the capability alone, so a method there has no
  `uses` of its own to add. A trait `impl`'s methods can use only what the
  trait's methods declare. Implementing `Panic` is an error.
- **A law's proof** names a law its trait has and a type that implements
  the trait.
- **Methods that replace a provided method** must have its exact signature,
  and the provided method must be pure, have a `time` clause, and change
  none of its arguments, which is what lets its body be its definition.
  That the body is functional, and that the replacement gives the same
  result, is the prover's job.

### Recursive types

A type that contains itself in place would be infinitely large. The checker
finds every cycle of types that contain each other in place, through fields,
variants, type arguments held in place, and associated types, and reports
any cycle that does not pass through an `indirect` variant, with a fix that
adds `indirect` to the variant where the cycle re-enters.

Whether a type argument is held in place is a fact of the generic type's
definition (see [Properties of types](#properties-of-types)): `Option` holds
its `Value` in place, while `List` holds its elements through a `Buffer`,
which the intrinsic module declares as heap storage. A type that holds an
associated type of a parameter in place, as
`type Kept[Source: Shown](part: Source.Part)` does, holds whatever the
`impl` chooses for each argument, so `type Tree(kept: Kept[Marker])` contains
itself when `Marker`'s `Part` is `Tree`. This is a package check, over the
type definitions of one package: packages do not depend on each other in a
cycle, so neither can their types.

A generic type that contains itself with different arguments, as in
`type Nested[Element] = Leaf(value: Element) | indirect Node(inner: Nested[List[Element]])`,
is an error found by the same walk, as DESIGN.md requires.

## Checking bodies

### Bidirectional, one statement at a time

Bodies are checked bidirectionally: an expression is either *checked*
against an expected type, which flows inward from annotations, parameters,
and operators, or has its type *inferred*. Unknown types inside one
statement are inference variables, solved by unification.

**Each statement settles its own types.** When a statement ends, every
inference variable in it must be solved. Literals that nothing decided take
their defaults, and anything else unsolved is an error that asks for an
annotation, with a fix that adds one to the `let`. A local's type is then
fixed for the rest of the body. This is local type inference, as in Swift,
Kotlin, Scala, and C#, rather than inference across a whole body, as in
Rust, OCaml, and Haskell:

- **A variable's type comes from its own line,** which is what a reader, an
  LLM, and a hover in the language server all see. An error is reported at
  the statement that caused it, never at a distant use that finally fixed a
  variable.
- **Checking is local and fast.** Unification never spans more than one
  statement, so its cost follows the size of the statement.
- **The cost is a few annotations.** `var names = []` needs
  `var names: List[String] = []`, and `var best = None` needs a type, as in
  Swift and Kotlin. SYNTAX.md already writes them this way, and
  `var best = 0` is an `Int64`, as SYNTAX.md says.

A statement here is the innermost one. The statements inside a block that is
part of a larger expression settle their own types, and the block's last
expression is checked against the block's expected type.

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
  a literal of an unsigned type is an error. A `USize` or `ISize` literal
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
value, or one ASCII character, with no `${...}`, and the checked form records
the value it stands for, as for an integer literal. In a pattern it matches
that value, and a range of them, `Character"a"..=Character"z"`, matches the
values between. A range pattern's type must be an integer type or
`Character`.

### Operators

Each operator becomes a call, so the checked form needs no operator rules of
its own. The call recorded is the one made, and gives what its method gives,
which for a comparison is not the operator's own `Bool`:

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
  place, then `place + value` as above, and records that the old value is
  handed to the operator as owned. When the trait has a version of its
  method that takes `own self`, that version is chosen.
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

Then the arguments must appear in the order of their parameters, which is an
error with a fix that reorders them when they do not. A parameter with a
default may be left out, and the checked form records which were left out,
for the default-presence mask that CODEGEN.md describes. Records and
variants differ in two ways, as SYNTAX.md says: arguments may come in any
order, and only a record or variant with exactly one field takes a bare
value.

**Lambdas are checked last.** The arguments of a call that are not lambdas
are checked first, in order, and unified with the parameters. Then each
lambda is checked against its parameter's type, which by then gives its
parameters their types and modes. Its result type may still be open, as
`Output` is in `items.map(fn(item) { item.name.copy() })`, and the body
decides it. A lambda whose parameter types are still unknown is an error
that asks for type arguments or an annotation. A parameter's type is never
worked out from how the body uses it.

**Generic arguments** are inference variables, solved from the arguments
and from the expected type, so `let digest: Array[UInt8, 32] = Array.filled(0)`
takes its length from the annotation. Explicit type arguments, as in
`parse[Int64](text)`, are unified first.

**Bounds are held wherever generic parameters are filled in,** whether the
arguments are written or worked out: at a call, where a function or a
method is used as a value, where a `for` loop calls `each`, and where a
generic type is named or a value of one is built, so `Holder(5)` is an
error when `Holder[Value: Shape]` and `Int64` is no `Shape`. Each bound is
checked once the statement has worked out the type it is on:

- **The type must implement the trait.**
- **Each associated type the bound fixes must equal the one the `impl`
  gives.** The two are unified, so the bound can be what works a type out:
  with `fn first_of[Input: Source[Item = Output], Output](input: Input) -> Output`,
  the call `first_of(numbers)` takes `Output` from `Numbers`'s `Item`.
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
- **A receiver's mode chooses the method's version.** No mark chooses the
  read-only version, and `mut` and `own` choose theirs. On a temporary, the
  `own` version is chosen if there is one, and the read-only one otherwise.
  A missing version is an error that names the versions there are.
- **A part that is lent is neither a place nor a temporary.** What a call
  of a lending method gives, and each field and element of it, is lent
  read-only or `mut`, as the method's signature says. It takes no mark: the
  mark that chose the method's `mut` version is the one before the place it
  is lent from. A part lent `mut` goes to a `mut` parameter, has its
  `mut self` methods chosen, and can be assigned to; one lent read-only
  cannot. Neither is ever given up to an `own` parameter or an `own self`
  method, unless it is `Plain` and so copied.

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

A name's versions are found together: the type's own methods with that
name, and those of the traits that give the type the name, each by how it
takes `self`. One function answers this for a call with a dot, a call
written in full, a `for` loop's `each`, and a quantifier's, and the
receiver's mode then chooses among them once. The traits must be one family,
each reached from another through what it requires. Two unrelated traits
with one name are an error at the call, however each takes `self`, with
fixes that write it in full, one for each trait. A type's own method and a
trait's that are the same one are reported by a package check, at the
`impl`. A name found nowhere is an error with a fix to the closest member.

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
`if false { ... }` is not reported.

### `todo`, `echo`, and `unreachable`

- **`todo` takes the expected type,** and the hole is reported with that
  type and the names in scope, as SYNTAX.md describes. With no expected
  type, as in `let body = todo`, it has the `Hole` type. Every operation on a
  `Hole` is accepted, and its result is a `Hole`, so the rest of the body is
  still checked as far as it can be. Its report says that the type is not
  decided and lists how the value is used. `todo` does not make the code
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

**What a pattern binds follows the matched value's mode.** Matching a
read-only place binds views of its parts, matching a `mut` place, as in a
`mut` loop, binds `mut` access to its parts for the arm or iteration, and
matching an owned value binds its parts as owned. A `Plain` part is always
copied.

### Exhaustiveness and reachability

`Patterns` uses Maranget's usefulness algorithm ("Warnings for pattern
matching", 2007), the one OCaml and Rust use, over the matched values as a
vector, so a `match` over several values is checked as one. It reads the
[core form](#the-core-form), so it checks the patterns that the prover and
code generation read, the ones that `?` expands to among them:

- **Constructors** are the variants of a sum type, `true` and `false`, the
  intervals of an integer or `Character` type, which ranges and literals
  split, and constants, which are expanded into the patterns of their
  values. Strings have infinitely many values, so a `match` on a string
  needs a pattern that matches everything. A value that is not worked out,
  such as a constant built by a call or a generic parameter that is a
  value, covers nothing but itself.
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

`Ownership` checks DESIGN.md's rules on modes, moves, and views within each
function. It reads the definition's [core form](#the-core-form) and the
interfaces of what the definition calls.

The check builds a control-flow graph of the body. Each point of the graph
does one thing to one place: it reads it, moves it, borrows it `mut`,
assigns it, or binds new locals. The edges follow the order of evaluation,
and a loop has a back edge. The body of a lambda is a separate entry into
the graph, because it runs when the lambda is called. Three analyses run on
the graph:

- forward, the places that may have been moved before each point;
- forward, the places that each holder of a view may view at each point;
- backward, the locals that are still used after each point.

A function for specifications only is not checked. It never runs, so it
moves and borrows nothing.

### Places

A place is a local, a parameter, `self`, or a constant, followed by fields
and by indexes of a `List`, a `Slice`, or an `Array`. A constant that a type
declares, such as `UInt8.maximum`, is a place like any other constant. An index whose value
the checker cannot compare, such as `items[i]`, stands for *some element* of
`items`. An index of any other collection is not a place: it is a call of
the collection's `at`, a lending call (see
[Yielding and lending](#yielding-and-lending)).

Two places *overlap* when one is a prefix of the other. `config.servers` and
`config.clients` do not overlap. `items[i]` and `items[j]` may, and so may
two slices of one collection: where that matters, the checker does not
report an error but records an obligation that the indexes or ranges are
disjoint, which the prover discharges, as DESIGN.md requires for
`sort(mut items[..middle])` beside `sort(mut items[middle..])`.

### Moves

A place is moved by `own place`, by a `for` loop over `own place`, by
matching an owned value, by `own base with (...)`, and by returning it. A
`Plain` value is copied instead.

- **A moved place cannot be used** until it is assigned again, on any path
  that may reach the use. The error points at the move, with a fix that
  writes `.copy()` at the move when the type is `Copyable`.
- **A field can be moved out on its own.** The rest of the record stays
  usable, and the whole becomes usable again once the field is assigned, as
  DESIGN.md describes. The checker tracks moved fields path by path.
- **Only owned places can be moved.** Moving out of a read-only parameter, a
  view, a constant, or an element, as in `own items[i]`, is an error, as in
  Rust. The fixes offer `copy()`, and a method such as `remove` for an
  element.
- **A place lent `mut` can be moved out of if it is put back.** A `mut`
  parameter, `mut self`, the variable of a `mut` loop, a `mut` binding of a
  `match`, and a lambda's `mut` parameter belong to someone else, who gets
  them back. Such a place, or a field of it, may be given up with `own` if
  it is assigned again on every path before it goes back: before the
  function returns, before the loop's iteration, the `match` arm, or the
  lambda ends, and, in a yielding method, before each `yield`, because a
  loop may stop the method there. A lending method always continues after
  its `yield`, so it may yield in between. Until the place is assigned,
  using it is an error, as for any moved place. So `Option.take` is
  `let taken = own self`, then `self = None`, then `taken`. This is sound
  because a panic ends the program: nothing can see the place while it is
  empty. Rust unwinds, so it forbids the move and offers `mem::replace`
  instead.
- **A name that a value is moved into owns it.** After `let taken = own
  items`, `taken` views nothing, and `items` can be assigned again while
  `taken` is in use.
- **A returned place that is not owned is an error,** with a fix that
  copies it. This holds for the function's last expression, and for the
  value of a block, an `if`, or a `match` arm that is the last expression.
- **Inside a lambda, a captured local is a view,** so it cannot be moved
  there.
- **The result records every move,** by the id of the core node that takes
  the value.

### Loans

A *loan* is a period during which a place is lent. Each is shared or `mut`:

| Loan | Kind | Lasts while |
|---|---|---|
| A read-only argument | shared | the call |
| A `mut` argument or receiver | `mut` | the call |
| A `let` of a place | shared | the binding is live |
| A value of a view type, such as a slice, a cursor, or a lambda that captures | shared | the value is live |
| What a lending call is called on | shared, or `mut` when the method takes `mut self` | the rest of the statement |
| A `for` loop's variable | shared or `mut` | the iteration |
| A `provide` of a place | shared or `mut` | the `provide` block |
| An operand that has been evaluated | shared | until its operation runs |

A loan is live while any value that holds it may still be used, which a
liveness analysis decides, as in Rust's non-lexical lifetimes. While a shared
loan of a place is live, nothing may change, move, or lend `mut` an
overlapping place. While a `mut` loan is live, nothing else may use an
overlapping place at all. So `swap(mut first, second: mut first)` is an
error, and `mut items.push(9)` is allowed once `middle` is no longer used, as
in SYNTAX.md's example. A loan of a view is also a loan of what the view
views.

The operands of one operation are evaluated in order, and an operand stays
as it was evaluated until the operation runs. The operands are the arguments
of a call, the fields of a constructor, the elements of a literal, the
scrutinees of a `match`, the collection and then the keys of an index, and
the value of an assignment and then the keys of its target.

- **An evaluated operand is lent until its operation runs.** An operand
  that is a place lends the place, and an operand of a view type lends what
  it views. A later operand may read what is lent, but may not change it,
  move it, or lend it `mut`. So `show(items[0], count: grow(mut items))` is
  an error, as in Rust: the call would be given an element of a list that
  `grow` has since changed. An operand that is a copy lends nothing.
- **A `mut` borrow for an argument begins at the call,** after every
  argument is evaluated. So `mut items.push(items.length())` is allowed, as
  Rust's two-phase borrows allow it. At the call, two places that the call
  borrows may not overlap if one of them is borrowed `mut`.

### Views

DESIGN.md's views are second class: they never outlive the function that
made them. The checker keeps them so with rules that need no annotations,
all read from one account of what a value views:

- **A call's result views everything its arguments lend it.** A result of a
  view type holds the loans of every argument lent to the call, read-only or
  `mut`, that is not `Plain`, and of every view-typed argument.
  `found.unwrap_or(default: backup[..])` therefore views `backup`, and
  `mut backup.push(9)` is rejected while the result is in use. Plain-data
  arguments, such as an index, lend nothing, so the rule rarely holds more
  than it must.
- **A place given `mut` that can hold views takes on the same loans,** since
  the callee may keep a view in it. After `mut views.push(data[0..2])`,
  `views` views `data`, and `mut data.push(4)` is rejected while `views` is
  in use.
- **A place assigned a view views what the value does.** After
  `holder.view = data[0..2]`, `holder` views `data`. A variable assigned
  again still views what it viewed before, since the checker follows no
  path one at a time.
- **A local that is a view stands for what it views.** A value read from
  `part`, after `let part = items[0..2]`, views `items` and not `part`, so a
  function may return it when `items` is a parameter.
- **A function returns views only of what reached it through its
  parameters.** A returned view-typed value may hold loans only of its
  parameters and of what they view, never of what ends with the function:
  its locals, and a parameter or `self` it takes `own`, unless that is
  itself a view. A method returning `self.items[1..4]` and
  `Option.unwrap_or` both meet this.
- **What the caller keeps views only the same.** A `mut` parameter, and
  `self` in a `mut self` method, outlive the function, so a view put in one,
  by assignment or by a call that takes it `mut`, must not be of what ends
  with the function. And since the caller goes on using it, nothing it views
  may be changed in the rest of the function.

- **Writing through a slice needs `mut` access to what it views.** A `var`
  that holds a `Slice` or a `StringSlice` can be passed `mut`, or assigned
  through, only if every place it views is mutable: a `var`, a `mut`
  parameter, the variable of a `mut` loop, or `mut self`. A slice held in a
  field is read-only whatever the mode of its holder, because that mode
  says nothing about what the field views. A slice parameter is writable if
  its mode is `mut`. The rule is for the two slice types only: a `var` of
  another view type, such as a cursor, can be passed `mut` over a read-only
  source.

- **A view cannot be passed with a `mut` borrow of what it views.** A call
  that is given a view and that borrows `mut`, as another argument, a place
  that the view views is an error in either order: the callee would hold
  the view and change what it views. The intrinsic operations that give a
  view back to its owner are the exception.

- **Nothing kept may view a temporary.** A temporary lives until the end
  of its statement, so a `let` or `var` whose view, or whose cursor, views
  an owned temporary passed read-only to the call that made it is an error
  that asks to bind the temporary to a name first, as Rust's E0716 does. So
  is a view of a temporary assigned to a place, or passed to a call beside
  a place given `mut` that can hold views. A cursor views what its call's
  read-only arguments view, as a view would. A string literal without
  interpolation is in static memory, so viewing one is fine.

A value of a view type may be bound by `let` or `var`, held in local records
and collections, and passed as an argument. It cannot be returned except by
the rule above, and cannot be placed where an owned, storable value is
required, such as an `own` function-typed parameter. Putting a view into a
record or a list makes that record or list a view, so "a view cannot be
stored" holds by construction.

A function type does not say whether a function captures, so every function
type is a view type, and the value decides what it views:

- **A named function, or a lambda that captures nothing, views nothing.** It
  can be returned and stored like any plain value.
- **A lambda that captures views what it captures and its environment.**
  The environment is the record of what the lambda captured. It is a local
  of the function that the lambda is written in, whatever the lambda
  captures, a parameter included. So a lambda that captures cannot be
  returned, alone or inside a record or a collection, and cannot be put in
  a place that the caller keeps. It can be passed to a call, and held in a
  local record or list that stays in the function. DESIGN.md's answer for a
  `make_adder` is a record with a method.
- **A function value given to an `own` parameter must capture nothing,**
  because the callee may keep it after the caller returns. A lambda that
  captures is refused there, and so is a function value that the caller
  does not own, such as a read-only function-typed parameter, which may be
  a lambda that captures.

A lambda cannot change what it captures, which is a type error: captured
variables are read-only inside it.

### Owned values where they are required

A `var`'s initializer, the value of an assignment, an `own` argument, a
field, a collection element, a part of a tagged string, and a returned value
must be owned. A place there must be marked `own` or copied with `copy()`,
unless it is `Plain`. Otherwise the error offers both fixes.

- **The type checker reports a missing mark.** The rule depends on the
  marks, which only the syntax tree has. In the core form, reading a value
  out of a place that is not `Plain` is always a move that the source
  allows.
- **A returned place needs no mark.** Returning an owned local moves it.
  Returning a place that is not owned, such as a read-only parameter, is an
  error with a fix that copies it.
- **A constant expression is exempt.** The compiler evaluates the value of
  a constant and a default, so a constant used inside one is not moved at
  run time.
- **A tagged string takes its parts,** because each part goes into the
  template that its tag receives. A plain string only reads the values it
  interpolates.
- **A yielded constructor lends its places instead.** In
  `yield Some(self[index])` the field is lent, not taken, so it needs no
  mark (see [Yielding and lending](#yielding-and-lending)).

### Yielding and lending

- **A `lends` method yields exactly once on every path,** as Swift checks
  its `_read` and `_modify` accessors. The checker finds a path with no
  `yield` or with two, and reports it. What it yields has the mode the
  signature states, and may be a part of `self` or a value the method made.
  A `lends` method cannot drive a `for` loop or be pulled.
- **A lending call lends the whole place it is called on,** for the rest of
  the caller's statement, read-only or `mut` as the method takes `self`. A
  `while` loop's test is a statement of its own for this, so what the test
  lends goes back before the body runs. Until then, a use of a place lent
  `mut`, or a change of one lent read-only, is an error, and so is passing a
  place to a call beside a part it lends when either is `mut`. An index of
  a collection other than a `List`, a `Slice`, or an `Array` is such a call,
  so two indexes of a user's collection are never lent `mut` in one
  statement, and `grid[a] = grid[b]` needs the right side in a `let` first.
- **A yielded constructor lends the places among its fields.** A lookup that
  can miss lends an `Option`, as in `yield Some(self[index])`, and the
  element stays in the collection. So in the constructor written directly
  after `yield`, and in a constructor that is a field of it, a field that is
  a place is lent to the value that is built, and needs no `own` and no
  copy. The place is anything the method could yield by itself: a part of
  `self`, a parameter, or a local.
  - A method that yields or lends read-only lends every place read-only. A
    `Plain` place is copied instead, as in any constructor.
  - A method that yields or lends `mut` lends the places that are marked
    `mut`, as in `yield Indexed(index: index, value: mut self[index])`.
    When the lend ends, such a place has the value of its field as the
    caller left it. A field without the mark takes a value, as in any
    constructor, so `index` is a copy, and a place there that is not
    `Plain` is an error whose fix is the mark. Two places lent `mut` to
    one value may not overlap: the same place twice is an error, and two
    indexes are an obligation for the prover, as for two `mut` arguments.
  - A yielded value that lends a place owns nothing. Each of its other
    fields is a constructor or a `Plain` value, such as an index or a
    slice. An owned value there is an error
    (`ownership.owned_beside_lent`) that says to bind it to a name first:
    the name is a place, and is lent like the rest. A yielded constructor
    that lends no place is an ordinary owned value.
  - A slice is a value, so `rest: self[1..]` is taken, not lent.
  - A method that yields such a value yields places, so it can be pulled
    only where the element is `Plain`.
- **A part that is lent goes back.** Returning it, storing it, or giving it
  to an `own` parameter is an error unless it is `Plain`, and so is binding
  it with `let`, since the name would outlast the statement. Matching one
  binds views of its parts, or `mut` access to them when it is lent `mut`.
- **A `yields` method may yield any number of times.** Calling it as a
  `for` loop's expression drives the loop. Calling it anywhere else makes a
  cursor, which is a view of the receiver when the method takes `self`, and
  owns it when the method takes `own self`. A method that yields `mut`
  cannot be pulled, which is an error at the pull: a `next()` call, or a
  `for` loop over a cursor held in a variable.
- **A pull hands out an owned value.** `next()` returns `Option[Element]`,
  so a method that yields read-only views of places, as `List.each` yields
  `self[index]`, can be pulled only where its element is `Plain`, which is
  copied implicitly anyway. A named place counts, whether a field, an
  element, a parameter, or a local. Anything else would be copied unasked,
  which DESIGN.md rules out, so pulling it is an error that suggests a `for`
  loop or a method that yields owned values. A method that yields only
  temporaries, such as calls' results, yields owned values, which a pull
  moves.
- **Pullability is worked out from the body,** as DESIGN.md says. A
  `yields` method whose yields reach a recursive call, through a `for` over
  a method in its own call cycle, cannot be pulled, and whether a method
  yields views of places is read from the body too. This is the one fact
  callers read from a body. It is stored apart from the interface, and a
  caller reads it only when the caller pulls the method.

### `parallel`

Each branch of a `parallel` block, and each iteration of a `parallel for`,
is checked as if it ran at the same time as the others. A place that one
branch changes, by assignment, `mut`, or `own`, must not overlap any place
another branch uses, with disjointness obligations for indexes as above. A
`parallel for` may change only its own element and its own locals.

## Capabilities

### What code may call

At each point in a body, a set of capabilities is *available*: the
function's `uses`, its capability parameters, and the capabilities provided
by each enclosing `provide`. Inside a capability `impl`'s methods, it is the
`impl`'s `uses`, which are each method's own. A call there through a
function value may also use the capability itself, which means this
implementation, so a method can hand it on to a function it is given; code
generation passes the implementation's own evidence. A direct call of the capability would
call the implementation itself, so it still needs the capability among the
`impl`'s `uses`, from outside.

The check runs on [the core form](#the-core-form), where every call is a
node, including the calls that sugar expands to. So a `for` loop over a
collection needs the capabilities that the collection's `each` uses, and an
interpolated string needs the capabilities that the `display` of each value
uses. A definition with an error has no core form, so it is not checked
until the error is fixed.

- **A capability call,** such as `Clock.now()`, needs its capability
  available.
- **A call to a function with `uses`** needs every capability in it, after
  its capability parameters are substituted, to be available.
- **A call through a function value** needs the capabilities of the value's
  type.
- **A lambda's body may use what the lambda's type lists,** which is the
  function type the lambda is checked against.
- **A capability parameter stands for a set of capabilities, which is
  solved wherever its function, method, or type is used.** A call of
  `for_each[capability Granted]` has a set of its own for `Granted`, as it
  has a type of its own for a type parameter, and so has a value of a type
  that has one. The set is in every type that got it from there: the
  function type a lambda is checked against, the type of what the call
  gives, the type of a local that holds it. It is the least set that holds
  what must be within it: what each function that meets such a type uses
  beyond what the type lists, and what a lambda's body needs beyond what
  its type lists. So `for_each(3, visit: tick)` needs `Clock` when `tick`
  uses it and `visit` is a `(fn(Int64) uses Granted)`, and after
  `let kept = later(tick)`, where `later` gives back the function it is
  given, `kept` is a `(fn() -> Instant uses Clock)`, and calling it needs
  `Clock`.
- **The sets are solved once the whole definition is checked,** since what
  must be within one can be anywhere in it: a `var` that holds what a call
  gave may be assigned another function later. Until then a set is an
  unknown in the types that hold it, which decides nothing else about them.
  Where a type that holds one meets a type that lists capabilities, the set
  must turn out to be within those, or, where the two types must be the
  same, to be those. Every type the checker gives out has each set in
  place of its unknown, and each call's type arguments have the set where
  the capability parameter is.
- **A function's own capability parameter stands for itself** throughout its
  body. Inside `for_each`, a `(fn(Int64) uses Granted)` takes only functions
  that use `Granted` or nothing. A call of `for_each` by itself is a call
  like any other, with a set of its own, which is `Granted` when it passes
  on the function it was given.
- **What states and does not run** has no capabilities at all, not even
  `Panic`, since what it means must be a value: a contract's clauses, what
  a function-typed parameter requires, a loop's clauses, a type's invariant
  and potential, a law, a proof, and a quantifier's body, whatever the
  function around it declares. **`parallel` branches and `parallel for`
  bodies** have only `Panic` available. A test without `uses` has only
  `Panic`, and whatever it provides.
- **A `uses` clause that is never needed is not an error,** since a function
  may declare a capability its later versions will use, and callers already
  provide it.

### `provide`

`provide implementation, ... { body }` checks each implementation like an
argument: a temporary is owned, a place is lent shared, and `mut place` is
lent `mut`. The capabilities provided are every capability its type
implements, found by looking up the capability `impl`s for the type in its
own package and in the packages of the capabilities visible here. A place
must be marked `mut` exactly when one of those `impl`s has a method that
takes `mut self`, with a fix that adds or removes the mark. The capabilities
each `impl` uses must be available at the `provide`. Providing anything that
implements `Panic` is impossible, since nothing can.

### Dependency grants

DESIGN.md says a dependency may use only the capabilities its manifest entry
grants, and that a grant is checked wherever the dependency's code is named.
The type checker enforces this where it can see a dependency's capabilities,
which is at the signatures of its code, never its bodies. Every capability
in those `uses` must be granted, except those that arrive through a
capability parameter, which are the caller's own. A dependency's code is
named by:

- **A call** to its function or method, or to a method of its trait, and to
  the `impl`'s method that then runs, when the `impl` is known.
- **Its function taken as a value,** since whoever is handed the value may
  call it.
- **Its `impl` meeting a bound,** which is checked in the one place a bound
  is held: for a call's type arguments, for the arguments of a type that is
  written, for `any value`, and for the bounds an `impl` must itself meet.
  The `impl` found is checked, and so are the `impl`s that meet its own
  bounds in turn, as the `impl` of `Source` for `List[Timer]` is met through
  the one for `Timer`. An `impl`'s methods can use only what their trait
  declares, so only a trait whose methods have `uses`, or an `impl` of a
  capability, ever asks for a grant here.
- **A `provide`** of its type, for the capabilities its `impl`s use.

Inside the dependency, its own bodies are checked against its own
signatures, so nothing it does can exceed what its signatures declare.

- **A grant is one query,** by the package and the dependency: the
  capabilities the manifest's entry names, each found as a definition. A
  prelude capability is named by its name and any other by its full path,
  so two capabilities that share a name are never taken for each other.
- **A package the manifest does not list is granted nothing,** which is how
  an `impl` in a package further away is caught.
- **The error names the code and the capability,** and says what to add to
  which entry. It has no fix: DESIGN.md has a grant always be a choice
  someone made. A dependency that offers both a client and a server needs
  only the grants for what the program names.

### The manifest

Each definition's result says which packages it uses, and the union over a
package's definitions, its tests apart, is what `truss publish` publishes
it with. Two rules about a package's manifest need its code too, so they
are package checks, reported with the manifest's file and not in a module:

- **A grant that names no capability** is an error, so a misspelled
  capability is not silently one that is never granted.
- **A dependency that nothing in the package uses** is an error, as an
  unused `use` is. A package uses a dependency by naming it in a path, by
  calling a method of one of its traits with a dot, or by an `impl` of it
  answering a call or meeting a bound. Each definition's result says which
  packages it uses, and the check is their union. It is made only of a
  package whose code all checks, since a call in a body with an error may
  not have been worked out, and the fix deletes the entry.

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

A type has at most one `impl` of a trait for each set of trait arguments,
whatever its own type arguments. Two `impl`s of one trait for one type
constructor overlap when their trait arguments unify, treating each `impl`'s
generic parameters as variables, so `impl Add[Element] for Vector[Element]`
beside `impl Add[Int64] for Vector[Element]` is an error. An `impl` for a
bare generic parameter, which would cover every type matching a bound, is
not allowed, as DESIGN.md says.

### Finding an `impl`

To find the `impl` of a trait for a type, the checker looks only in the
packages the location rule allows: the trait's, the type's, and those of the
trait arguments' outermost types. Each lookup is one query, such as "the
`impl`s of `Add` for `Instant` in the package of `Duration`", so adding an
`impl` re-checks only the definitions that asked that question.

An associated type is read from the `impl` that matches the type, whether or
not the bounds on that `impl`'s parameters hold. `impl`s do not overlap, so
no other `impl` could answer, and a bound that does not hold is reported
where the trait is asked for. Reading the type therefore asks nothing of
the type's arguments, which is what lets a type's properties turn on an
associated type without a question coming back to itself.

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
- **A method can be called through `any`** when it takes `self`, `mut self`,
  or `own self`, has no generic parameters of its own, and neither takes nor
  returns `Self`. Calling any other method is an error at the call.

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
  range or a collection is an expression in code as well; one over a type,
  and `==>`, are errors in a body that is compiled, which the parser leaves
  to this stage since only the signature's types say whether a body is.
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

Whether an expression is constant is read from its checked form, not from
how it is spelled:

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

## The checked form

The checked form of a definition is a set of tables keyed by the tree's
node ids (see [Node identity](#node-identity)). The tools read it, because
they answer questions about the source as it is written, broken code
included: the type at a position, what a name means, the holes. The usage
check reads it for which statements never finish. Every other check, the
prover, and code generation read [the core form](#the-core-form) instead.
The tables record:

- **the type of every expression,** with no inference variables
- **what each name means:** the definition and its type arguments, the field
  or variant, the method's version by receiver mode, the `impl` chosen for a
  trait method, and each normalized associated type
- **each call's arguments:** the parameter each goes to, its mode, the
  defaults left out, and every conversion from the
  [No subtyping](#no-subtyping) table
- **each literal's type and value,** with floats already rounded
- **each pattern's variants and fields,** and the order of arms
- **each call of a lending method,** with how the part it gives is lent
- **the capability set** at each call, with each capability parameter of
  what is called solved among the call's type arguments, and the evidence
  each `provide` builds, for each capability its implementations implement
- **obligations** that the type checker created, as described next

It is canonical, so that two checks of the same definition give equal
results, and the database saves it with the graph, as DATABASE.md
describes.

### The core form

The core form is the type checker's output for one definition: a typed,
desugared tree. Ownership checking, the prover, and code generation read it
instead of the syntax tree, and none of them repeats a decision that the
type checker made.

A definition has a core form if it parsed completely and has no error. A
definition with an error has none, and no later stage runs on it.

The core form records these decisions:

- **Calls are resolved.** Every call names its callee and has one argument
  per parameter, in parameter order. The receiver of a method is the first
  argument. An omitted argument is marked as a default, and the default
  expression is in the callee's own core form. A callee is a function or a
  method of a type with its type arguments, a trait method with the
  evidence that selects its `impl`, a capability method, an operation of
  `standard::intrinsic`, or a function value (an indirect call).
- **Every expression is a place or a value.** A place is a local, a
  constant, a field of a place, the result of a lending call, or a
  temporary that holds a value for the enclosing statement. An index
  expression is a lending call of `Index.at`. Every place carries its type.
- **An operand is a borrowed place or a value.** The operands are: an
  argument, the scrutinee of a `match`, a `let`, or an `is`, the operand of
  a `yield`, a field of a constructor, an implementation in a `provide`, an
  indirect callee, an interpolated value, and the cursor of a loop. Reading
  a value out of a place is a node of its own. It copies the value if the
  type is `Plain` and moves it otherwise. Code that only borrows a place
  never has that node.
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
- **Syntactic sugar is desugared.**
  - `?` is a `match` that evaluates to the success value or returns the
    failure.
  - A compound assignment such as `total += step` evaluates its target
    once, and assigns the result of the operator applied to the target's
    current value.
  - A `for` loop over a collection is a loop over a call of the
    collection's `each`.
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
  constructed at run time. An interpolated string records its pieces, the
  `display` method of each interpolated value, and the methods of the text
  builder. Widening a function value, and
  converting between a built-in integer and `Integer`, are explicit
  conversion nodes.
- **A cost term over a bound names the trait method.** `time(Element.equal)`
  in a cost bound is a node that holds the trait method, with the type
  parameter as its self type.
- **Every node has a type.** The type is fully inferred and normalized. It
  contains no inference variable and no hole.
- **A condition says whether it is executable.** A `requires` clause or an
  `assert` is executable if it can be evaluated at run time: it contains no
  quantifier, no `Integer` value, no `old` or `result`, and no call of a
  specification-only function.
- **A block says whether it diverges.** A block diverges if control never
  reaches its end. The code after a `return`, or after a loop that nothing
  leaves, is then known to be unreachable without inspecting types.
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

Core nodes hold no source spans, so reformatting a definition does not
change its core form. The span of each syntax node, by id, is a separate
result that only code that shows source asks for.

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
  compares each pair of fields in order with `&&`, so it stops at the first
  difference.
- **`hash`** writes the variant's index, counted from 0 in declaration
  order, and then hashes each field.
- **`compare`** orders by variant index. For two values of the same
  variant, it compares the fields in order, and the first pair that is not
  equal decides.
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

A result depends on exactly what it read through `Query`, and the database
pushes a change in any of these to the results that read it:

| What a result reads | Example |
|---|---|
| The resolved form of a definition, or a part of it | The body of `parse_config` |
| The interface of a definition | The interface of `List.push` |
| The shape of a type | The shape of `Point` |
| The facts of a type's definition | What must be `Plain` for `Option` to be |
| The value of a constant | `digest_size` |
| The names a file defines with one name | The definitions named `count` in `report.truss` |
| A module | Whether `standard::json` exists, and its visible names named `parse` |
| The members of a type with one name | The members of `List` named `length` |
| The traits of a package that declare a method with one name | The traits of `standard` with a method `compare` |
| One thing a package's manifest says | The modules of `weather`, or its dependencies, or the width of its `USize` |
| The `impl`s of a trait for a type constructor, in one package | `Add` for `Instant`, in the package of `Duration` |
| The capability `impl`s of a type | The capabilities `MemoryFiles` implements |
| A body fact | Whether `Tree.each` can be pulled |
| A manifest entry | The capabilities granted to `http`, each as the definition its name means |

A lookup across a package is a lookup in an index built from what the
package's files declare, and from nothing else:

- **A package's declarations are listed once,** and each index is one pass
  over that list: its methods and member constants by owner and name, its
  traits by the names of their methods, its `impl`s by trait and type, and
  its types by the groups that contain each other. A method written inside
  a trait is declared as that trait's, so finding the traits with a method
  `compare` reads no trait's interface.
- **Each question about an index is a result of its own,** so a definition
  that asked for the members of `List` named `length` is checked again only
  when that answer changes, though the index is rebuilt whenever the package
  declares something new.
- **What a manifest says is read one thing at a time.** A result that reads
  a package's modules is not worked out again when its dependencies change.

What each kind of result depends on:

- **A resolved form** depends on its own tree, the file's `use` lines, and
  the name lookups it made.
- **An interface** depends on the resolved signature and the shapes and
  interfaces of the types and traits it names.
- **A checked body** depends on its own resolved form and interface, and on
  the interfaces, shapes, and lookups it used. It never depends on another
  body, except through a pulled method's pullability.

So the costs of everyday edits follow from what each result reads:

| Edit | Checked again |
|---|---|
| A function's body | That body. Its interface is unchanged, so nothing else. |
| A local's name | That body |
| A function's `ensures` | That function's clauses, and no caller's types. Callers' proofs are PROVER.md's. |
| A function's parameter type | That function, and every definition that read its interface |
| A method added to `List` | Definitions that looked up a member of `List` with that name |
| An `impl` added | Definitions that looked up `impl`s of that trait for that type in that package |
| A definition added to a file | Definitions in that file that looked up that name, including bindings checked for hiding |
| A field added to a type | Definitions that used its shape, and those that asked a fact of it that came out different |
| A definition moved to another module | Its users' names, which re-checks their types. Their test results are already done, because a test's key holds no names, as CODEGEN.md describes. |

## Diagnostics

Diagnostics use the shared `Diagnostic` type from [LEXER.md](LEXER.md), with
codes such as `resolve.unknown_name`, `types.mismatch`,
`types.missing_label`, `patterns.not_covered`, and `ownership.use_after_move`.
Every diagnostic is an error, since Truss has no warnings, and the checker
gives an exact fix whenever it knows what was meant:

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
- **The reading of `f[X]` is stated.** An error in `f[X]` says which reading
  applied, such as "`parse` is a generic function, and `[Int64]` is its type
  argument", as DESIGN.md asks.
- **Habits from other languages** that need types are reported with fixes,
  such as `pair.0` and a tuple `(a, b)`, which say that Truss has no tuples
  and point to the record types in the standard library.
- **Holes are not errors.** A `todo` is reported to the tools with its type
  and the names in scope, as SYNTAX.md describes, and builds refuse programs
  that can reach one.

## Interfaces to other stages

- **The parser** gives one syntax tree per definition, with positions
  relative to it and an id on every node. Later stages record what they
  decide in tables keyed by those ids, and never change the tree. For a
  broken definition, the parser keeps what PARSER.md states, and the type
  checker relies on it as [Broken definitions](#broken-definitions)
  describes.
- **The prover** reads core forms, the interfaces and contracts of what
  they call, the functional bodies it reads as definitions, and the type
  checker's obligations, as [PROVER.md](PROVER.md) describes. It discharges
  every `requires` and invariant, every operation that could fail, every
  cost, termination, and every obligation above.
- **Code generation** reads core forms, the shapes of types, and which
  methods can be pulled, as CODEGEN.md describes. Instantiation cycles have
  already been rejected.
- **The build** uses core forms to find what `main` can reach, to refuse
  programs that can reach a `todo` or an `echo`.
- **Tools** show the type of an expression and the definition a name means
  from checked forms, and list every hole with its type, the names in
  scope, and what it blocks.

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

When a call to a trait's yielding method resolves to a known `impl` that
defines the method, the checker records the callee as the `impl`'s method,
not the trait's. `List` gets `each(self)` from `impl Iterable`. The type of
the cursor and the contract of a loop over a list must then come from the
list's `each`, which only the `impl`'s method has.

## Not built

- **An interpolated string as calls.** It is still a node that names the
  text builder's methods and each value's `display`. It will be desugared
  to those calls once they have `time` clauses.
- **A contract as a result of its own.** DESIGN.md has callers' proofs read a
  function's contract, apart from its interface and its body. The contract
  is type-checked with the body, and the prover reads it from the callee's
  tree, so a change to a callee's body reaches its callers' proofs, which
  then find each query's answer kept by the query's text.
- **Checked forms stored in a specified encoding.** They are kept as OCaml's
  marshaled values, as DATABASE.md describes.
- **A shape that ignores the order of fields.** DESIGN.md says reordering a
  type's fields rebuilds nothing. A shape keeps its fields in the order they
  are written, so reordering them re-checks what reads the shape. Code
  generation's layout already ignores the order.

