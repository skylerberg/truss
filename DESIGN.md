# Truss Design Decisions

This document records what Truss code means and why. For how code is written,
see [SYNTAX.md](SYNTAX.md). For the goals behind these decisions, see
[GOALS.md](GOALS.md). Nothing is built yet. This is the design agreed so far.

## Source code

- **Text files are the source of truth.** Programmers and tools edit ordinary
  files.
- **The compiler stores each top-level definition by its content.** It parses
  each definition, resolves its names, and hashes the result. Whitespace and
  the order of signature clauses do not affect the hash, so reformatting never
  triggers a rebuild.
- **The hashes record what each definition depends on.** This lets builds,
  tests, and proofs redo only the work a change actually affects.
- **A function's signature and body are hashed separately.** Type checking and
  proofs in callers depend only on the signature. Changing a body without
  changing its signature, such as filling in a `todo`, re-checks no callers.
  Only code generation and the affected tests run again.
- **The order of a type's fields does not affect its hash.** Reordering fields
  rebuilds nothing, except code that uses a derived `Ordered`, which compares
  fields in declaration order. The compiler chooses memory layout, and a record
  with more than one field is always built with named arguments, so field
  order is otherwise never observable.
- **A parameter's default is hashed apart from the signature.** The signature
  records only that the parameter has a default. Type checking in callers
  depends only on that, so changing a default re-type-checks nothing. Callers
  that leave the argument out depend on the default itself, so their proofs
  and tests are checked again; callers that pass it are not affected. The
  default is filled in by the function, not copied into each caller, so only
  the function is compiled again.
- **Each derived implementation is its own definition.** `derives Hash` on
  `Point` stands for a separate `impl Hash for Point`. Its hash comes from the
  trait, the shape of `Point`, and the version of the compiler's rule for
  deriving `Hash`. The generated code is never stored. Adding a derive changes
  nothing that already exists. Changing a field re-checks only code that
  compares, hashes, or orders the type. A compiler release that improves a
  derivation rule invalidates only the implementations made with it.

### What you see is what compiles

Invisible characters that change how text is displayed are a compile error
anywhere in a source file, including inside strings. They have no other use
in source that an escape cannot serve.

- **Bidirectional controls** can make code display differently from how it
  compiles, the "Trojan Source" attack (CVE-2021-42574). Truss has no
  comments, so string literals are where such an attack would hide. Rust
  rejects these characters in the same way; Go, Java, and Python leave
  detection to editors and review tools.
- **Control characters** such as escape and backspace can make a terminal
  hide or rewrite lines in `cat` or `git diff`.
- **Other invisible characters**, such as zero-width spaces and Unicode tag
  characters, can make two strings look the same or hide text from a human
  reviewer that an LLM still reads. Hiding instructions this way is a known
  attack on LLM agents, which write and review much Truss code.

The zero-width joiner, the zero-width non-joiner, and the variation selectors
stay legal, because emoji and scripts such as Persian need them in visible
text. Anything rejected can still be written in an ordinary string as an
escape, such as `\u{2068}`, so a rare legitimate use is visible in review.

## No comments

Truss has no comments. Comments go stale without the compiler noticing, and
LLMs tend to fill code with comments that repeat what it already says. Truss
moves what comments usually explain into forms the compiler checks:

- **Names** say what something is. The naming rule (whole words, no
  abbreviations) makes them descriptive.
- **Signatures, `requires`, and `ensures`** say what a function does.
- **Invariants and laws** say what always holds for a type or trait.
- **Cost clauses** say how expensive a call is.
- **Tests** show how code is used, and their names record requirements.

Reasons that would otherwise go in a comment ("why is this done this way?")
belong in a name. For example, a function called
`treat_missing_account_as_empty` explains itself without a comment. Writing
about a whole package, such as guides and overviews, lives in ordinary
documentation files beside the code.

## Line breaks

Statements end at a line break, following Go's rule: a line break ends a
statement when the line ends with a token that can end one. Truss adds a short
list of tokens that may start a continuation line: `.`, `else`, `with`, `|`,
`=>`, `->`, the clause keywords, and binary operators that cannot begin an
expression. Inside `(` and `[`, line breaks are ignored, as in Python.

- **It fits how Truss code is laid out.** Clauses sit on the lines after a
  signature, variants start with `|`, and the body's `{` follows the
  clauses. Go's rule alone would forbid all of these.
- **It allows the method chains LLMs write by habit,** with each `.` at the
  start of a line, as in Kotlin, Swift, and Rust.
- **It never guesses.** JavaScript continues a line whenever the next one
  could continue it, so a line starting with `(` silently calls the line
  before. Truss's rule is fixed by the tokens alone. The cases it reads as
  two statements, such as a line starting with `-`, leave an unused value,
  which is a compile error, so they are caught rather than misread.
- **The lexer decides alone,** because keywords are reserved. The rule needs
  no type information and no knowledge of what the parser is doing, and
  indentation never matters, unlike in Haskell or Python.

## Syntax from other languages

LLMs have seen far more Rust, TypeScript, Python, Go, and C than Truss, so
they will often write those languages' syntax by habit. Truss treats this as
a design input rather than user error:

- **Each common habit gets its own error and an exact fix.** `i++`, `&mut x`,
  `let mut`, `|x|` closures, `;`, and `// comments` each produce a message
  that names the Truss form and a replacement that tools can apply
  directly. With fast inference, the time an agent spends in a confusing
  edit-compile loop is what dominates, so a precise fix saves more than any
  other diagnostic. This follows Rust, Swift, and Elm, which give targeted
  errors for syntax from other languages, rather than Go and Zig, which
  mostly do not.
- **Foreign sequences are rejected, not reinterpreted.** `--x` could mean
  `-(-x)`, and `//` could lex as two divisions; both are errors instead, so
  that a habit never compiles to something unintended. This also keeps those
  sequences free: if Truss ever adds comments, `//` can mean a comment
  without changing what any existing code means.
- **Nothing foreign is accepted and cleaned up later.** Ignoring a stray `;`
  would be friendlier at first, but it would give each construct two
  spellings and make files differ until they were formatted.

## Types and inference

- **Signatures are written out in full.** Parameter types, return types,
  top-level constants, and capabilities (`uses`) are never inferred, so a
  signature can be read on its own.
- **Constants are worked out when compiling, from literals only.** A constant
  is built from literals, arithmetic, other constants, and records and
  collections of those, but it cannot call functions. This follows Go's
  constants, and it keeps the first compiler free of an interpreter: allowing
  calls would mean running Truss code while compiling, with exactly the same
  results as the target machine, including float functions from libc and the
  size of `USize`. Rust started with similarly limited constants and has
  widened them release by release without breaking code, and Truss can do the
  same once it has a compile-time evaluator. Tagged-template checks will need
  that evaluator anyway, and constants should then share it.
- **Bodies are inferred.** Local variables and lambdas do not need type
  annotations.

### Single-field records

Giving values that mean different things their own types, such as `UserId` and
`OrderId`, or `Meters` and `Feet`, turns mixing them up into a type error.
Truss does this with a record that has one field, such as
`type UserId(number: UInt64)`, rather than a special wrapper syntax:

- **No new concept.** It is an ordinary record, so construction, field access,
  `with`, invariants, and `opaque` all work as they do for any record.
- **The author names the field.** `port.number` says what is inside. A built-in
  name such as `.value` or Rust's `.0` would not. Building one still needs no
  label, because a record with one field can take a bare value: `UserId(42)`.
- **It costs nothing at run time.** A record with one field has exactly the
  same representation as the field.
- **Operations are not inherited.** The record does not get the field's
  methods or operators, because many would not make sense: adding two
  `UserId`s is meaningless.

Truss has no type aliases either, so a type name always means exactly one
type.

### No tuples

Truss has no tuples. Values that belong together go in a record:

- **Every value has a name.** Tuple elements are read by position, as in
  Rust's `.0` or Python's `[0]`, which says nothing about what they mean.
- **Values cannot be swapped by accident.** In a pair of two `Int64`s, such as
  a width and a height, nothing stops a caller from reading them in the wrong
  order. Named fields rule this out.
- **Signatures say more.** `-> Option[Extremes]` with fields `lowest` and
  `highest` explains itself, while `-> Option[(Int64, Int64)]` does not.

The standard library provides `Indexed`, `Entry`, and `Pair` for the common
cases, and record patterns leave out the type name, so taking a record apart
stays short: `for (index, element) in scores.enumerate()`. That pattern
looks like a tuple but matches fields by name, so `(i, item)` is an error
that names the real fields rather than a silent positional match. Elm made a
similar choice when it limited tuples in favor of records, and Go has no
tuples either.

If small one-off groupings turn out to be too verbose, anonymous records with
named fields could be added later, written `(lowest: 1, highest: 9)`. They
would keep the names, unlike tuples.

### Building values and calling functions

A record is built the way a function is called, and its fields are declared
the way parameters are: `type Point(x: Float64, y: Float64)` is built as
`Point(x: 0.0, y: 0.0)` and matched as `Point(x, y)`. One set of rules covers
calls, construction, and patterns.

- **Arguments after the first are named.** The argument against tuples, that
  two values of the same type can be swapped by accident, applies just as much
  to `copy(backup, original)` or `connect(host, true, false)`. Google found
  swapped arguments of the same type to be a recurring bug in production Java
  ("Detecting Argument Selection Defects", OOPSLA 2017). A single-field record
  type helps only when the two arguments have different types; labels also
  tell `source: Path` from `destination: Path`.
- **The first argument may be bare.** A function's name usually says what its
  first argument is (`sqrt(area)`, `copy(original, ...)`), so a label there
  would only repeat it. This is the Objective-C and Smalltalk convention, and
  the one Swift's API guidelines arrive at. The first argument may still be
  labeled when that reads better.
- **A variable with the parameter's name needs no label.** `copy(source,
  destination)` passes the variables `source` and `destination`, as OCaml's
  `~source` and Gleam's `source:` do. Labels cost nothing when names already
  agree, which is the common case, and must be written exactly when names
  disagree, which is when swapping is possible. A bare name goes to the
  parameter it names wherever it appears, so `copy(destination, source)` is
  reported as out of order rather than silently swapping the two.
- **No declaration syntax decides labeling.** Swift lets each parameter opt
  out of its label with `_`, so how to call a function depends on choices its
  author made. In Truss the rule is the same for every function, and parameter
  names are always part of the API. Renaming one is a breaking change, which
  the rename tool handles within a project.
- **Calling through a function value is positional.** Function types have no
  parameter names, as in Swift since SE-0111, where labels in function types
  had created confusing conversions between otherwise identical types.
- **Records differ in two ways.** Fields can be written in any order, and only
  a record with exactly one field takes a bare value, as in `Some(3)`. Field
  order has no meaning in a record, so a bare first argument would make it
  part of the record's API, and reordering fields could change what callers
  build. A function's parameter order is part of its API in every language.
- **`{` always starts a block in an expression.** Building records with braces,
  as Rust and Go do, makes `if kind == Kind.Unit { x }` ambiguous: it could be
  a record with the field `x` or a block returning `x`. Rust and Go need a
  special rule for record literals before a block. With parentheses, the
  question never comes up.
- **Declarations look like construction.** A record is declared as
  `type Point(x: Float64, y: Float64)`, the shape it is built and matched in,
  as with Java's records, Kotlin's data classes, and Scala's case classes.

#### Defaults

A parameter or field can have a default, which can be left out when calling or
building:

- **Adding a parameter is a change in one place.** Without defaults, every
  caller must be edited, which in a codebase shared by many agents is a large
  diff that collides with their work. With a default, only the function
  changes.
- **Without overloading, defaults are the alternative to near-duplicates.**
  Languages without either grow workarounds: Rust's `sort`, `sort_by`, and
  `sort_by_key`, Go's options structs, and builder types.
- **A default is a constant.** It follows the rules for constants and cannot
  refer to other parameters, so it is the same at every call. It cannot hide
  an effect, and it costs what reading a constant costs.
- **Defaults are applied by the function,** as in Kotlin, not copied into each
  caller, as in C# and Swift. C# is known for callers keeping an old default
  after a library changes it. In Truss, changing a default compiles only the
  function again.

### Type invariants

A type can declare an `invariant`, a condition that holds for every value of
the type.

- **Facts move from signatures into types.** Every `SortedList` is known to be
  sorted, so functions that take one need no `requires is_sorted(...)`, and the
  prover uses the fact for free. A fact carried by a type cannot be forgotten
  at a call site, because nothing that breaks it can have that type.
- **Invariants are proven at compile time, like `requires`.** They are never
  checked at run time.
- **An invariant must hold wherever other code could see the value:** when the
  value is built (directly or with `with`), when it is passed to a call or
  returned, and when the function holding it ends. Between those points, a
  function body may break the invariant temporarily. For example,
  `SortedList.insert` can append an element and then move it into place. This
  is safe because of mutable value semantics: nothing else can see the value
  while it is in the middle of a change. Panics end the program and capability
  calls always return, so no half-updated value can ever be observed.
- **`with` is checked after all of its updates,** so several fields can change
  together.
- **Values from outside the program come in through constructors** that check
  or establish the invariant, such as `Port.try_from(number)`, which returns a
  `Result`.
- **Functions called in an invariant must be pure and have a `time` clause.**
  An invariant is a logical statement, and a function that might never return
  has no well-defined result. If such functions were allowed, the prover could
  derive false statements.

Invariants and opaque types solve different problems. An invariant protects
facts about a value's contents, so a type with an invariant can safely expose
its fields. An opaque type controls where values come from and keeps the
representation private.

## Memory

Truss uses **mutable value semantics**. Every variable holds its own value, and
two variables never refer to the same changeable data.

- There is no garbage collector and no runtime beyond libc.
- **There is no mutable global state.** Values defined at the top level are
  constants. Anything that changes lives in a variable, a parameter, or a
  capability implementation, so all state a function can touch is visible in
  its signature. This is also why many tests can safely share one process.
- There are no lifetime annotations. The only references are read-only views,
  and they cannot be stored (see below).
- A function can modify a caller's value only through a `mut` parameter. An
  `own` parameter takes ownership of the argument. The call site repeats the
  keyword (`sort(mut scores)`), so the effect on each argument is visible
  where the call is made. Truss uses keywords rather than a symbol like `&`,
  which means a read-only reference in Rust and an address in C.
- The same marking applies to method receivers (`mut scores.sort()`) and to
  loops (`for score in mut scores`). Searching for `mut scores` finds every
  place `scores` can change.
- Only places (variables, fields, and elements) are marked. A temporary value
  has no other owner, so it is always handed over as owned and needs no mark.
- **Implicit copies never allocate.** A type made only of fixed-size data
  with nothing on the heap (integers, floats, `Bool`, and records or sum types
  built only from those) copies implicitly, because copying it is a plain
  memory copy. Every other type, such as `List`, `String`, or anything that
  contains them, needs an explicit `copy()`, so the cost of copying shows in
  the code. The compiler works out which types copy implicitly from their
  fields; there is nothing to declare.
- To keep a value while passing it to an `own` parameter, pass `value.copy()`.
- Record updates (`own config with (server.port: 443)`) follow the same
  rules. An owned base is reused in place, so the update costs one write per
  field. Updating a nested field takes a single path, as it does with
  assignment.

### Views

Slices, read-only parameters, and `let` bindings of places can refer to the
original value instead of copying it. This is sound without lifetimes because
views are *second-class*, as in Hylo:

- **The original is frozen while a view is in use.** It cannot be changed or
  moved until the view's last use. Since the name is read-only either way,
  this changes whether a copy happens, never what the code means.
- **Views cannot be stored or returned,** so they never outlive the function
  that made them. The one exception is a method returning a view of `self`.
  There is only one possible source, so the caller knows what the result
  depends on without any annotation. This is Rust's lifetime elision rule for
  `&self`, made the only rule. A record holding views is itself a view.
- **`mut` access never has a name.** It lasts only for a call, a `mut` loop, or
  a `provide mut` block, so there is no mutable reference to track across
  statements. Disjoint parts of one collection can still be passed `mut` side
  by side, because the prover shows the ranges do not overlap.
- **The compiler checks each function on its own.** The rules involve only
  one function body plus the signatures it calls, which keeps checking fast
  and incremental.
- **Owned values are explicit.** A `var`, an `own` parameter, a record field, a
  collection element, or a return value needs an owned value, so a place there
  must be marked `own` or copied with `copy()`. A `let` of a place needs
  neither.
- **The only implicit conversion is from an owned collection to its view.** A
  `List` becomes a `Slice` and a `String` becomes a `StringSlice` when passed to
  a parameter of the view type.

String literals are `String`s in static memory. Creating one costs nothing,
and the first change that needs more room copies it to the heap. Methods such
as `push` may allocate anyway, so cost clauses already account for that copy.

### Closures

A lambda that reads local variables holds views of them, so it follows the
rules for views:

- **Lambdas capture by read-only view.** They can be passed to the functions
  they call, which covers comparators, `map`, `filter`, and `parallel`
  callbacks, but not stored or returned. A lambda can't change or move what it
  captures, so any lambda is safe to call from parallel branches.
- **No changing captured variables.** State that changes as you go belongs in a
  `for` loop or a method like `fold` that returns the result. Function types
  stay a single kind.
- **Only functions that capture nothing can be stored.** A named function, or a
  lambda that uses no local variables, is just a pointer to code. A
  function-typed parameter is non-escaping by default, as in Swift. Declaring
  it `own` lets the function keep it, and then only capture-free functions can
  be passed.
- **Behavior with state is a record with a trait**, not a closure. A
  `make_adder(5)` that returns a closure becomes `Adder(amount: 5)` with an
  `impl`.

This avoids what Rust needs on top of plain closures: `move` closures and
three closure traits (`Fn`, `FnMut`, and `FnOnce`). Hylo's closures are
second-class in the same way, and Zig has no closures at all.


## Methods

A method is a function in its type's namespace (`fn List[Element].push`). The
choices below keep method calls predictable:

- **Methods live with their type.** They can only be defined in the type's own
  package, so a method is always easy to find, and two packages can never add
  conflicting methods to one type.
- **Every call uses parentheses.** A reviewer can tell that `names.length()`
  runs code, and might have a cost, while `point.x` only reads a field.
- **One name can have a version per receiver mode.** The keyword at the call
  site picks the version. One `enumerate` serves read-only, `mut`, and `own`
  loops, where Rust needs three names (`iter`, `iter_mut`, `into_iter`).
  Overloading by parameter types is not allowed, because it makes calls harder
  to predict.
- **Trait methods need no import.** Forgetting to import a trait is a common
  error in languages that require it. Name clashes between traits are reported
  at the call site and fixed by writing the call in full.
- **Each type has at most one implementation of a trait.** An `impl` must live
  in the package of the trait or of the type.
- **Constructors follow one convention.** `Type.new(...)` is the main
  constructor. Other constructors have descriptive names, since overloading
  `new` by parameter types is not allowed.
- Because nothing is shared, the proof system never has to reason about two
  names changing the same memory.

### Equality, ordering, and deriving

- **Deriving is opt-in, with a `derives` clause.** `derives Equal, Hash` sits on
  the type alongside `invariant`, as in Haskell and Scala 3. It is opt-in
  because implementing `Equal` on a public type is a promise to its users, and
  structural equality is wrong for some types, such as a set stored as an
  unsorted list. Truss has no macros, so `derives` covers what Rust's
  `#[derive]` is mostly used for.
- **Laws come for free with derived implementations.** `Equal` must be
  reflexive, symmetric, and transitive, `Ordered` must be a total order that
  agrees with `Equal`, and equal values must have equal hashes. A derived
  implementation satisfies these automatically when its fields do. A
  hand-written one proves them like any other law.
- **Only derived equality lets the prover substitute.** A derived `Equal` is
  true structural equality, so from `a == b` the prover may conclude
  `f(a) == f(b)`. A hand-written `Equal` only promises an equivalence, so the
  prover does not assume that. Switching a type from derived to hand-written
  equality re-checks the proofs that relied on it.
- **Float equality is lawful.** IEEE's `NaN != NaN` breaks reflexivity, and
  Truss proves its laws rather than ignoring them as Swift does. So `==` on
  floats treats all NaNs as equal and otherwise follows IEEE, which keeps
  `-0.0 == 0.0`. NaN is ordered after every number. `ieee_equal` gives exact
  IEEE behavior when numeric code needs it. Float equality is hand-written, so
  the prover never substitutes through it, which matters because
  `-0.0 == 0.0` while `1.0 / -0.0 != 1.0 / 0.0`. The solver's floating-point
  theory, which distinguishes IEEE equality from identity in the same way,
  checks it directly. Lean instead gives floats no lawful equality, which
  would stop a `Point` of floats from deriving `Equal`. SPARK proves NaN never
  occurs, which would make every float division a proof obligation.
- **Derived `Ordered` and `Hash` need a derived `Equal`.** Their laws link them
  to `Equal`. Two derived implementations agree by construction. A hand-written
  `Equal`, such as one for a set stored as a list, would not agree with a
  field-by-field `Ordered` or `Hash`, so such a type writes those by hand too.
- **Comparisons need matching types,** consistent with having no implicit
  conversions.
- **Debug output is built in for every type.** Tools such as the test runner
  use it to show values, so nothing has to be derived, unlike Rust's `Debug`.
  Text meant for people goes through `Display`, written by hand, because a
  structural dump is rarely what a user should see.

### Traits that require other traits

`trait Ordered: Equal` means every `Ordered` type is also `Equal`. This follows
Rust and Swift.

- **Laws can span traits.** `Hash` requires `Equal`, so its law, that equal
  values hash equally, can be stated and proven. In Rust, `Hash` does not
  require `Eq`, and that law is only a comment.
- **No diamond problems.** A type has at most one implementation of each
  trait, so two traits that both require `Equal` share it.
- **Every `impl` is written out.** Rust also allows one `impl` to cover every
  type matching a bound. That makes it hard to tell which implementation
  applies, and it is the source of Rust's long-stalled "specialization"
  feature. Truss needs one `impl` per type, which is empty for a trait that
  only combines others.
- **Methods with bodies cannot be replaced.** A trait method with a body, such
  as `Ordered.max`, is the same for every implementation. So `a != b` always
  means `!(a == b)`, `max` always agrees with `compare`, the prover can reason
  from the trait alone, and adding an `impl` never changes what such a method
  does. The cost is that a type cannot swap in a faster version. That is
  rarely needed, and the type can offer one under its own name.

### Dynamic dispatch

| Need | Use |
|---|---|
| One type, known at the call | Generics with a trait bound (static dispatch, no runtime cost) |
| A fixed set of alternatives | A sum type |
| An open set, mixed in one collection | `any Trait` |

- **The cost is visible.** `any Handler` is a distinct type, written with
  `any` as in Swift, and making one takes an explicit `any value`, which
  allocates once. An implicit conversion would hide an allocation.
- **An `any` value is an ordinary value.** It owns its contents and copies only
  with `copy()`. If its contents hold a view, it is a view too.
- **Limits apply to calls, not traits.** Methods that need the concrete type,
  such as `Equal.equal(self, other: Self)` or a constructor, cannot be called
  through `any`. The compiler reports this at the call, so a trait never
  becomes unusable with `any` just because one of its methods doesn't fit, as
  with Rust's object-safety rules.
- **Dynamic calls are verified through the trait.** Contracts and costs written
  on a trait's methods bind every `impl` and are proven for each one. The
  prover handles a call through `any` from the trait's signature alone, so
  `requires`, `ensures`, laws, costs, and capabilities all still hold. Adding a
  new `impl` checks only that `impl`, never the callers.
- **No downcasting.** An `any Handler` cannot be tested for or converted back
  to its concrete type. Code that needs to know which type it has is dealing
  with a closed set, and a sum type expresses that better, with exhaustive
  matching.

## Integers

- **`USize` is used for sizes, lengths, and indices.** A length can never be
  negative, and a bounds check is a single comparison (`index < length`).
  **`ISize` is used for offsets and the distance between two positions.**
- **Integer types never convert implicitly.**
- **Literals take their type from context, with no suffixes.** `3` can be any
  integer type, so there is one way to write it, and `let small: UInt8 = 3`
  needs no `3u8`. When nothing decides the type, it defaults to `Int64` or
  `Float64`, which keeps simple local variables free of annotations. An
  integer literal is never a float, so `1` and `1.0` always look different.
- **Negation is an operator.** A negated literal is range-checked after
  negation, so `-128` fits an `Int8`. Negating a signed value is an overflow
  proof obligation like any other arithmetic, and unsigned values cannot be
  negated at all.
- **Overflow is never silent, for every integer type.** An operation that could
  overflow must be proven safe. Otherwise the code must use an explicit
  alternative: `checked_add` (returns an `Option`), `wrapping_add`, or
  `saturating_add`.
- The standard library provides APIs that avoid index arithmetic, such as
  `items.last()`, `enumerate`, `zip`, and reverse ranges.

## No hidden failure

**Code never stops abruptly unless its signature says it can.** The only
exceptions are failures no language can rule out: running out of memory and
overflowing the stack.

Every operation that can fail creates a proof obligation. This includes integer
overflow, division by zero, indexing or slicing out of bounds, oversized
shifts, `unwrap`, and `expect`. If the compiler cannot prove the operation is
safe, it reports an error and suggests four fixes:

1. **Establish it locally**, for example with an `if` that checks the length
   first.
2. **Require it from the caller** with a `requires` clause.
3. **Use the checked version**, which returns an `Option` or `Result`, such as
   `items.get(index)` or `checked_div`.
4. **Declare `uses Panic`**, which allows a runtime failure and shows it in the
   signature.

`requires` clauses are always proven at compile time at every call site. They
never become runtime checks.

`unreachable` has only the first fix: it must be proven unreachable, or the
code does not compile. Code that says a point can't be reached must not
quietly crash when it is. To crash on purpose, call `Panic.crash(...)`, which
the signature shows.

`Panic` appears in signatures like any other capability, and every caller
inherits it. Unlike other capabilities, **a panic cannot be caught.** Code
cannot `provide` an implementation of `Panic`. `Panic.crash(message)` prints
its message and location to stderr and ends the process with a nonzero exit
code. No cleanup code runs; the operating system reclaims memory and open
files.

- **No one can see a half-finished update.** If a panic could be caught, the
  code that caught it might be left holding a value whose type invariant was
  broken partway through a change. Ending the process rules this out.
- **Robust programs prove they cannot panic instead of catching panics.** A
  server can require its request handlers to have a type without `Panic`, such
  as `fn(Request) -> Response uses Database, Log`. The compiler then guarantees
  no request can crash the process. If the whole process fails, a supervisor
  such as systemd or Kubernetes restarts it.
- **Tests cannot expect a panic.** A test that passes only when code crashes
  would treat crashing as intended behavior, which is what `Result` is for.
  Misuse that other languages test this way, such as breaking a precondition,
  cannot compile in Truss, because `requires` is proven at every call site.
  Error cases are tested as values, as in
  `assert parse(text) == Err(ParseError.Empty)`. To check that a program
  crashes on bad input, an external test runs the built program through the
  `Processes` capability and checks its exit code.
- **A failed `assert` is not a panic.** `assert` is only allowed directly in
  tests and proofs, so a failed `assert` simply ends the test as failed, like
  an early return. The prover can rely on an asserted fact for the rest of the
  test.
- **A panic ends only one worker.** The test runner keeps a pool of worker
  processes, about one per core, each running one test at a time. A panic
  ends its worker. The runner records that test as failed, with the panic's
  message and location, starts a new worker, and carries on. New processes
  start only after a crash, so code that merely could panic costs nothing
  extra. Sharing a process between tests is safe because Truss has no mutable
  globals and a test touches only what it is given, so no test can leave state
  behind for another. Running out of memory and overflowing the stack are
  handled the same way.
- **Tests have a time limit.** A test that does not finish, for example by
  reaching a loop with no `time` clause that never ends, is stopped after a
  limit set for the whole project and reported as failed.
- `main` may declare `uses Panic` when crashing is the right behavior.

Floating-point arithmetic follows IEEE 754. NaN and infinity are ordinary
values, so float operations never fail.

## Errors

Recoverable errors are values of type `Result[Value, Error]`. The `?` operator
returns early with the error. There is no exception mechanism other than
`Panic`, which is for bugs and broken assumptions, not expected errors.

**Every value must be used.** A statement whose value is not `Unit` is a
compile error, as in Zig, and `let _ = expression` discards a value on
purpose. One rule catches three kinds of mistake:

- **A dropped error.** Ignoring the `Result` of a write would hide a failure
  the signature shows. In Go, ignored errors are a well-known source of bugs.
- **A pointless call.** A pure function has no effects, so a call whose
  result is thrown away does nothing. It is always a mistake, such as
  writing `names.sorted()` when `mut names.sort()` was meant.
- **A misread line break.** A line starting with `-` begins a new statement
  (see Line breaks), which leaves an unused value.

Rust and Swift warn only for some types or functions, which needs a way to
mark them and catches only those. Truss has no warnings and no attributes,
and a rule for every value needs neither. It pushes APIs toward returning
`Unit` when the result is usually not needed: a map's `insert` returns
nothing, and `replace` returns the old value.

`?` never converts the error. It only works when the error type matches the
function's, and any conversion is written at the call with `map_error`, as in
`toml::parse(text).map_error(ConfigError.Malformed)?`.

- **No hidden code runs.** In Rust, `?` silently calls a `From`
  implementation chosen by type. That call can allocate and has costs of its
  own, and choosing it by type is a known source of confusing inference
  failures. In Truss, every conversion is a visible call, and its costs are
  proven like any other call.
- **Errors get domain names.** Because conversion is written out, each error
  type says what went wrong in the function's own terms, such as `Unreadable`
  or `Malformed`, rather than collecting every underlying error.
- **Conversion stays short.** A single-value variant can be used as a
  function, so the conversion is usually one word.
- **`Option` and `Result` don't mix implicitly.** `?` works on either, in a
  function returning the same kind. `.ok_or(error)` and `.ok()` convert between
  them.

Gleam, OCaml, and Swift's typed throws work the same way. Error unions such as
`FileError | ParseError`, which `?` could widen automatically as in Roc, could
be added later without breaking any code, if wrapper types written only to
combine two errors become common.

## Capabilities

Truss tracks side effects through capabilities. A capability is a named set of
methods for doing something outside pure computation, such as reading files or
getting the time. A function lists the capabilities it needs with `uses`, and
whoever runs the function chooses the implementation with `provide`.

- **Functions are pure unless they declare `uses`.** A pure function cannot
  read files, use the clock, or do anything else outside its inputs.
- **A dependency can only do what its signature allows.** This limits the
  damage a compromised package can do.
- **Tests are deterministic.** A test provides fake implementations of files,
  clocks, networks, and so on. A test must provide every capability it uses,
  so test results can be cached safely.
- **Tests that touch the real world say so.** A test that declares `uses` is
  external: the runner gives it real implementations of exactly those
  capabilities, as the runtime does for `main`. Its result depends on the
  world, not just the code, so it is never cached and runs every time the
  suite runs. It gets no hidden isolation; a test that wants a scratch
  directory narrows file access with `provide`, where a reader can see it.
  Failed tests are never retried, because a retry hides exactly the failures
  an external test exists to catch.
- **Implementations are ordinary types.** A capability is implemented with
  `impl`, just like a trait. An implementation with state, such as an
  in-memory file system, is a type with fields. Providing it as `mut` leaves
  the changes in the caller's variable afterward.
- **A capability method always returns to its caller.** It cannot jump out of
  the surrounding code, stop it partway through, or run it more than once. So
  calling a capability works exactly like calling a function, and compiles to
  one. Truss needs no stack unwinding and never captures "the rest of the
  computation". A value can never be left half-updated by a computation that
  was abandoned partway, because nothing can be abandoned. Early exit always
  goes through `Result` and `?`, where each step is visible.
- **Passing capabilities through is explicit.** A function that passes on
  whatever its callback needs declares a capability parameter
  (`capability Granted`). This keeps one rule everywhere: no `uses` means
  pure. Callbacks are pure by default, which is the safe choice for
  comparators and anything run in parallel.

- **`main` gets exactly what it declares.** `main` is an ordinary function
  with a fixed signature, `fn main(arguments: List[String]) -> ExitCode`, plus
  its `uses` clause. The runtime provides the real implementation of each
  capability `main` lists, and nothing else, so `main`'s signature says
  everything the program can do. Arguments are a parameter rather than a
  capability, so a test can call `main` with fake arguments and fake
  implementations like any other function. The program ends by returning an
  `ExitCode`. There is no `exit` call, since a capability method always
  returns.
- **The standard capabilities are fine-grained where trust differs.** Reading
  files is separate from writing them, and opening connections is separate
  from accepting them. A config loader with only `FileRead` cannot destroy
  anything. They are in the prelude because signatures are written with them.
- **Narrowing is ordinary code.** An implementation's methods can use
  capabilities, and a call to the capability being implemented goes to the
  next provider out. So an implementation can check each call and pass it on,
  such as one that only allows files under a directory or connections to
  certain hosts. The code being called cannot tell it has been narrowed. This
  is how handlers work in effect systems, and it needs no special mechanism.
  The standard library provides the common cases.
- **Providing a type provides every capability it implements.** If one type
  narrows both reading and writing, providing it narrows both, so one cannot
  be left open by mistake. To narrow only one, use a type that implements only
  that one.
- **Capabilities don't inherit; they layer.** A higher-level capability, such
  as `ReadDatabase`, is implemented using lower-level ones, such as
  `NetworkClient`. Code that uses it gets only its methods, and the lower-level
  power shows up where the implementation is provided, so `main`'s signature
  still lists it. A dependency can be granted `ReadDatabase` alone and never
  touch the network. Narrowing is the case where the layer implements the same
  capability it wraps. What Truss leaves out is bundling, such as
  `capability FileSystem: FileRead + FileWrite`. A bundle adds power under a
  new name, so a reviewer reading `uses FileSystem` would have to look up what
  it includes, and manifest grants would get coarser. Bundles would save some
  typing in signatures, but LLMs write most of those.
- **Signatures and narrowing do different jobs.** A signature limits which
  capabilities code has. Narrowing limits what a capability can reach, such as
  which files or hosts.

This is deliberately simpler than the algebraic effect handlers of languages
like Koka or OCaml 5, which can pause, abandon, or repeat a computation. Those
features support things like async code, generators, and backtracking. Truss
does concurrent work with blocking calls instead (see Concurrency), so it does
not need them.

### Dependencies

Signatures alone leave a gap. If your code already uses `NetworkClient` and
calls `json::parse`, a new version of `json` could start using the network and
your code would still compile, because you already had the capability to pass
along. So the package manifest grants each dependency its capabilities:

- **A dependency gets no capabilities unless granted.** It can only do pure
  computation.
- **Exceeding a grant fails the build.** The error names the dependency's
  function and the capability it used. Giving a package more power is always a
  visible change to the manifest.
- **Grants nest.** A dependency can only grant its own dependencies a subset of
  what it was granted.
- **Passing through does not count.** Running a caller's callback with the
  caller's capabilities (through a `capability Granted` parameter) is not the
  dependency doing anything itself.
- **The standard library needs no grant.** It holds the real implementations.

Because `main`'s `uses` clause is complete, a later compiler could also apply
operating system restrictions such as seccomp, Landlock, or pledge to match.
A program without network capabilities then could not open a socket even
through a compiler bug.

## Costs

Cost clauses state proven bounds on what a function consumes.

- **Costs are optional.** If present, they are checked. If absent, nothing is
  promised.
- **Bounds can be asymptotic or exact.** `time` takes Big-O bounds. Countable
  resources (`allocations`, `allocated_bytes`, `calls(...)`) also take exact
  bounds such as `== items.length()`, which can say, for example, that each item
  is processed exactly once. Concrete time bounds are not allowed because they
  cannot be proven across different machines.
- **Costs count capability calls.** `cost calls(FileRead.read) ==
  paths.length()` states a number of file reads. That number holds no matter
  which implementation performs the reads.
- **Costs compose through signatures.** A caller's cost is proven from its
  callees' cost clauses, without reading their bodies, so changing one function
  only re-checks what depends on it.

## Termination

- **A `time` clause promises the function terminates.** `cost time finite`
  promises termination without giving a bound.
- **A function without a `time` clause might not terminate.** No separate
  marker is needed.
- **Functions used in `requires`, `ensures`, laws, or proofs must have a `time`
  clause.** Otherwise the proof system would not be sound.
- A loop that runs until a capability says to stop, such as reading until the
  end of a stream, cannot be proven to terminate, because an implementation
  could keep supplying data forever. Such functions have no `time` clause.

## Verification

Everything Truss promises is proven at compile time: `requires` and `ensures`
clauses, cost clauses, type invariants, trait laws, loop invariants, and the
safety of every operation that could fail.

**Most proofs are automatic.** Each fact to be proven is sent to an automated
solver, as in Dafny, Verus, and SPARK. The programmer writes a proof only when
the solver gets stuck.

**Proofs use the language's own syntax**, in the style of Dafny:

- A `theorem` is a named fact, written like a function. Its `requires` clauses
  are its assumptions, its `ensures` clauses are its conclusions, and its body
  is the proof. Calling a theorem makes its conclusions available at that
  point. A theorem that calls itself on smaller input is a proof by induction.
- A `proof { }` block inside a function body gives the prover hints at that
  point. It is removed from the compiled program.
- `proof Trait.law for Type { ... }` helps prove a law for one implementation.

The alternative, a tactic language like Lean's, checks proofs very predictably
but is a second language to learn. Truss proofs use only calls, `match`, `if`,
and `assert`, which programmers and LLMs already know.

**Reviewers can trust proofs instead of reading them.** The machine checks
every proof, so a reviewer only needs to read the signatures and contracts.
Proof blocks are hashed separately from the code around them. Editing a proof
re-checks proofs but does not rebuild the program or rerun tests.

**Verification is modular.** The prover knows other functions only by their
signatures, except for pure functions used in specifications, such as
`is_sorted`, whose definitions are what they mean. Each proof therefore looks
at a small amount of code, which keeps proofs stable and checking O(change).

**Proof checking is deterministic.** The solver runs within fixed limits
measured in steps, never in wall-clock time, and its version is pinned as part
of the toolchain. Results are cached by hash. A proof that passes once keeps
passing, and a slow machine never fails a proof that a fast one passes.
Solver-based tools are known for proofs that break for unrelated reasons, so
Truss designs against this from the start.

**There is no `assume`.** The only gap allowed in a proof is `todo`. A
program that can reach an unfinished proof cannot be built, just like one that
can reach unfinished code. Otherwise a missing proof that an addition cannot
overflow would allow a failure the signature does not show. If a function
claims something in its signature, the claim must be proven before it ships;
a claim that is not ready can simply be left out.

**Specifications use exact integer arithmetic.** In `requires`, `ensures`,
invariants, laws, and cost clauses, integer arithmetic never overflows, so a
specification cannot itself have an overflow bug. Float arithmetic in
specifications follows IEEE 754, as in code. Exact real arithmetic would
describe results the hardware does not produce, so such contracts could never
be proven. The solver checks float contracts bit for bit, which is slow, so
they are best kept rare.

## Unfinished code

Truss supports designing a package's API before implementing it. Signatures,
types, and contracts can be written first, with `todo` in place of bodies and
type definitions.

- **Unfinished code is checked as far as it can be.** Callers are type-checked
  and proved against the signatures of unfinished functions, including their
  `requires`, `ensures`, and cost clauses. A caller's contracts can be fully
  proved before the functions it calls exist.
- **Unfinished code is never shipped.** A `todo` cannot simply panic when
  reached, because that would be a failure hidden from the signature. Instead,
  the compiler tracks holes through the dependency graph, and `truss build`
  refuses any program whose `main` can reach one, whether it is in code or in
  a proof.
- **Tests run anyway.** A test that reaches a `todo` stops its worker process,
  as a panic does, and is reported as incomplete. Tests can
  be written before the code they test.
- **The tools list every hole and what it blocks:** the tests, proofs, and
  builds waiting on it. Each hole comes with its expected type and the names
  in scope, which makes it a self-contained task for a person or an agent, and
  lets several agents fill holes in parallel.

## Debug output

`echo expr` lets pure code show a value without declaring a capability. It
follows Gleam's `echo` and Rust's `dbg!`: it records the value with its
source location and passes the value through unchanged.

- **It changes nothing the compiler reasons about.** Types, proofs, and cost
  clauses treat `echo expr` as `expr`, so adding one never changes whether
  code compiles or verifies.
- **It cannot ship.** Like Elm's `Debug` and Gleam's `echo`, it is for
  development only: builds refuse programs that can reach one, and packages
  that contain one cannot be published. That is what makes it safe to skip
  `uses` here.
- **It works well with cached tests.** Adding an `echo` changes the function's
  hash, so the affected tests re-run and show the output, instead of being
  served from the cache. Removing it restores the old hash, and the cached
  results apply again. Tests are deterministic, so a re-run takes exactly the
  same path as the run being investigated.
- **Its output stays readable.** It is attached to each test's report and
  grouped by parallel branch or task, never interleaved. The tools shorten
  very large values.
- **It is a whole word.** `debug` and `trace` were passed over because they are
  common names for variables and fields.

## Loops

Loops give the prover facts for free, so most loops need no annotations:

- `for i in 0..items.length()` proves `i < items.length()`, so `items[i]` needs no
  check.
- A `for` over a collection or range runs exactly once per element. This is
  how a clause like `cost calls(visit) == items.length()` gets proven.
- A `for` over a collection or range always terminates.

A `while` loop in a function with a `time` clause must be proven to terminate.
The compiler handles simple cases itself. Otherwise the loop states a
`decreases` clause. Loop `invariant` clauses supply facts the prover cannot
work out alone. These clauses sit on the loop itself, so the reasoning stays
next to the code it explains.

There are no labeled breaks for now. They may be added later if real code turns
out to need them.

## Parallelism

Parallelism means using several cores to finish a computation sooner. In
Truss it is deterministic: a `parallel` block or `parallel for` loop always
gives the same result as running its parts one after another.

- **No data races, by the same rule as calls.** Truss has no aliasing, and a
  place passed as `mut` can't be used by anything else at the same time. That
  rule is what rejects `swap(mut first, second: mut first)`. Applying it
  across branches means branches may share what they read but never what they
  change.
- **No capabilities inside.** A capability implementation can hold state, so
  two branches calling it would race, and the order of their calls would vary
  from run to run. Leaving capabilities out keeps the result fixed, and the
  only exception is `Panic`.
- **No `uses` needed.** A function that uses `parallel` is still pure, and
  tests that run it can still be cached.
- **Proofs and costs work as for sequential code.** Branches are disjoint, so
  their order can't matter, and the prover treats them as running in order.
  `time` measures total work, so a `parallel` block costs the sum of its
  branches. A separate measure for elapsed time on many cores may be added
  later.
- **Panics end the program, as anywhere else.** If more than one branch could
  panic, which message is printed may vary.
- **Simple to compile.** A compiler may run `parallel` code sequentially and
  still be correct, which is what stage0 can do. Later compilers can use a
  thread pool built on the threads in libc.
- **Early exit is not allowed.** Leaving with `return` or `?` would raise the
  question of what happens to branches that are still running. Branches return
  values instead, and the code after the block decides what to do with them.

The design follows Rust's scoped threads and rayon, Swift's `async let`, and
Hylo, which also uses mutable value semantics.

## Concurrency

Concurrency means handling many things that spend their time waiting, such as a
server's connections. It is nondeterministic by nature, since requests can
arrive in any order, so it goes through capabilities. The direction is
decided. The exact syntax for task groups and channels is not yet:

- **Blocking calls, no async.** Code waits by calling a capability method that
  returns when the result is ready, as in Go. There is no `async` or `await`,
  so functions are not split into two kinds that can't easily call each other.
  This fits the rule that a capability method always returns.
- **A `Tasks` capability starts concurrent tasks.** In stage0 its real
  implementation can use operating system threads. A later one can use
  lightweight tasks without any code changing, because code only sees the
  capability.
- **A task gets its data as an owned argument.** `spawn` takes a function and
  a value to hand over to it, as in `spawn(handle, input: own connection)`,
  the way pthreads and Zig pass a function and its argument. So no closure
  ever needs to own what it captures. The function may still read data from
  around its task group, because tasks cannot outlive the group.
- **Tests stay deterministic.** A test provides a `Tasks` implementation that
  runs tasks in an order chosen by a seed. A race then becomes a repeatable
  test failure instead of a rare, flaky one. This is how FoundationDB tests its
  database.
- **Tasks live inside a task group.** A task cannot outlive the group that
  started it, as with Trio's nurseries and Swift's task groups. A task can
  therefore read data from the code around the group without lifetimes.
- **No shared mutable memory.** User code has no mutexes or atomics. A task can
  be given owned data. When several tasks need the same state, one task owns it
  and the others send it owned messages through channels. A mutex could be
  added later as a separate, clearly marked capability if performance requires
  it.
- **Tasks get capabilities through their function type**, the same way
  callbacks do. Calls into one implementation never overlap, because the
  runtime has them take turns. A stateful fake in a test stays consistent
  without any locking in user code.
- **Waiting may never end.** A function that waits on a channel cannot be
  proven to terminate, so it has no `time` clause.

## Collections

- **Each collection has one way to be written.** `[a, b, c]` is always a
  `List`, and `[]` is the empty list, so there is no `List.new()` or
  `List.of(...)`. Maps use Swift's `[key: value]`, with `[:]` for the empty
  map; `{ }` already means blocks. Sets have no literal, because
  making `[...]` mean a `Set` from context would make a literal's meaning
  depend on its surroundings. `Set.from([...])` says it plainly.
- **Literal allocation is counted.** A non-empty list or map literal in a
  function body counts as one allocation in `cost` clauses, and an empty one
  as none. The compiler may keep such literals in static memory, but cost
  clauses don't depend on that. Constants and defaults are different: they
  always live in static memory, so reading one costs nothing.
- **Duplicate keys in a map literal are a proof obligation.** Letting the last
  one win would silently hide a mistake.
- **`Map` and `Set` iterate in insertion order,** like Python's `dict` and
  JavaScript's `Map`. Iteration order never varies from run to run, so tests
  stay deterministic and their results can be cached.
- **Indexing follows the no-hidden-failure rule.** `items[i]` and `ports[name]`
  must be proven valid, and `get` returns an `Option` when they can't be.
  Assigning to a map key inserts or replaces, so it cannot fail.
- **Open-ended ranges only appear in brackets.** `items[2..]` is useful, but
  allowing `0..` elsewhere would give `for` loops with no end, and every `for`
  loop is guaranteed to terminate.
- **Strings cannot be indexed.** A UTF-8 string's byte `i` and character `i`
  are different things, so code says which it means with `bytes()` or
  `characters()`, as in Rust and Swift.
- **User collections can support `[]`.** The `Index` trait's method carries a
  `requires`, so a user's `Grid` gets the same proof rules as a `List`.

## The standard library and prelude

The standard library's root module is `standard`. Truss aims to include
enough in it, plus a set of approved packages, that most programs need few
outside dependencies. Every dependency is a possible target for a supply-chain
attack.

A small prelude of names that nearly every program needs (built-in types,
`Option`, `Result`, the core collections and traits, and the standard
capabilities) is in scope
in every file. The prelude is the same everywhere: projects cannot define their
own, and code cannot hide a prelude name with its own definition. A reader or
an LLM can therefore rely on `List` or `Result` meaning the same thing in every
file of every project.

## Visibility

- **Private (the default):** visible only within the file.
- **`internal`:** visible anywhere in the package.
- **`public`:** visible to other packages.

Defaulting to private makes keeping code modular the easiest option.

A `public opaque type` exposes its name but not its contents. Only code in its
package can read, build, update, or match on it. Visibility is set for the type
as a whole, never per field. Truss uses opaque types for three things:

- **Control over where values come from.** Some types are only safe if outside
  code cannot build them, such as `SqlQuery`, whose text must come from source
  literals, or tokens that act as capabilities. No property of the value itself
  can express this.
- **Freedom to change a type's internals.** Code in other packages cannot
  depend on the fields, so a package can change how a type is stored without
  breaking anyone.
- **Protecting low-level internals,** such as the pointer, length, and capacity
  inside `List`.

The access boundary is the package rather than the file, because a type's
methods can live in any file of its package. Public types expose their fields
unless marked `opaque`, following Gleam. This is visible in review, because
the fields are written right in the type's public declaration.

## Strings

Truss has two string forms: ordinary strings (`"..."`), which have escapes and
fit on one line, and raw strings (`"""..."""`), which have no escapes and may
span several lines.

- **Raw strings take text exactly as written.** Regular expressions and
  Windows paths keep their backslashes, without the `\\d` doubling that causes
  bugs in other languages. Multi-line text uses real line breaks instead of
  `\n`.
- **The closing `"""` sets the indentation** to remove, as in Swift, Java, and
  C#. A raw string can be indented to match the code around it without that
  indentation ending up in the text. As in Swift and C#, every line must start
  with exactly that whitespace, so mixed tabs and spaces are an error rather
  than a silent change to the text. Unlike Java, trailing whitespace is kept:
  raw strings have no escapes, so whitespace that was stripped could not be
  written back.
- **Interpolation is `${expr}` in both forms.** Languages that mark
  interpolation with a single `{` (Python, C#, Rust) or `$` (Kotlin) make
  JSON, regular expressions, and shell text painful, because those characters
  are common in such text and must be escaped. C# and Kotlin later added rules
  that count delimiters to work around this. JavaScript's `${`, by contrast,
  almost never appears in ordinary text, so lone braces and dollar signs stay
  literal and no workaround is needed. Truss's tagged templates come from
  JavaScript too, so the syntax is familiar.
- **Strings have no concatenation operator.** Interpolation and methods such
  as `join` and `push` are the one way to build text. `+` stays numeric, and
  each allocation shows as an interpolation or a method call rather than
  hiding in an operator. Adjacent literals do not join either, as they do in C
  and Python, where a missing comma in `["a" "b", "c"]` silently merges two
  elements.
- **Raw strings have no escapes at all.** When text contains `${` itself, as
  shell scripts and JavaScript do, the string is opened with more `$`s
  (`$$"""`), and only that many `$`s start an interpolation. This follows C#
  11 and Kotlin 2.2, which both moved to it from escape sequences, and it is
  the same fix Truss already uses for text containing `"""`: make the
  delimiter longer. A fixed escape such as Terraform's `$${` would make one
  sequence special in an otherwise raw string, and leave no simple way to
  write a `$` right before an interpolation, as in a price.
- **Line endings are always `\n`,** so a string means the same thing, and
  hashes the same, whatever line endings the source file uses.
- **A `Character` is a Unicode scalar value,** as in Rust. It has a fixed
  size, so it copies implicitly, and what counts as one never changes between
  Unicode versions, so hashes stay stable. A grapheme cluster, which is what a
  reader sees as one character, has no fixed size and its boundaries change as
  Unicode adds rules, so `graphemes()` returns slices of the string instead.
- **Characters and bytes are tagged templates,** as in `Character"é"` and
  `UInt8"a"`, not a separate literal such as `'a'`. The tag's `requires`
  proves at compile time that the text is exactly one character, so this
  needs no new lexer rule and no second set of escapes.

## Tagged templates

A tagged template such as `SqlQuery"... ${user_id}"` keeps its literal text and its
interpolated values separate. That makes injection attacks impossible by
construction:

1. **Only the compiler can create literal text segments.** Their type,
   `Literal`, can only be made from a string literal in source code, so text
   produced at runtime can never pass as trusted query text.
2. **Each interpolated value is converted to the tag's value type.** For SQL
   that type is `SqlParameter`. A value with no meaning in SQL is a type error.
3. **APIs accept the template's result type, not `String`.** A database query
   function takes a `SqlQuery`, so an interpolated plain string will not
   compile. `SqlQuery` is an opaque type, so outside code cannot build one by
   hand.
4. **Unsafe cases are explicit.** Pieces that cannot be parameters, such as
   table names, use their own validated types (for example `SqlIdentifier`).
   Running raw text requires a clearly named function such as
   `SqlQuery.from_trusted_text`, which is easy to find in review.

The same mechanism works for HTML, shell commands, regular expressions, and
similar languages.

**The tag is a type.** `SqlQuery"..."` builds a `SqlQuery` through the
`FromTemplate` trait, so the tag names exactly what you get back, and a plain
`"..."` is simply the `String` tag. A lowercase tag function would not fit the
prelude, which holds only `UpperCamelCase` names, and would read less clearly
from another module.

**Malformed literal text is a compile error.** A tag states what valid text
looks like with `requires`, such as `is_valid_pattern(template.literals)`. The
literal text is a constant, so the compiler proves the clause by running the
check on it. This is possible because functions used in specifications are pure
and must terminate. The check runs with the same step limits and caching as
other proofs. This gives:

- **Mistakes found at build time.** `Regex"[a-z"` fails with the tag's own
  error message, instead of failing in production.
- **No failure at runtime.** Once the literal text is known to be valid,
  building the value cannot fail, so templates need no `?` and no `Panic`.
- **No new mechanism.** It reuses `requires`, pure functions, and termination.
  It is a small, controlled version of Zig's `comptime`.

A check cannot look at anything outside the code, such as a live database
schema the way Rust's sqlx does, because builds have no capabilities. A schema
written as a constant in the code could be checked the same way later.

## Naming

Names in Truss code, including the standard library, use whole words, with no
abbreviations, and single letters only for loop indices such as `i` and `j`.
Code is read and reviewed far more often than it is written,
and with LLMs writing much of it, longer names cost almost nothing to type.
This is a convention, not a compiler rule. The standard library and style
guides set the example, because a hard rule would get in the way of the
reasonable exceptions.

**A name always refers to one thing in a given scope.** No name can hide
another: not a prelude name, not a definition in the same file, and not a
variable from an enclosing scope. Readers never have to check whether a
familiar name has been replaced by a local one.

**Keywords are reserved, with a few exceptions.** Reserved keywords let the
lexer tell a keyword from a name on its own, which keeps the grammar simple
and lets the lexer alone decide whether a newline ends a statement. The
exceptions are words that are both common names and needed only in one
narrow place: `result` in `ensures`, `old` in specifications, and `time`,
`allocations`, `allocated_bytes`, `calls`, and `finite` in `cost` clauses.
Reserving those would ban names like `result` and `time` from all code to
serve a few specifications. Words that other languages use as keywords, such
as `loop`, `async`, and `where`, are reserved now, so that adding one later
breaks no code and borrowed code gets a clear error.

**Names can use any script.** The whole-words rule asks for names a reader
understands, and for many teams those are words in their own language. The
danger is that a malicious change could add a name that looks like an
existing one but is spelled with different characters, which matters for a
language built for supply-chain safety. So the protections are errors, not
warnings: names must be in Normalization Form C, a name cannot mix Latin with
Cyrillic or Greek or with more than one other script, and two names in a
package that Unicode lists as confusable cannot both be visible. Scripts
without case count as lowercase, as in Go and Haskell, so the parser's rule
that case tells a type from a value still holds. Keywords and the standard
library stay ASCII so that every program can be read with them.

**Constants are values, so they are `lower_snake_case`:** `math::pi`,
`UInt8.maximum`, `Instant.epoch`. A separate case for constants, such as
`MAX_SIZE`, would give the lexer a third kind of name, and an
`UpperCamelCase` constant could not be told apart from a type or
constructor. The cost is that a constant cannot be used as a pattern, since a
`lower_snake_case` name in a pattern binds a variable. A guard or `==` covers
that case.

**Imports bring in modules, not individual names.** After
`use standard::file_system`, code writes `file_system::read_text(path)`. Every
name that is not local or from the prelude shows where it comes from, right
where it is used. Two modules can both define `Path` without a clash, so Truss
needs no import aliases. Aliases would let the same thing go by different
names in different files, which makes code harder to search, rename, and
predict.

**Modules have their own namespace, marked by `::`.** In Go and Python a
module name is an ordinary name, so a variable called `url` or `json` hides
the module, a well-known source of bugs. With our no-hiding rule it would be
worse: those natural names would be forbidden, and adding an import would
break unrelated code in the same file. Because modules are only ever written
before `::`, they never clash with variables, and `.` always means a type or a
value. Rust uses `::` the same way.

**The prelude holds only `UpperCamelCase` names.** Case is enforced, so the
prelude can never clash with a variable or function name. Things other
languages make global functions have other homes: `Console.print_line`,
methods such as `items.length()`, `Ordered.max(left, right)`, and keywords
such as `todo` and `unreachable`. Adding a name to the prelude can still clash
with a user's type, so the prelude only changes with a new language version,
which comes with an automatic rename for such clashes.

**Variants live under their type.** In expressions a variant is written
`LogLevel.Warning`, like the constructor `LogLevel.new`, so the name shows its
type and two types can share a variant name. Rust started with variants in the
module and moved them under the type because of such clashes. In patterns the
variant is written bare and looked up in the type of the value being matched,
just as a method is looked up in the type of its receiver. The value is right
there, so the reader isn't left guessing. The prelude's `Some`, `None`, `Ok`,
and `Err` are bare everywhere.
