# Truss Design Decisions

This document gives the reasons for Truss's design: why the language has its
rules, and the choices of the toolchain and the standard library that the
language depends on. [SPECIFICATION.md](SPECIFICATION.md) states the rules
of the language, and [PACKAGES.md](PACKAGES.md) the rules of packages; this
document states a rule only as far as its reason needs. Another language is
named only where its experience is the reason for a choice. For the goals
behind these decisions, see [GOALS.md](GOALS.md).

## Source code

- **Text files are the source of truth.** Programmers and tools edit ordinary
  files.
- **A change costs in proportion to its size.** GOALS.md asks that building,
  testing, and proving cost O(change), not O(project). The rules in this
  section make that possible. [DATABASE.md](DATABASE.md) describes how the
  toolchain caches results and finds a change's dependents.
- **Each top-level definition stands on its own.** A definition's identity
  does not depend on its position in its file, the definitions around it, or
  its layout, so reformatting a file or moving a definition within it
  changes nothing that depends on it. See
  [Definition identity](#definition-identity).
- **Code refers to other code by name, never by its content.** Unison refers
  to code by hash, so changing one body changes the hash of everything that
  reaches it. A Truss definition names its dependencies by module path and
  name, so changing a body changes nothing about its dependents.
- **A function's signature and body are apart.** Type checking and proofs in
  callers depend only on the signature, so changing a body, such as filling
  in a `todo`, re-checks no callers. The signature is itself two parts: its
  interface, which callers' types depend on, and its contract, which only
  callers' proofs depend on. Strengthening an `ensures` re-proves callers but
  type-checks none of them again.
- **A body is part of its package's interface only when the function is
  `transparent`.** A body that other packages' proofs rely on would
  otherwise be part of the interface without being in the signature, and a
  change to it could break their proofs with no change that a reader of
  signatures sees. Verus makes the same split with `open` and `closed`. A
  public contract and a `transparent` body name only public definitions,
  because the contract of a function that other packages cannot see is not
  compared between releases. A `transparent` body may read a hidden field,
  since a change to the field is a change to the body, which is compared.
- **The order of a type's fields is not part of its shape.** The compiler
  chooses the layout, and a record with more than one field is built with
  named arguments, so field order is observable only to a derived `Ordered`.
- **A parameter's default is apart from the signature.** The signature
  records only that the parameter has one, so changing a default
  re-type-checks nothing. Callers that leave the argument out depend on the
  default, so their proofs and tests are checked again. The function fills
  the default in, so only the function is compiled again.
- **Each derived implementation is its own definition,** made from the trait,
  the type's shape, and the compiler's rule for deriving, and never stored.
  Adding a derive changes nothing that exists, and changing a field
  re-checks only code that compares, hashes, or orders the type.
- **A name is looked up in few places.** A definition depends on lookups
  keyed by scope and name, such as the members of `List` named `length`, and
  a lookup that found nothing is depended on too. When a definition is added,
  removed, or renamed, only the lookups with its scope and name are made
  again. Swift's incremental builds keyed such lookups by name alone, and
  rebuilt far too much. Truss's rules keep each lookup to a few places:
  methods live with their type, an `impl` lives with its trait, its type, or
  a type its trait's arguments name, and an unqualified constant comes only
  from the same file.
- **Renaming or moving a definition redoes little.** Its users' types are
  checked again, which is cheap. Their proofs, test results, and compiled
  code are keyed by content, not by name, so they are found already done.
- **Positions are relative to their definition.** Panics, `echo`, failed
  asserts, and debug information record positions within their definition,
  and a table built at the end of the build turns them into a file and line.
  Otherwise adding a line at the top of a file would change the output of
  every definition below it.
- **Development builds do not inline across the definitions being worked
  on.** Inlining makes a caller's code depend on its callee's body.
  Development builds inline only from the standard library and from registry
  packages, whose bodies change only with a new toolchain or lock file, so
  inlining never widens a rebuild while editing. Release builds inline
  across everything.
- **Upgrading a dependency costs O(its diff).** A path holds no version, so a
  new version of a package is an edit to code the project does not own, and
  is followed like any edit.
- **A new compiler release redoes only the work its changes affect.** Each
  stage of the compiler is versioned on its own: the parser, the type
  checker, the prover with its pinned solver, code generation, and each rule
  for deriving. A release that changes code generation leaves every proof
  valid.

### Definition identity

A definition is its kind, its structure, the names it resolves to, its local
variable names, its literal values, and the order of clauses within each
kind. A change to any of those is a change to the definition, and nothing
else is.

- **Not part of it:** layout, the order between kinds of clause, its
  position in the file, and how a literal is written: `0xFF` and `255` are
  the same. The file keeps each literal's spelling, so `truss fmt` can print
  it back.
- **The order of clauses of one kind is part of it,** because each
  `requires` may rely on the ones before it.
- **Field order is part of it only for types with a derived `Ordered`.**
- **Local names are part of it.** Truss shows local names in diagnostics and
  `echo` output, and a result that ignored them would show an old name.
  Renaming a local re-checks one body.

### Invisible characters

The invisible characters behind known attacks are an error anywhere in a
source file, including inside strings. An escape serves every other use.

- **Bidirectional controls** can make code display differently from how it
  compiles, the "Trojan Source" attack (CVE-2021-42574). Truss has no
  comments, so string literals are where such an attack would hide.
- **Control characters** such as escape and backspace can make a terminal
  hide or rewrite lines in `cat` or `git diff`.
- **Other invisible characters**, such as zero-width spaces and Unicode tag
  characters, can make two strings look the same, or hide text from a human
  reviewer that an LLM still reads, which is a known attack on LLM agents.

The zero-width joiner, the zero-width non-joiner, and the variation selectors
stay legal, because emoji and scripts such as Persian need them. This stops
the known attacks, not every way of hiding data: a run of variation
selectors can still carry hidden bytes in a string. Closing that would need
rules for where each character may appear in every script, so it is left to
review tools.

## No comments

Comments go stale without the compiler noticing, and LLMs fill code with
comments that repeat it. Truss moves their usual content into forms the
compiler checks:

- **Names** describe each thing, and the naming rule makes them descriptive.
- **Signatures, `requires`, and `ensures`** state a function's behavior.
- **Invariants and laws** state the facts that always hold.
- **Cost clauses** say how expensive a call is.
- **Tests** show how code is used, and their names record requirements.

A reason that would go in a comment belongs in a name, such as
`treat_missing_account_as_empty`. Writing about a whole package lives in
Markdown files beside the code.

## Line breaks

A line break ends a statement when the token before it can end one and the
token after it can begin one, which is Scala's rule. Go's rule looks only at
the token before.

- **It fits how Truss code is laid out.** Clauses sit on the lines after a
  signature, variants start with `|`, and the body's `{` follows the
  clauses. Go's rule would forbid all of these.
- **It follows from one principle.** The tokens that continue a line are
  exactly those that cannot begin a statement, so the list falls out of the
  grammar, and a closing `}` needs no special case.
- **It allows method chains** with each `.` at the start of a line, which
  LLMs write by habit.
- **It never guesses.** JavaScript continues a line whenever the next one
  could continue it, so a line starting with `(` silently calls the line
  before. The cases Truss reads as two statements, such as a line starting
  with `-`, leave an unused value, which is an error.
- **`match` arms are separated by line breaks, like statements,** rather than
  by commas, which Rust makes optional after a block arm, giving two
  spellings. The cost is that a `match` cannot fit on one line; `is` covers
  most uses of one-line matches.
- **The lexer decides alone,** because keywords are reserved. The rule needs
  no type information, no parser state, and no indentation.

## Rejected sequences

LLMs have seen far more Rust, TypeScript, Python, Go, and C than Truss, and
write those languages' syntax by habit.

- **Foreign sequences are rejected, not reinterpreted.** `--x` could mean
  `-(-x)`, and `//` could be two divisions; both are errors instead, so a
  habit never compiles to something unintended. This also keeps the
  sequences free: if Truss adds comments, `//` can mean one without changing
  existing code.
- **Nothing foreign is accepted and cleaned up later.** Ignoring a stray `;`
  would give each construct two spellings, and files would differ until
  they were formatted.

## Types and inference

- **Signatures are written out in full,** so a signature can be read on its
  own.
- **Constants are evaluated when compiling, from literals only.** Constants
  appear in types, as in `Array[UInt8, digest_size]`, and keeping them free
  of calls means type checking never waits for code to run. Rust started
  with similarly limited constants and widened them without breaking code,
  and Truss can do the same.
- **Code run while compiling is compiled code.** Tagged-template checks and
  the tables of constant maps run Truss code while compiling. It is compiled
  and run the way tests are, rather than by a separate interpreter, so there
  is one meaning of Truss code to keep correct, and results match the
  compiled program exactly, including the width of `USize`. Such code only
  discharges proofs and produces static data, so it never feeds type
  checking.
- **Explicit type arguments use the same brackets as indexing.** Rust needs
  `parse::<i64>` because `<` is also less-than; brackets have no such clash.
  The parser builds the same tree for both and name resolution decides,
  which the no-shadowing rule keeps simple. Two costs follow: a highlighter
  that works from the text alone can mistake `items[Color.Red]` for a type
  argument, so exact highlighting comes from the language server, and
  diagnostics about `f[X]` must say which reading applied.
- **Each statement settles its own types.** Rust, OCaml, and Haskell infer
  across a whole body, so a variable's type can come from a use many lines
  later, and an error can show up far from its cause. In Truss a variable's
  type is visible on its own line, to a reader, an LLM, and the language
  server, and checking stays local and fast. A local declared from literals
  alone is the exception (see [Integers](#integers)). The cost is an annotation where
  a statement alone cannot decide, as in `var names: List[String] = []`.
- **Generic code is compiled once for each set of type arguments,** so
  generics cost nothing at run time. This rules out polymorphic recursion,
  which Truss reports while type checking, as Go does, rather than failing
  while compiling copies, as Rust does.

### Single-field records

Values that mean different things get their own types with a record of one
field, such as `type UserId(number: UInt64)`, rather than a wrapper syntax:

- **No new concept.** Construction, field access, `with`, invariants, and
  `opaque` work as for any record.
- **The author names the field.** `port.number` names its contents, which a
  built-in name such as `.value` would not.
- **It costs nothing at run time.**
- **Operations are not inherited,** because many would make no sense: adding
  two `UserId`s is meaningless.

Truss has no type aliases either, so a type name always means one type.

### No tuples

- **Every value has a name.** A tuple element read by position says nothing
  about its meaning.
- **Values cannot be swapped by accident.** Nothing stops a caller from
  reading a width and a height from a pair in the wrong order.
- **Signatures say more.** `-> Option[Extremes]` explains itself, and
  `-> Option[(Int64, Int64)]` does not.

Record patterns leave out the type name, so taking a record apart stays
short: `for (index, element) in scores.enumerate()`. That pattern matches
fields by name, so `(i, item)` is an error that names the real fields rather
than a silent positional match. If small groupings turn out too verbose,
anonymous records with named fields could be added later.

### Building values and calling functions

One set of rules covers calls, construction, and patterns: a record is
declared the way parameters are, built the way a function is called, and
matched in the same shape.

- **Arguments after the first are named.** Two arguments of one type can be
  swapped by accident: Google found swapped arguments to be a recurring bug
  in production Java ("Detecting Argument Selection Defects", OOPSLA 2017).
  A single-field record helps only when the types differ; labels also tell
  `source: Path` from `destination: Path`.
- **The first argument may be bare.** A function's name usually identifies
  its first argument, as in `sqrt(area)`, so a label would repeat it.
- **A variable with the parameter's name needs no label.** Labels then cost
  nothing when names agree, the common case, and must be written exactly
  when names disagree, when swapping is possible. A bare name goes to the
  parameter it names wherever it appears, so `copy(destination, source)` is
  reported as out of order rather than swapping the two.
- **No declaration decides labeling.** Swift lets each parameter opt out of
  its label, so how to call a function depends on its author's choices. In
  Truss the rule is the same for every function, and parameter names are
  part of the API.
- **Calling through a function value is positional.** Swift removed labels
  from function types (SE-0111) because they created confusing conversions
  between otherwise identical types.
- **Records differ in two ways.** Field order has no meaning, so a bare first
  argument would make it part of the record's API, and only a record with
  one field takes a bare value.
- **`{` always starts a block in an expression.** Building records with
  braces makes `if kind == Kind.Unit { x }` ambiguous between a record and a
  block, which Rust and Go resolve with a special rule. With parentheses the
  question never comes up.

#### Defaults

- **Adding a parameter is a change in one place.** Without defaults, every
  caller must be edited, which in a codebase shared by many agents is a large
  diff that collides with their work.
- **Without overloading, defaults are the alternative to near-duplicates,**
  such as Rust's `sort`, `sort_by`, and `sort_by_key`, or option structs and
  builder types.
- **A default is a constant,** so it is the same at every call, hides no
  effect, and costs as much as reading a constant.
- **Defaults are applied by the function, not copied into each caller.** C#
  copies them into callers, which keep an old default after a library
  changes it.

### Matching several values

`match state, event` matches two values without making a tuple. State
machines are the main reason to match on tuples, and this covers them.
Patterns correspond to values by position only within one `match`, where the
values and the arms are on the screen together.

### Testing patterns

- **`value is pattern` is a `Bool`.** One construct covers tests, loops,
  conditions in specifications, and combinations with other conditions,
  where Rust needed three forms, `if let`, `while let`, and let-chains. A
  name bound by `is` can be used only where the test is known to be true.
- **`let ... else` leaves early when a pattern does not match.** C# instead
  keeps a name bound by `is` usable after `if (!(v is T x)) return;`, which
  lets a name outlive the `if` that introduced it. In Truss a name's scope
  follows blocks.
- **Float literals are not patterns.** `-0.0 == 0.0`, so a pattern `0.0`
  would quietly match both. A guard says so.

### Type invariants

- **Facts move from signatures into types.** Every `SortedList` is sorted, so
  functions that take one need no `requires is_sorted(...)`, and a fact
  carried by a type cannot be forgotten at a call.
- **An invariant belongs to the whole type, never to one variant.** It can
  then state facts about the whole value, such as a tree being balanced, and
  a trailing clause belongs to one thing only. A condition on one variant is
  a `match`, or a field whose type carries it.
- **An invariant holds wherever other code could see the value.** Between
  those points, a body may break it, as `SortedList.insert` does to append
  and then move an element. Nothing else can see a value in the middle of a
  change, panics end the program, and capability calls always return, so no
  half-updated value is ever observed.
- **A private method that takes `mut self` is a step of an update,** so
  `insert` can call a helper while the list is half sorted. The helper states
  its needs with `requires` and `ensures`. Ada's type invariants bind only
  the subprograms that code outside the package can call; Truss draws the
  line narrower, at methods private to a file, and only for `self`.
- **Functions called in an invariant are pure and terminate.** A function
  that might not return has no result to reason about, and allowing one would
  let the prover derive false statements.

Invariants and opaque types solve different problems. An invariant protects
facts about a value's contents, so a type with one can expose its fields. An
opaque type controls where values come from and keeps the representation
private.

## Memory

Truss uses mutable value semantics: every variable holds its own value, and
two variables never refer to the same changeable data. There is no garbage
collector and no runtime beyond libc.

- **Operating-system resources are released like memory,** so `?` and
  `return` need no cleanup code. Releasing one never runs Truss code: only
  the standard library's real capability implementations create handles,
  since there is no foreign code.
- **Buffered data is never lost silently.** Closing a file that was only
  read loses nothing, but flushing a buffered writer can fail, and losing its
  data would go unnoticed, which is how Rust's `BufWriter` loses writes when
  it is dropped. So a writer is only lent, inside a scope, and user code
  never owns one it could drop unfinished. Linear types could instead let a
  writer be owned and stored, but every `?` while one is open would drop it,
  and generic code would need to say which type parameters it never drops.
- **There is no mutable global state.** Everything that changes lives in a
  variable, a parameter, or a capability implementation, so all the state a
  function can touch is visible in its signature, and many tests can share
  one process.
- **The call repeats `mut` and `own`,** so the effect on each argument is
  visible where the call is made, and searching for `mut scores` finds every
  place `scores` can change. Keywords avoid `&`, which means a read-only
  reference in Rust and an address in C. A temporary has no other owner, so
  it needs no mark.
- **A mark covers the longest place it can,** so `mut config.servers.sort()`
  leaves the other fields of `config` usable at the same time.
- **A field can be moved out on its own.** Otherwise taking one field from a
  record would mean copying it or moving the whole record.
- **Recursive types say where they allocate.** A variant that holds its own
  type would be infinitely large in place, so it is marked `indirect`, and
  the allocation is written where the type is declared. Rust says the same
  with `Box`, which every pattern then reaches through; the mark keeps
  patterns unchanged.
- **Implicit copies never allocate.** A `Plain` value copies as a plain
  memory copy. Every other type needs `copy()`, so the cost of copying shows
  in the code.
- **Handles cannot be copied.** Copying one would duplicate an
  operating-system handle, which can fail, and `copy()` cannot fail.
- **Generic code makes its copies explicit** with a `Copyable` bound, so a
  plain `[Element]` accepts every type, handles included. The name avoids
  Rust's `Copy`, which means implicit, where Truss's `copy()` is explicit.
- **Opaque types declare whether they copy.** Inferring it from hidden fields
  would let other packages depend on fields they cannot see: adding a
  `String` field would break a package that relied on implicit copies. Other
  types show their fields, so a change to them is visibly a change to the
  API, and their copying stays inferred.

### Views

A read-only name can refer to the original value without lifetimes because
views are second-class, as in Hylo:

- **The original is frozen while a view is in use.** The name is read-only
  either way, so this changes whether a copy happens, never the semantics.
- **Being a view is a property of a type,** derived from its fields like
  copying, so nothing is declared.
- **Views never outlive the function that made them.** Putting a view in a
  record makes the record a view, so a view can never be stored past its
  function. Generic code that keeps a value asks for `Storable`. An
  `any Trait` hides its type, so it is a view unless `Trait` requires
  `Storable`.
- **A call's result views only places its arguments view.** The caller treats
  the result as viewing every read-only and view argument, so it needs no
  annotation. Rust names which input a result borrows from with lifetimes;
  Truss's rule is coarser but needs none, and `Plain` arguments such as
  indexes lend nothing, so it rarely holds more than it must. A rule that
  only views of `self` can be returned would not be enough: `unwrap_or`
  returns a value of its parameter's type, which is a view whenever the
  `Option` holds one.
- **`mut` access is never stored,** so there is no mutable reference to track
  across statements.
- **The compiler checks each function on its own,** from its body and the
  signatures it calls, which keeps checking fast and incremental.

**Constants are read-only places.** An owned value from a constant is made
with `copy()`, so its allocation is written and counted. Swift instead copies
on the first write to any collection, so every in-place change, such as
`items[i] = x`, would check for static memory and might allocate, and no
`cost allocations == 0` could be proven for code that changes a collection
it was given. A string literal is the exception that costs nothing: only
methods that write bytes change a `String`, and those may allocate anyway.

### Lending and yielding methods

A method gives its caller parts of `self` without returning a stored
reference, which would need lifetimes. `lends` gives one part, exactly once,
as Swift's `_read` and `_modify` accessors do; it is how `items[i]` works.
`yields` gives any number of parts, as a generator does; it is how `for`
loops and cursors work.

- **The signature says which.** A lending method is proven on the promise
  that it continues after its `yield`, while a loop may stop at any `yield`.
  If the body decided, a body edit could change callers' meaning, and a
  caller could break a lending method's proof by looping over it.
- **User collections are not second-class.** `[]` and `for` work through
  `Index` and `each`, so a user's `Grid` gets the same syntax and proof rules
  as a `List`.
- **A lent part need not be stored in `self`.** A collection that packs its
  elements, such as a set of bits, can still be indexed: its `at` makes the
  `Bool`, lends it, and writes it back. Rust's `Index` returns a reference,
  so there such a collection cannot be indexed.
- **A lending call lends its whole receiver.** The method waits to resume,
  and was proven as if nothing else touches `self` until it does. So
  `mut grid[a].swap(mut grid[b])` is an error for a user's `Grid`.
  `List`, `Slice`, and `Array` can lend two parts because their `at` has
  nothing left to do after its `yield`.
- **A lending method always continues afterward,** so a type can update
  values that depend on the part, such as a cached total.
- **A loop can stop at any `yield`, and the method does not continue.**
  Continuing to the next `yield` would do unasked-for work, such as reading
  one more line after `break`, and Truss has no `finally`. So invariants
  hold at every `yield`, and a type whose invariant a changed element would
  break offers read-only and owned loops, and changes single elements through
  a lending method.
- **The contract names the yielded parts and the history,** as Dafny's
  iterators do. A loop over a list then gets its facts from the list's
  `each`, so a user's collection gets the same facts. In a range's clauses
  the loop variable names the next index, because `kept <= index` reads
  better than `kept <= yielded.length() + 1`.
- **Read-only and owned yields can be pulled.** Internal iteration alone
  cannot advance two sequences together, so it cannot write `zip`, merge, or
  `peek`. One rule covers both uses: a method may end at any `yield`.
- **A pull yields an owned value,** so a read-only yield of a place is
  pulled only where the element is `Plain`; anything else would be copied
  unasked.
- **`mut` yields cannot be pulled,** since a cursor would store `mut` access.
- **Recursive yields can be looped over but not pulled.** A cursor would need
  room for every level of the recursion, which C# and Python allocate behind
  the scenes. A cursor over such a structure is a type with an explicit
  stack, so its allocations are visible. Whether a method can be pulled is
  derived from its body, one of two facts callers take from a body; the
  tools show both with the signature.
- **Cursor types have no name.** A cursor is a state machine the compiler
  makes from one method, described by `Cursor`. Code that holds one is
  generic over it, or uses `any Cursor` and allocates once. Returning a
  cursor without allocating would need opaque result types, which can be
  added later if needed.
- **No coroutines at run time.** A loop or a lending call compiles to a call
  that receives the caller's code as a function, which inlining makes as
  cheap as a written-out loop. A pulled cursor compiles to a state machine.

### Closures

A lambda that reads local variables holds views of them:

- **Lambdas capture by read-only view,** so they can be passed to comparators,
  `map`, and `parallel` callbacks, and any lambda is safe to call from
  parallel branches.
- **No changing captured variables.** State that changes as you go belongs in
  a `for` loop or a method like `fold`, and function types stay one kind.
- **Only functions that capture nothing can be stored.** A function-typed
  parameter is non-escaping unless it is `own`.
- **A callee states the arguments it passes its callback.** A lambda's parameters
  have no annotations, so `indices.map(fn(i) { values[i] })` could not prove
  its index unless `map`'s parameter type carries a `requires`. It is allowed
  only on a parameter's type, so it never becomes part of a type that values
  are stored in or compared by.
- **Behavior with state is a record with a trait,** not a closure.
- **`return` in a lambda leaves the lambda.** Kotlin's non-local `return`
  from an inline lambda is a known source of confusion.
- **A lambda's types come only from where it is used.** Rust checks a
  closure's body before it knows the parameters' types, so "type annotations
  needed" is one of its commonest errors. Never inferring a parameter's type
  from the body keeps checking local. Modes are inferred too: `mut` at a
  call marks a change to an existing value, and a lambda's parameter is a new
  name.
- **There is one way to write a lambda.** A block's value is its last
  expression, so a short form such as `x => x * 2` would only be a second
  spelling. `it` and `$0` are not whole words, and a trailing lambda is a
  second way to pass an argument.

This needs none of Rust's `move` closures or its three closure traits.

## Methods

- **Methods live with their type,** in its package, so a method is easy to
  find, and two packages can never add conflicting methods to one type.
- **Every call uses parentheses,** so a reviewer can tell that
  `names.length()` runs code and `point.x` reads a field.
- **One name can have a version per receiver mode.** One `enumerate` serves
  read-only, `mut`, and `own` loops, where Rust needs `iter`, `iter_mut`, and
  `into_iter`. Overloading by parameter types is not allowed, because it
  makes calls harder to predict.
- **Versions merge only where one author wrote them:** a type's own methods,
  the methods an `impl` in the type's package writes, and a trait with the
  traits it requires. Picking among everything visible would let code added
  elsewhere take over a call. On a temporary the `own` version is chosen, so
  if another package could give a type's `label(self)` a `label(own self)`,
  `Counter(3).label()` would change meaning when that package was added. A
  method an `impl` leaves to its trait is no different, since a later
  release of the trait can add one.
- **Traits with type parameters cover most uses of overloading.**
  `Int64.from(count)` picks an `impl` of `From[Source]` by the type of
  `count`. Free overloading would cost fast, local type checking: Swift's
  "expression too complex to type-check" errors come from overloads combined
  with literals typed by context, which Truss also has. Adding an overload
  anywhere could change an existing call, and a reader could not tell which
  `process` runs in `process(item)`. Traits with type parameters avoid
  these, because argument types are settled first, nothing is chosen from
  the expected result, and the candidate `impl`s live in fixed places.
- **Truss has no `into()`,** whose target Rust infers from context and which
  is a common source of inference failures.
- **Mixed-type arithmetic goes through the operator traits,** because times,
  geometry, and money need `instant + duration`. Comparisons stay within one
  type, because the laws of `Equal` and `Ordered` relate a type to itself.
- **An operator trait says where its operation is defined.** If `add`
  promised a result for every pair of values, an `impl` for a fixed-width
  integer would have to wrap or crash, and generic code could overflow with
  nothing in its signature to show it. So the operation requires
  `add_is_defined`, and generic code carries the obligation that an operator
  on a built-in type has.
- **Associated types are chosen by each implementation,** and type
  parameters choose the `impl`. Truss needs both: associated types for
  `Index` and collections, and type parameters for `From` and the operators.
- **Overloading by argument labels may come later.** It interacts with
  defaults and the optional first label, and named constructors cover it
  for now.
- **Trait methods need no import,** since forgetting one is a common error
  where they do.
- **Only traits from nearby packages are found by a dot.** Swift let
  extension members leak to every module that imported their module, even
  indirectly, so a change deep in the dependency graph could break distant
  calls, and SE-0444 limited them to direct imports. Truss uses the manifest
  for the same limit.
- **A clash between names is always an error, never a silent choice.** Where
  a type's own method wins over a trait's, as in Rust, adding a method can
  silently change an existing call. In Truss an upgrade can break a call only
  with an error that names both sides. A release that only adds names is
  still compatible, since otherwise no type could ever gain a method.
- **An `impl` lives with its trait or with a type it names,** which is Rust's
  orphan rule, simplified. Packages cannot depend on each other in a cycle,
  so for any pairing of types only one package can name them all, and an
  `impl` has one possible place.
- **Constructors follow one convention.** `Type.new(...)` is the main
  constructor, and others have descriptive names, since `new` cannot be
  overloaded.

### Equality, ordering, and deriving

- **Deriving is opt-in.** Implementing `Equal` on a public type is a promise
  to its users, and structural equality is wrong for some types, such as a
  set stored as an unsorted list. Truss has no macros, so `derives` covers
  the uses of Rust's `#[derive]`.
- **Laws come for free with derived implementations,** when the fields
  satisfy them.
- **Only structural equality lets the prover substitute.** A hand-written
  `Equal` promises only an equivalence, and a `Point` of floats has
  `Point(x: 0.0, y: 0.0) == Point(x: -0.0, y: 0.0)` while `1.0 / x` tells them
  apart. An opaque type's equality would depend on fields other packages
  cannot see. Like copying, it is derived from the type's shape.
- **Float equality is lawful.** IEEE's `NaN != NaN` breaks reflexivity, and
  Truss proves laws rather than ignoring them. So all NaNs are equal and NaN
  is ordered last. Making floats IEEE by default would bring Rust's
  limitation instead: floats that cannot be sorted, used as map keys, or
  compared in a derived `Equal`. Giving floats no lawful equality would stop
  a `Point` of floats from deriving `Equal`.
- **Lawful float comparison costs a little:** a few instructions per
  comparison, which can matter in a hot loop. The `ieee_` comparisons are
  the exact, single-instruction escape hatch.
- **One derived `Serialize` works with every format,** because its methods are
  generic over a `Serializer`. A type that needs other names writes its
  `impl`, since Truss has no attributes.
- **Derived `Ordered` and `Hash` need a derived `Equal`.** Their laws link
  them to `Equal`, and two derived implementations agree by construction. A
  hand-written `Equal`, such as one for a set stored as a list, would not
  agree with a field-by-field `Ordered` or `Hash`.
- **Debug output is built in for every type,** so the test runner can show any
  value without a derive. Text for people goes through `Display`, written by
  hand, because a structural dump is rarely fit for a user.

### Traits that require other traits

- **Laws can span traits.** `Hash` requires `Equal`, so its law, that equal
  values hash equally, can be stated and proven. In Rust, `Hash` does not
  require `Eq`, and that law is only a comment.
- **No diamond problems.** A type has one implementation of each trait, so
  two traits that both require `Equal` share it.
- **Every `impl` is written out, and none overlap.** An `impl` that covers
  every type matching a bound makes it hard to tell which implementation
  applies, and overlapping impls are the source of Rust's long-stalled
  specialization. Starting strict leaves room to relax the rule later.
- **A provided method can be replaced only by a version proven to give the
  same result.** So `a != b` always means `!(a == b)`, the prover reasons from
  the trait alone, and adding an `impl` never changes a provided method's
  meaning, while a type can still swap in a faster version. This covers
  most uses of specialization without overlapping impls. Fast paths that
  depend only on how a type is stored, such as copying a list of plain data
  at once, need no language feature: the compiler knows which types are
  `Plain`.
- **An `impl` can promise more than its trait:** a weaker precondition and a
  stronger postcondition, which is behavioral subtyping. It lets `Index` say
  nothing about the lent part, while `List`'s `impl` says which element. A
  tag's `from_template` is the one method whose `requires` may be stronger,
  since a tag exists to constrain a template's literal text, and a template
  always names its tag.

### Dynamic dispatch

| Need | Use |
|---|---|
| One type, known at the call | Generics with a bound, dispatched statically |
| A fixed set of alternatives | A sum type |
| An open set, mixed in one collection | `any Trait` |

- **The cost is visible.** Making an `any` takes an explicit `any value`,
  which allocates once. An implicit conversion would hide the allocation.
- **An `any` type fixes every associated type** of its trait, since a method
  that mentions one could not otherwise be called.
- **Limits apply to calls, not traits.** A method that needs the concrete
  type cannot be called through `any`, and the error is at the call, so a
  trait never becomes unusable with `any` because one method doesn't fit, as
  Rust's object-safety rules make it.
- **Dynamic calls are verified through the trait,** so adding an `impl`
  checks only that `impl`, never the callers.
- **No downcasting.** Code that needs to know which type it has is dealing
  with a closed set, which a sum type expresses with exhaustive matching.

## Operator precedence

Precedence is a partial order. Operators have a relative precedence only
where languages agree on one, such as `*` over `+`, and every other
combination needs parentheses.

- **Bitwise operators and shifts combine only with themselves.** C puts `&`
  below `==`, so `flags & mask == 0` tests `mask == 0`, and C, Rust, Go, and
  Swift order the bitwise operators differently from one another. An LLM
  trained on all of them cannot be trusted to remember one table.
- **`&&` and `||` cannot be mixed,** for the same reason.
- **`!` cannot be the left operand of `is`.** `not x is y` negates the test
  in Python, and `!x is T` negates the value in C# and Swift.
- **Comparisons do not chain,** because `a < b < c` means one thing in
  Python and another in C.
- **`echo` covers everything after it,** so putting it in front of an
  expression shows the whole expression.
- **Ranges bind more loosely than arithmetic,** so `0..count - 1` means
  `0..(count - 1)`.
- **`+=` exists, and `++` and `--` do not.** `+=` writes a place once, so a
  long place is not mistyped the second time and an index is proven once.
  As expressions, `++` and `--` were confusing and rarely clearer than
  `+= 1`, which is why Swift removed them. The old value goes to the operator
  as owned, so `matrix += other` can work in place without separate traits
  such as Rust's `AddAssign`.
- **An assignment evaluates its right side before its target.** A compound
  assignment's target holds no value until the result is stored, so
  evaluating the operand first keeps all other code out of that window: a
  `?` in the operand cannot return with the target moved out.
- **Integer division rounds toward zero, and `>>` copies the sign bit,** as
  the hardware does.

## Integers

- **`USize` is for sizes, lengths, and indices,** so a length is never
  negative and a bounds check is one comparison. `ISize` is for offsets.
- **Code is verified for every width `USize` can have.** The prover knows
  only that it has 32 or 64 bits, so a proof holds on every target and its
  result needs no target in its key. A package that runs only on 64-bit
  targets says so with `usize_bits = 64`, and a package that does not cannot
  depend on one that does, so a package that claims to run everywhere does.
- **Literals take their type from context, with no suffixes,** so `3` has one
  spelling and simple variables need no annotations. An integer literal is
  never a float, so `1` and `1.0` look different.
- **A local declared from literals takes its type from its first use.**
  Otherwise `let limit = 10` would fix `limit` at `Int64`, and code on
  `UInt8` or `USize` would need an annotation on every such local. Only a
  literal type outlives its statement, and it can only become a number type,
  so the declaration still tells the reader that the local is a number. A
  use that disagrees with the first is one error, with a note at the
  statement that decided the type.
- **A literal in an operator takes the other operand's type,** as Go's
  untyped constants do. The rule never looks at which `impl`s exist, so
  adding one never changes a call. Rust lets `impl` search decide a literal's
  type, so an `impl` added later can make an existing call ambiguous.
- **A leading zero is an error.** `0755` is octal in C and the shell, where
  its obvious use is file permissions, and reading it as decimal would
  silently give the wrong permissions.
- **Overflow is never silent,** for every integer type.
- **Code for every width is written once, against the integer traits,** as
  Swift's extensions of `FixedWidthInteger` are, where Rust's standard
  library generates each width with a macro.
- **The integer traits are sealed,** so generic code over one is proven once
  for each built-in type, with that type's range and bits (see PROVER.md).
  For the same reason, a literal under such a bound fits every type that
  implements the trait.

## No hidden failure

**Code never stops abruptly unless its signature says it can.** The only
exceptions are running out of memory and overflowing the stack, which no
language rules out. Every operation that can fail is a proof obligation, with
four ways to meet it: establish it locally, require it from the caller, call
a checked version, or declare `uses Panic`.

**Tests do not wait for proofs.** A program is built only once every
obligation it reaches is proven, but a test build checks every primitive
operation that could fail when it runs. Generated code never has undefined
behavior, even where a proof is pending or failed, so tests run as soon as
the code type-checks, alongside the prover. A failed check names the
operation, which tells an agent whether a failed proof is a real bug or a
prover that needs a hint. A test build checks every operation whether or not
it was proven, so its results do not depend on the state of any proof.

**No clause is evaluated when a program runs.** Running a `requires` would pay
for its proof again, at whatever the clause costs: a test build would make
`binary_search` linear by checking that its list is sorted. Each check that
a test build makes takes constant time.

**`unreachable` must be proven.** Code that says a point can't be reached must
not quietly crash when it is. To crash on purpose, call `Panic.crash`, which
the signature shows.

**A panic cannot be caught.**

- **No one can see a half-finished update.** Code that caught a panic could be
  left holding a value whose invariant was broken partway through a change.
- **Robust programs prove they cannot panic.** A server can require its
  handlers to have a type without `Panic`, so no request can crash the
  process. If the whole process fails, a supervisor restarts it.
- **Tests cannot expect a panic.** That would treat crashing as intended
  behavior, which is the job of `Result`. Misuse that other languages test
  this way, such as breaking a precondition, does not compile. To check that
  a program crashes on bad input, an external test runs it through
  `Processes`.
- **A failed `assert` is not a panic.** It ends the test as failed, like an
  early return.
- **A panic ends only one worker.** The test runner keeps a pool of worker
  processes, each running one test at a time, and starts a new worker after
  a crash. Sharing a process between tests is safe because Truss has no
  mutable globals and a test touches only its inputs.
- **Tests have a time limit,** so a loop that never ends fails its test.

**Float results are the same on every platform.** Functions such as `sin` and
`exp`, and conversions between floats and text, are the standard library's
own rather than the platform's C library's, whose results differ between
systems, as Java's `StrictMath` is. A cached test result then holds on every
machine, and evaluation while compiling matches the compiled program.
`to_bits()` returns one pattern for every NaN, because processors disagree
about which NaN an operation produces.

## Errors

Recoverable errors are values of type `Result`, and `?` returns early with
the error. `Panic` is for bugs, not expected errors.

**Every value must be used.** One rule catches three kinds of mistake:

- **A dropped error,** such as the ignored `Result` of a write.
- **A pointless call.** A call of a pure function whose result is thrown away
  does nothing, as `names.sorted()` where `mut names.sort()` was meant.
- **A misread line break.** A line starting with `-` begins a new statement,
  which leaves an unused value.

Rust and Swift warn only for marked types or functions, which catches only
those. A rule for every value needs no warnings and no attributes. It pushes
APIs toward returning `Unit` when the result is usually not needed.

**Every variable must be used, and every `match` arm must be reachable.**
Such code is almost always a mistake, often a typo, and the two rules also
make constants safe to use by name in patterns. Parameters are exempt,
because a trait implementation may not need every parameter.

**Unreachable code is an error,** since it is almost always a line left behind
by an edit. The check uses types alone, so it never reasons about values.
Code after a `todo` is unfinished, not dead.

**`?` never converts the error.**

- **No hidden code runs.** In Rust, `?` silently calls a `From`
  implementation chosen by type, which can allocate and is a known source of
  inference failures. In Truss every conversion is a visible call, with its
  costs proven.
- **Errors get domain names,** such as `Unreadable` or `Malformed`, in the
  function's own terms.
- **Conversion stays short,** because a single-field variant is a function.

Error unions that `?` widens automatically could be added later without
breaking code, if wrapper types written only to combine two errors become
common.

## Capabilities

A capability is a named set of methods for doing something outside pure
computation. A function lists the capabilities it uses, and whoever runs it
chooses the implementations.

- **Functions are pure unless they declare `uses`.**
- **A dependency can do only the effects its signature allows,** which limits
  the damage a compromised package can do.
- **Tests are deterministic.** A test provides fakes of files, clocks, and
  networks, so its result can be cached.
- **Tests that touch the real world say so.** An external test's result
  depends on the world, so it is never cached. It gets no hidden isolation;
  a test that wants a scratch directory narrows file access where a reader
  can see it. Failed tests are never retried, because a retry hides exactly
  the failures an external test exists to catch.
- **Implementations are ordinary types,** and one with state is a type with
  fields.
- **A view never crosses into or out of an implementation.** A caller cannot
  see which implementation its call reaches, so it could not know a view it
  passed is still held, and a view of the implementation's storage would
  outlive a later call that replaces it.
- **A capability method always returns to its caller.** So a capability call
  works and compiles like a function call, Truss needs no stack unwinding,
  and no computation is abandoned partway with a value half updated. Early
  exit goes through `Result` and `?`, where each step is visible.
- **Passing capabilities through is explicit,** with a capability parameter,
  which keeps one rule: no `uses` means pure. Callbacks are pure by default,
  the safe choice for comparators and anything run in parallel.
- **A trait can leave a set of capabilities to each implementation.**
  Otherwise `Cursor.next` would use no capability for every implementation,
  and a cursor that reads a file could not be passed to `zip` or `to_list`.
  Swift's `AsyncIteratorProtocol` leaves its error type to each
  implementation the same way. Effect variables on every function type, as in
  Koka, are more general, but a capability parameter already covers their
  main use, a callback. `any` fixes such a set to the empty set, because code
  that holds the value cannot name the capabilities of the type it hides.
- **A function type puts its clauses after its result, in parentheses.**
  Truss has whole clauses, not one or two effect keywords, so they come in
  the same order as in a definition, and the parentheses mark where they end.
- **`main` gets exactly the capabilities it declares,** so its signature says
  everything the program can do. Arguments are a parameter, so a test can
  call `main` with fake arguments and implementations. There is no `exit`,
  since a capability method always returns.
- **The standard capabilities are fine-grained where trust differs.** A config
  loader with only `FileRead` cannot destroy anything.
- **Opening a handle and using one are separate capabilities.**
  - If a handle's methods required the capability that opened it, reading a
    connection would need `NetworkClient` or `NetworkServer`, and a request
    handler would hold the power to open connections of its own.
  - One capability for every handle lets files, connections, and pipes
    implement the same `Reader` and `Writer` traits.
  - A handle is a token, and the provider of `Handles` decides a read's
    result, so a test can simulate a file or a network.
- **Narrowing is ordinary code,** an implementation that checks each call and
  passes it on. The code being called cannot tell it has been narrowed.
- **Providing a type provides every capability it implements,** so a type
  that narrows both reading and writing cannot leave one open by mistake.
- **Capabilities layer instead of inheriting.** `ReadDatabase` is implemented
  with `NetworkClient`, and the network shows where the implementation is
  provided, so a dependency granted `ReadDatabase` alone never touches the
  network. Truss leaves out bundles, such as
  `capability FileSystem: FileRead + FileWrite`: a reviewer reading
  `uses FileSystem` would have to look up its members, and grants would get
  coarser, to save typing that LLMs mostly do.
- **Signatures and narrowing do different jobs.** A signature limits which
  capabilities code has, and narrowing limits a capability's reach.

This is deliberately simpler than algebraic effect handlers, which can pause,
abandon, or repeat a computation for async code, generators, and
backtracking. Truss waits with blocking calls (see
[Concurrency](#concurrency)), so it does not need them.

### Dependencies

If your code already uses `NetworkClient` and calls `json::parse`, a new
version of `json` could start using the network, and your code would still
compile, because you already had the capability to pass along. So the
manifest grants each dependency its capabilities (see
[PACKAGES.md](PACKAGES.md#grants)):

- **Every dependency has a grant, a project's own packages included.** Much of
  a project's code is written by LLMs and not all of it is reviewed, so the
  limit matters at home as it does for a stranger's code.
- **Giving a package more power is always a visible change to a manifest,**
  and never made by a tool: whoever grants one writes a line a reviewer sees.
- **Grants are checked wherever a dependency's code is named,** not only at
  calls, since otherwise a package with no grant could have its `impl` run
  by a package that has one. The dependency's bodies are already checked
  against its signatures, so nothing it does can go further.
- **A package needs a grant even for a capability it defines,** since the
  capability's provider decides its behavior.
- **Grants nest through signatures.** A function a package offers carries in
  its `uses` every capability beneath it, so a package hands its own
  dependencies no more than it holds, with no rule about manifests.
- **A new version cannot take more capabilities for functions already
  called,** because adding one to a function's `uses` is not a compatible
  release.
- **Each package's capabilities are recorded** in the lock file, so an upgrade
  deep in the graph that hands a package the network shows as a changed line.
- **Nothing in a package runs when it is fetched or built.** Install scripts,
  build scripts, and procedural macros run a dependency's code with
  everything the developer can reach, which is how a package that steals a
  publishing token goes on to publish itself under its victim's name. Truss
  has none of them, the code that runs while compiling is pure, and a
  dependency's external tests are never run by its users.

Grants cannot stop a wrong answer: a pure dependency can still return a
result that its user acts on. Contracts narrow that, and review of a
project's dependencies is still needed.

Because `main`'s `uses` clause is complete, a later compiler could also apply
operating-system restrictions such as seccomp to match, so a program without
network capabilities could not open a socket even through a compiler bug.

## Costs

- **Costs are optional,** and checked where present.
- **Bounds can be asymptotic or exact.** Countable resources take exact
  bounds, which can say that each item is processed exactly once. Concrete
  time bounds are not allowed, because they cannot be proven across
  machines.
- **`O(f)` holds for every input, not just large ones.** The textbook
  definition is about limits, which a prover handles poorly, and it gives
  wrong answers for bounds in several variables (Howell, "On Asymptotic
  Notation with Multiple Variables", 2008).
- **Bounds can depend on the result,** since output-sensitive bounds, such as
  that of a function that returns its matches, are common and otherwise
  impossible to state.
- **`log(n)` rounds log₂(n + 1) up,** so it is defined at 0 and stays an
  integer; inside `O` the base makes no difference.
- **Amortized bounds are proven with potentials,** following Automatic
  Amortized Resource Analysis (AARA). AARA needs values that are never
  shared, because two references to one structure could spend its potential
  twice, and mutable value semantics gives exactly that, so amortized bounds
  compose soundly. A value's potential includes its parts', so pushing onto
  a list inside a list is paid for by the inner list.
- **There are no expected-time bounds.** A hash map is O(1) only on average,
  assuming hashes behave randomly, which no proof can promise against an
  attacker's input, and proving expected bounds needs logics that are still
  research.
- **Costs count capability calls,** and the count holds whatever
  implementation performs them.
- **Costs compose through signatures,** so changing one function re-checks
  only its dependents.
- **Loops can state their cost so far,** as an invariant about the cost. Most
  loops need none. A loop's cost is never `amortized`, since potential
  belongs to the values a loop changes, and never `finite`, since a loop
  shows that it ends with `decreases`.

## Termination

- **A `time` clause promises termination,** so no separate marker is needed.
- **Functions in specifications are pure and terminate.** A function that
  might not return, or might stop the program, has no value to reason about.
- **Recursion over the parts of a value needs no annotation,** as Lean
  accepts structural recursion. Other recursion states a measure. Truss does
  not guess one, as Dafny does, because a structural check plus an explicit
  clause is more predictable than a guess that may or may not work.
- **Recursion counts every way a function can reach itself.** A function can
  name another as a value, or use an `impl` where a bound needs one, and the
  code that receives it calls back. Without counting those, a package could
  implement a trait with a method that calls a generic function that calls
  the method back, and each `time` clause would be proven by assuming the
  other. Truss has no mutable state outside variables, and a value cannot
  hold a terminating function that takes the value, so every cycle is
  visible within one package.
- **A type cannot hold a terminating function that takes the type.** With
  `type Knot(run: (fn(Knot) -> Bool cost time finite))`, a function that
  calls `knot.run(knot)` calls itself with no name in its code that says so.
  Coq and Lean forbid this for every function type, as strict positivity.
  Truss forbids it only with a `time` clause, because a function with a
  `time` clause cannot call one without, so `type Button(on_click:
  fn(Button))` is legal.
- **A loop that runs until a capability says to stop cannot be proven to
  terminate,** because an implementation could supply data forever.

## Verification

Everything a program promises is proven at compile time.

- **Most proofs are automatic.** Each obligation goes to an automated solver,
  as in Dafny, and the programmer writes a proof only where it gets stuck.
- **Proofs use the language's own syntax:** theorems, proof blocks, and law
  proofs are written with calls, `match`, `if`, and `assert`, which
  programmers and LLMs already know. A tactic language, as in Lean, checks
  proofs very predictably but is a second language to learn.
- **Reviewers can trust proofs instead of reading them,** and read only
  signatures and contracts. A proof is a result of its own, so editing one
  re-checks proofs without rebuilding the program or rerunning tests.
- **Verification is modular.** The prover knows other functions by their
  signatures, and reads a body only where it is a definition, so each proof
  looks at little code, which keeps proofs stable and checking O(change).
  The prover's design is in [PROVER.md](PROVER.md).
- **Proof checking is deterministic.** The solver runs within limits counted
  in steps, never in wall-clock time, and its version is pinned. A proof
  that passes once keeps passing, and a slow machine never fails a proof
  that a fast one passes. Solver-based tools are known for proofs that break
  for unrelated reasons, so Truss designs against it from the start.
- **There is no `assume`.** A missing proof that an addition cannot overflow
  would allow a failure the signature does not show. A claim that is not
  ready is left out of the signature.

### Bodies and contracts in proofs

- **A functional body is its function's definition,** as Dafny's
  `function`s are. A body with a loop has no meaning the solver could use
  without a loop invariant, which would restate the contract.
- **No keyword marks either kind.** The body already says which it is.
  Whether a body is read is a fact callers' proofs depend on, so their traces
  record it, and the tools show it with the signature.
- **A definition is read only where everything it reads is visible,** so
  `opaque` keeps the representation private from proofs too.
- **Definitions must be well founded,** which the `time` clause and the rules
  of [Termination](#termination) guarantee.
- **Quantifiers are expressions in code too.** The binder carries its range,
  so the body may rely on it, where a lambda passed to a method would know
  nothing about its argument. So the standard library has no `all` or `any`
  methods, and testing every element has one spelling.

### Specifications

- **Specifications have no capabilities,** not even `Panic`: a logical
  function that might stop the program has no value to reason about.
- **Specifications read left to right,** so
  `index < items.length() && items[index] > 0` is well defined.
- **Specifications have implication.** "If this holds, then that holds" is the
  commonest shape of a specification, and `!a || b` hides it. `==>` binds
  more loosely than `&&` and `||`, as in Dafny. Code already has `if` and
  `!a || b`, so `==>` stays in specifications.
- **Laws take `requires` premises,** so `transitive` reads as its
  definition.
- **Integer arithmetic in specifications is exact,** so a specification cannot
  have an overflow bug, and `decreases high - low` can be negative, which is
  the case the prover must rule out. An `Integer` stands where a built-in
  integer is expected with no cast, since the obligation that it fits is
  proven either way.
- **A function for specifications needs no keyword,** since its signature
  already mentions a type that exists only in specifications.
- **Float arithmetic in specifications follows IEEE 754.** Exact real
  arithmetic would describe results the hardware does not produce, so such
  contracts could never be proven. Float contracts are checked bit for bit,
  which is slow, so they are best kept rare.

### Mathematical models

A contract about a whole collection needs a value to compare it with.
Saying that `push` adds an element at the end through `length()` and
indexing alone takes a quantifier for every statement, and a hand-written
`Equal` is not even structural. So the prelude has mathematical collections
that exist only in specifications, and a type gives its value in their terms
through `Model`. Verus, Creusot, SPARK, and Dafny each converged on this.

- **An opaque type's model is how other packages reason about it** without
  seeing its fields.
- **The mathematical types have structural equality,** so the prover can
  substitute through them where a collection's own `Equal` is hand-written.
- **`identical(a, b)` is identity.** Generic contracts must say that an
  element is a given value whatever its type, and `==` cannot: it is the
  type's `Equal`, which `List[Element]` does not require, and for a set
  stored as an unsorted list it is an equivalence rather than identity. So
  `==` keeps one meaning everywhere. Verus instead gives `==` a different
  meaning in specifications than in code, which would let a contract on a set
  mean identical representations where its author meant the same set.

## Unfinished code

A package's API can be designed before it is implemented, with `todo` in
place of bodies and type definitions.

- **Unfinished code is checked as far as it can be,** so a caller's contracts
  can be fully proven before its callees exist.
- **Unfinished code is never shipped.** A `todo` that panicked when reached
  would be a failure hidden from the signature, so a build refuses any
  program that can reach one.
- **Tests run anyway,** and a test that reaches a `todo` is incomplete, so
  tests can be written first.
- **The tools list every hole and the work it blocks,** with its expected type
  and the names in scope, which makes each a self-contained task, and lets
  several agents fill holes in parallel.

## Debug output

`echo expr` lets pure code show a value without declaring a capability.

- **It changes nothing the compiler reasons about,** so adding one never
  changes whether code compiles or verifies.
- **It cannot ship,** which makes it safe to skip `uses`.
- **It works with cached tests.** Adding an `echo` changes the keys of the
  tests that reach it, which run again and show the output. Tests are
  deterministic, so the run takes the same path as the one being
  investigated.
- **Its output stays readable,** grouped by branch or task, never
  interleaved.
- **It is a whole word,** and `debug` and `trace` are common names.

## Loops

Most loops need no annotations, because the contract of the `each` method a
loop calls gives the prover its facts: an index in bounds, one iteration per
element, and termination. None is a special case, so a user's collection
gives its loops the same facts by making the same promises. A `while true`
that is never left has type `Never`, so a server whose main loop runs
forever can return `Never`. There are no labeled breaks for now.

## Parallelism

Parallelism means using several cores to finish a computation sooner. In
Truss it is deterministic: a `parallel` block gives the same result as
running its branches one after another.

- **No data races, by the rule for calls.** A place passed `mut` can be used
  by nothing else at the same time, which rejects
  `swap(mut first, second: mut first)`. Across branches, branches may read the
  same place, but a place one branch changes is used by no other.
- **No capabilities inside.** Two branches calling one stateful
  implementation would race, and the order of their calls would vary from run
  to run. Code whose parts use capabilities at once is concurrent.
- **A function that uses `parallel` is still pure,** and tests that run it can
  be cached.
- **Proofs and costs work as for sequential code.** Branches are disjoint, so
  their order cannot matter. `time` measures total work.
- **`span` is planned, for the work that cannot be done at once.** On `p`
  cores a function finishes in time proportional to `time / p + span`, the
  work-span model of Cilk, so `cost time O(n)` with `cost span O(log(n))`
  would promise a function that gets faster with each core. `span` joins the
  grammar with the first standard library function that states it.
- **The result does not depend on the machine.** Where a computation is
  split is decided by its input, never by the number of cores, so a parallel
  float sum gives the same bits everywhere.
- **Branches run on a pool of threads that steal work,** one per core, started
  the first time a program runs code at once.
- **Tests run branches in order,** since the test runner already runs one test
  per core, and a failed check is then the same on every run.
- **Early exit is not allowed.** A branch uses no capabilities, so it cannot
  be asked to stop, and leaving early would have to abandon the other
  branches or wait for work whose result is thrown away.

## Concurrency

Concurrency means doing several things whose order is not fixed, such as
serving connections, or waiting for a reply and a timer at once. Such code's
behavior can depend on the order of events, so concurrency is an effect:
code that does it declares `uses Tasks`.

- **A `concurrent` branch differs from a `parallel` one in one way:** it may
  use the capabilities around it. So the rule about places that rules out
  data races in `parallel` rules them out here too.
- **A task never outlives the block that started it,** as in structured
  concurrency, such as Trio's nurseries. So a branch can read the places
  around it without lifetimes, and use the capabilities provided around it,
  whose implementations are the enclosing code's variables. A task started
  with Go's `go` can outlive everything it was given, so it could be given
  neither.
- **A task borrows only places that outlive the loop.** A `concurrent for`
  iteration outlives the `yield` that started it, so a place that could
  change when the method resumes cannot be yielded to a task.
- **It is a construct, not a `spawn(work)` function.** `spawn` would have to
  keep `work`, and only a function that captures nothing can be kept, so the
  task could read nothing around it and would hand back its result through
  a handle to join. A branch needs neither.
- **Blocking calls, no async.** Code waits by calling a capability method
  that returns when the result is ready. `uses` already separates code that
  can wait from code that cannot, and a second mark for the same fact, such
  as `async`, would split functions into two kinds that can't easily call
  each other.
- **How a task waits can change without any code changing.** Every call that
  waits is in the standard library's real implementations, since there is no
  foreign code, so they can give each task a thread or switch many tasks on
  a few threads, and no caller can tell which. Go and Java cannot switch away
  from a task that waits inside foreign code.
- **Cancellation is an error value.** A cancelled task's calls that would wait
  return the value that says they did not finish, and `?` carries it out, so
  a cancelled task ends by returning, along a path written in its code. The
  value comes from an implementation proven against its `ensures`, so a
  caller's proof holds either way. Raising an exception at the call, or
  dropping a computation at whichever `await` it had reached, would abandon
  the computation partway, which Truss never does.
- **A time limit and a race are ordinary code,** two branches each of which
  returns, so nothing like Go's `select` is needed.
- **A channel's message is owned and `Storable`,** so sending copies nothing,
  and the message never views an original that could be gone before it is
  received. A task that waits for several kinds of message receives one sum
  type from one channel.
- **State that tasks share lives in a capability implementation.** Two tasks
  cannot share a variable that either changes, so shared state, such as a
  table of sessions, implements a capability, and `uses Sessions` marks every
  function that can touch it.
- **A `mut` implementation is a monitor.** Within a call nothing else changes
  the state, between two calls anything may, and no task holds a view of the
  state, since a method returns none.
- **Proofs already allow for it.** The prover never models an
  implementation's state, so no proof assumed that it stays the same between
  calls.
- **These mutexes cannot deadlock.** An implementation's methods call only
  capabilities provided outside it, so every task acquires mutexes from the
  innermost implementation outward. A callback that uses a capability could
  acquire one out of order, which is why such a method takes none.
- **Mutual exclusion costs nothing where there are no tasks,** since whether
  a `provide mut` needs a mutex is known from signatures.
- **A mutex is not a value.** Rust's `Mutex` and Go's `sync.Mutex` change the
  value of a read-only place, which mutable value semantics rules out, and
  two tasks that take two of them in different orders deadlock. A task that
  owns the state and answers messages needs nothing new, but every use of the
  state then switches tasks twice and waits behind every other use.
- **A channel is built on a cell with a pure update.** The cell runs a pure
  function on its value while it holds its mutex. A pure function cannot
  wait, use another cell, or do I/O, so two updates cannot deadlock, and no
  task holds the mutex across a call that can wait.
- **Data races cannot happen, and waiting forever can.** A task can wait for
  a message no task will send.
- **Tests stay deterministic.** A test's `Tasks` runs one task at a time,
  chosen by a seed, and switches only at capability calls. Tasks share no
  memory that changes, so the orders of those calls are all the orders there
  are, and a race is a failure that one seed repeats, not a flaky one.
  FoundationDB tests this way.
- **A test's clock moves when every task waits,** so a test of a timeout takes
  no real time and its result can be cached.
- **Tasks and `parallel` branches run on one pool,** so code that computes
  and code that waits do not compete with two pools for the same cores.

## Collections

- **Each collection has one way to be written.** `[a, b, c]` is a `List`, so
  there is no `List.new()` or `List.of(...)`. Maps use `[key: value]`, since
  `{ }` already means a block.
- **A `[...]` literal takes its type from context,** as number literals do,
  and the expected type is always written nearby.
- **`Array[Element, count]` holds a fixed number of elements in place,** so a
  digest or a lookup table needs no heap and copies like an integer.
  Arithmetic on its length inside types is left out for now: Rust has worked
  on it for years without settling it, and it can be added later.
- **Literal allocation is counted.** A non-empty list literal counts as one
  allocation, whether or not the compiler keeps it in static memory, so cost
  clauses do not depend on an optimization.
- **A set or map literal is a sequence of calls,** so a `cost` clause is
  checked against the code that runs.
- **Constant collections are built while compiling,** by the standard
  library's own insertion code with no random hash key, so lookups cost as
  on any map and the table is the same on every build.
- **Duplicate keys in a map literal are a proof obligation,** the `requires`
  of `insert`. Letting the last one win would hide a mistake.
- **`Map` and `Set` iterate in insertion order,** which never varies from run
  to run, so tests stay deterministic and their results can be cached.
- **Maps resist hash flooding deterministically.** Keys chosen to collide can
  turn each operation into a scan of the whole map, which stalled servers in
  many languages in 2011. A random hash key per process, the usual defense,
  is randomness no signature shows: it would change timing and allocation
  counts from run to run, and make a test near its time limit flaky. Truss
  instead does as Java 8 does: a bucket that fills up becomes a balanced
  tree, so the worst case is O(log n), which cost clauses can promise. This is
  why keys are `Ordered` as well as `Hash`.
- **Random hashing is available through a capability,** for code that must
  stay fast under attack, and every source of randomness goes through one.
- **Open-ended ranges only appear in brackets,** because `0..` elsewhere would
  give `for` loops with no end.
- **Strings cannot be indexed,** because a UTF-8 string's byte `i` and
  character `i` differ, so code says which it means.

## No foreign code

- **A young ecosystem grows by being written in Truss.** If packages could
  call C, the quickest way to get a library would be to wrap one, and LLMs
  would take that shortcut every time, leaving an ecosystem over C code that
  no proof, capability, or cost clause covers. Elm made the same choice in
  0.19.
- **Foreign code would escape every guarantee.** A C function can do
  anything, so its capabilities, contracts, and costs could only be assumed,
  and Truss has no `assume`.
- **The cost is reach.** Anything that needs the operating system or special
  hardware comes only through the standard library. `extern` and `unsafe`
  stay reserved in case foreign calls are ever added.
- **Code for one platform lives only in the standard library,** so nothing
  else needs conditional compilation. Other code asks `Environment`, so the
  answer is tracked and a test can supply another.

## The standard library and prelude

Truss is batteries included: the standard library holds the modules a
command-line tool or a network service needs, so most programs need no
other dependency. Every dependency is a possible target for a supply-chain
attack, and the standard library is the one package every program already
trusts.

- **The standard library is part of the toolchain,** with no version of its
  own, in no manifest and no lock file.
- **A package says which Truss it is written for,** with `truss = "1.4"`,
  which is both the language version its files are read as and the least
  toolchain that can build it. Packages written for different versions build
  together, as Rust's editions allow.
- **The standard library never breaks.** A module that must break gets a
  successor beside it, named with `_v2`, as Go added `math/rand/v2`. Python's
  standard library modules went stale because they could be neither fixed
  nor removed; a successor fixes a module without removing it.
- **It holds the modules most programs would otherwise take from a package:** code
  that needs the compiler or the operating system, types that packages share
  to interoperate, such as `Path` and `http::Request`, implementations of
  published standards, such as JSON, TLS, and the cryptographic algorithms,
  and the protocols of a network service. Go's `net/http` shows that a
  standard library can hold protocols that still evolve. Cryptographic
  primitives need processor instructions, which only the standard library
  can reach.
- **Clients for a product are approved packages,** owned by `truss` on the
  registry, such as `truss::postgres`. They follow a product's releases, not a
  published standard, and few programs need any one of them. They are
  plain Truss, granted capabilities like any dependency, and held to the
  toolchain's review and release rules.

The prelude holds the names nearly every program needs, and is the same
everywhere, so `List` or `Result` means the same thing in every file. A
package cannot define a type with a prelude name, so a name is in the
prelude only if most programs' signatures use it: `Path` is, and `Pair` is
not, because a package may want that name.

### Standard library conventions

- **Each module is one subject, one level below `standard`.** Code writes a
  name with its module, so a type's name does not repeat the module's:
  `json::Value`. A category above the module, as in Go's `encoding/json`, is
  not written at the use site, so it only adds something to remember.
- **Subdirectories hold files that no one imports:** the methods and `impl`s
  of types declared in the parent module, and the real capability
  implementations.
- **Every module documents itself in a Markdown file beside it.**
- **Every method of a view also exists on its owner,** so `mut names.sort()`
  works without `names[..]`. Truss converts an owner to its view only at a
  parameter, so the standard library declares the methods.
- **Methods that work on any collection are provided methods of
  `Iterable`,** so a user's collection gets them by implementing `each`.
- **A collection method takes a pure callback, and an `Option` or `Result`
  method one that may use capabilities.** `map` and `sort_by` may later run
  their callback in parallel. `Option.map` calls its callback at most once,
  in place of an `if`.
- **A lookup that can miss lends an `Option`,** so nothing is copied, whatever
  the element type.
- **A capability declares only primitive operations,** so a narrowing
  implementation or a fake has few methods to write, and every helper works
  with every implementation.
- **Every operating-system failure is a `SystemError`,** so code that reads a
  file and sends it over a connection handles one error type.
- **Text in an embedded language is a tagged template.** A
  `processes::Command` is a program and an argument list, never a string
  passed to a shell.
- **A generic method's time counts its bounds' methods.** `O(self.length())`
  would be false for `contains` on a list of strings, where one comparison is
  not one step. A promise of `O(1)` on `Equal.equal` could not be kept by
  `String`, and a second trait for constant-time comparison would give every
  generic method two versions.
- **A write reports at most the bytes it was given,** proven for every
  implementation, so `write_all` can find the bytes that are left.
- **Each capability ships with its test fakes and its narrowing
  implementations.**
- **`files::MemoryFiles` is a file system, not a table of contents.** It
  returns the error the operating system returns for each misuse, because a
  test of error handling is only as good as the errors the fake can produce.
- **`simulation::World` fakes every capability at once,** because one provider
  must implement `Handles` for every handle, as the operating system does.
  FoundationDB tests its database this way.

## Visibility

A definition is visible only within its file unless it says `internal` or
`public`, which makes keeping code modular the easiest option.

A public signature cannot mention a private type, since other packages could
never name it. A `public opaque type` exposes its name but not its contents,
for three reasons:

- **Control over where values come from.** Some types are safe only if
  outside code cannot build them, such as `SqlQuery`, whose text must come
  from source literals.
- **Freedom to change a type's internals.**
- **Protecting low-level internals,** such as the pointer and capacity inside
  `List`.

The access boundary is the package rather than the file, because a type's
methods can live in any file of its package. Public types expose their fields
unless marked `opaque`, which is visible in review, because the fields are
written in the public declaration.

There is no level between `internal` and `public`. Swift's `package` level
works because the code it spans is versioned as one unit; Truss versions
each package on its own, so two packages that shared more than their public
definitions could be paired at versions never checked together. Code that
shares its internals belongs in one package, which costs nothing, since a
package is not a unit of building.

## Packages

A package is the unit of every boundary Truss checks: paths, `internal` and
`opaque`, where methods and `impl`s live, grants, and versions. The rules are
in [PACKAGES.md](PACKAGES.md).

- **A package is not a unit of building.** Results are kept for each
  definition, so splitting a package makes no build faster, and a package is
  split only where someone wants a boundary checked.
- **Every kind of package works one way.** A package is named by a path that
  is the same in every file of every project, and where its code comes from
  follows from the name.
- **A package's program starts at its `main` module,** so finding it is one
  lookup, and a package builds at most one program.

### Projects

- **Every package under the project's root belongs to it,** with no list of
  members. A list is one more file that every agent adding a package must
  edit, and so one more place for two agents to collide.
- **Packages find each other by name, never by a path.** Cargo's
  `path = "../geometry"` breaks when a directory moves.
- **A project's package takes the place of the registry's package of the same
  name,** which is how a dependency is fixed ahead of its owner, with nothing
  more to write and the copy in the repository for a reviewer to see.
- **A project's own packages have no versions,** because they are the code
  being worked on.

### Package names

- **A registry package is named `owner::name`.** On a registry with one flat
  list of names, a name one letter from a well-known one is how much malware
  arrives, and LLMs make this worse by making up names that attackers then
  publish under. With an owner in the name, who published the code is in
  every path that uses it.
- **The name in code is the registry's name, with no other,** because a
  rename would be an alias, and Truss has none.
- **A name is one package for good,** never handed to someone else.

### Versions

- **A build holds one version of each package,** because a path means one
  thing. Where two versions share a build, one path names two types: Rust's
  "expected `Vector`, found `Vector`".
- **So a release never breaks the API of an earlier one of the same name.**
  A change that would is published under a new name with `_v2`, as Go
  requires `/v2` for a module's second major version. Both can be in one
  build, and one file can use both while its code moves over. Where
  compatibility is left to each author's care, breaking changes in releases
  that claimed to be compatible are routine.
- **The registry checks it, from the signatures,** since the signature says
  everything important about a definition. Elm's registry checks releases
  the same way, from types alone; Truss's signatures hold more, so the check
  covers more.
- **Bodies are not promised.** A release may change a function's result
  within its contract, which is how a fix reaches its users. A proof in
  another package that leaned on a body is checked again after an upgrade.
  A guarantee users are meant to rely on goes in an `ensures`.
- **The registry gives each release its number,** so a number is never wrong
  about the changes.
- **There are no 0.x versions.** A version that may break at any release
  cannot be the one version of its name in a build.
- **A compatible release can still surface an error,** such as a new name that
  clashes with a user's, or a stronger contract the solver cannot answer
  within its limits, but never a change in the code's behavior.

### Choosing versions

- **A build uses the newest version that any of its packages was checked
  with,** and nothing newer, which is Go's minimal version selection.
- **Nothing new enters a build until someone asks.** Choosing the newest
  release a range allows puts a release published an hour ago into every
  build, which is how a compromised release reaches thousands of machines
  before anyone has read it.
- **There are no ranges and no solver.** Every version under one name is
  compatible with those before it, so "at least this one" is all a
  requirement can say. Choosing among ranges is NP-complete, and its answer
  changes as packages are published; this rule's answer depends only on the
  lock file, so it is the same on every machine, every day.
- **Versions are written only in the lock file.** An LLM does not know which
  versions exist today, so no file written by hand holds one.
- **The lock file names content,** so fetching changes no answer and needs no
  command.
- **Two changes to a lock file always merge,** by taking the higher version.
  A solver's lock file is one of many valid answers, which cannot be merged
  without solving again.
- **An upgrade is tried before it is made,** and reports the signatures that
  changed, the packages that enter the build, and each package that would
  hold a new capability.

### The registry

- **A package is published as its source,** so the code a reviewer reads in
  the registry is the code that compiles. A release whose published files
  differed from its repository is how the xz backdoor shipped.
- **Content is checked against a public log,** as Go's checksum database
  does, so the registry cannot give two users different code under one
  version, and a mirror needs no trust.
- **A package is published only when it is finished,** and the registry
  checks it again, which is safe with a stranger's code because nothing that
  runs while checking has a capability.
- **Proofs are shared, signed.** Proving a whole dependency tree on a machine
  that starts with nothing, such as an agent's new container, is the cost
  GOALS.md sets out to remove. Every signed result is a function of its key,
  so a registry that signed a false one is caught by whoever computes it
  again.
- **A new toolchain proves the registry again,** as far as it changed the
  proofs, and a toolchain that fails a proof of an approved package that the
  last one passed is not released.
- **A release marked as one not to use still builds,** since a mark that
  broke builds would let one compromised account stop every project that
  depends on it.

### Omitted package features

- **Optional parts of a package,** such as Cargo's features, exist to keep
  unwanted code out of a build. Code that nothing reaches is never compiled
  or granted anything, so a switch has nothing to save, and features cost
  Cargo builds that work only with some sets of switches.
- **A second list of dependencies for tests.** The dependencies only tests
  reach are computed when a package is published.
- **Dependencies on a git repository or a directory.** Unpublished code is
  worked on in the project that uses it.
- **Build scripts and code generators** (see [Dependencies](#dependencies)).

## Strings

- **Raw strings take text exactly as written,** so regular expressions and
  Windows paths keep their backslashes, without the doubling that causes
  bugs.
- **The closing `"""` sets the indentation,** so a raw string can be indented
  with the code around it. Every line starts with exactly that whitespace, so
  mixed tabs and spaces are an error rather than a silent change. Trailing
  whitespace is kept, because raw strings have no escapes to write it back.
- **Interpolation is `${expr}`.** A single `{` or `$` as the marker makes JSON,
  regular expressions, and shell text painful, because those characters are
  common there. `${` almost never appears in ordinary text, as JavaScript's
  template literals show.
- **Strings have no concatenation operator,** so `+` stays numeric and each
  allocation shows as an interpolation or a call. Adjacent literals do not
  join, because a missing comma in `["a" "b", "c"]` would silently merge two
  elements.
- **Text that contains `${` opens the string with more `$`s,** the fix Truss
  already uses for text that contains `"""`: a longer delimiter. C# 11 and
  Kotlin 2.2 both moved to it. A fixed escape such as `$${` would make one
  sequence special in an otherwise raw string.
- **Line endings are always `\n`,** so a string means and hashes the same
  whatever the file's line endings.
- **A `Character` is a Unicode scalar value.** It has a fixed size, so it
  copies implicitly, and its definition never changes between Unicode
  versions. A grapheme cluster has no fixed size and its boundaries change as
  Unicode adds rules, so graphemes are slices of the string.
- **Characters and bytes are tagged templates,** so they need no new lexer
  rule and no second set of escapes.

## Tagged templates

A tagged template keeps its literal text and its interpolated values apart,
which makes injection attacks impossible by construction:

1. **Only the compiler can create literal text,** so text produced when the
   program runs can never pass as trusted query text.
2. **Each interpolated value is converted to the tag's part type,** so a value
   with no meaning in SQL is a type error.
3. **APIs take the template's type, not `String`,** and `SqlQuery` is opaque,
   so outside code cannot build one.
4. **Unsafe cases are explicit,** such as `SqlQuery.from_trusted_text`, which
   is easy to find in review.

- **The tag is a type,** so the tag names the result, and a plain string is
  the `String` tag. A lowercase tag function would not fit the prelude.
- **Malformed literal text is a compile error.** Functions in specifications
  are pure and terminate, so the compiler can run the tag's check, which
  always finishes, and building the value then cannot fail. It reuses
  `requires`, pure functions, and termination.
- **A check cannot look outside the code,** such as at a live database
  schema, because builds have no capabilities.

## Naming

Names use whole words, with no abbreviations. Code is read far more often
than it is written, and with LLMs writing much of it, longer names cost
almost nothing to type. This is a convention, not a compiler rule, because a
hard rule would get in the way of the reasonable exceptions.

**A name always refers to one thing in a scope,** so readers never check
whether a familiar name was replaced by a local one.

**Keywords are reserved, with a few exceptions.** Reserved keywords let the
lexer tell a keyword from a name on its own, which lets it alone decide
whether a line break ends a statement. The exceptions are common names
needed in one narrow place, such as `result` and `time`; reserving those
would ban them from all code to serve a few specifications. The parser
recognizes them by their spelling where a clause expects them, since a lexer
mode would have to know where each clause ends. Words other languages use as
keywords, such as `loop` and `async`, are reserved now, so adding one later
breaks no code.

**Names are ASCII.** A name spelled with look-alike characters, such as a
Cyrillic `а`, is a known way to slip a malicious change past review.
Allowing every script safely takes normalization, rules about mixing
scripts, and Unicode's list of look-alikes checked across every name, all
changing with each Unicode version, and it still leaves gaps. The cost is
that a team cannot name things in its own language; text in any language
still goes in strings and documentation.

**Each language version pins a Unicode version,** as Java's specifications
do. Which characters are forbidden comes from Unicode data that changes every
year, so otherwise whether a file compiles would depend on the build of the
compiler.

**Constants are `lower_snake_case`, as values are.** A separate case would
give the lexer a third kind of name, and an `UpperCamelCase` constant could
not be told apart from a type.

**A constant in a pattern is written by its name.** In Rust this is a known
trap: a misspelled constant silently becomes a binding that matches
everything. Truss closes it with errors where Rust warns: such a binding makes
later arms unreachable, or is unused as the last arm, and adding a constant
that turns a binding into a comparison leaves the `match` incomplete. A
constant in a pattern has structural equality, so matching it and comparing
it with `==` agree.

**Imports bring in modules, not names,** so every name shows where it comes
from, two modules can both define `ParseError`, and Truss needs no aliases,
which would let one thing go by different names in different files.

**Every module path starts with a package name,** even inside the package, so
a path is written the same everywhere and found by searching. Relative paths
make one module look different depending on where it is named from.

**Modules may depend on each other in a cycle,** because dependencies are
tracked between definitions, not files.

**Modules have their own namespace, marked by `::`.** Where a module name is
an ordinary name, a variable called `url` hides the module, and with the
no-hiding rule such natural names would be forbidden and an import could
break unrelated code.

**The prelude holds only `UpperCamelCase` names,** so it never clashes with a
variable or function. Adding a name can still clash with a user's type, so the
prelude changes only with a language version, which comes with an automatic
rename.

**Variants live under their type,** so the name shows its type and two types
can share a variant name. In patterns the variant is bare and looked up in
the matched value's type, as a method is in its receiver's.
