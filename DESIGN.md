# Truss Design Decisions

This document records what Truss code means and why. For how code is written,
see [SYNTAX.md](SYNTAX.md). For the goals behind these decisions, see
[GOALS.md](GOALS.md). It describes the language, not a compiler: what
stage0 builds of it, and what it does not yet, is in the documents of
stage0's stages, which [IMPLEMENTATION.md](IMPLEMENTATION.md) lists.

## Source code

- **Text files are the source of truth.** Programmers and tools edit ordinary
  files.
- **A change costs what it changes.** GOALS.md asks that building, testing,
  and proving cost O(change), not O(project). The rules in this section are
  what the language promises so that they can. How the toolchain keeps
  results, and finds what a change reaches, is in
  [DATABASE.md](DATABASE.md).
- **Each top-level definition stands on its own.** What a definition is does
  not depend on where it is in its file, on the definitions around it, or on
  how it is laid out, so reformatting a file, or moving a definition within
  it, changes nothing that depends on it. See
  [What a definition is](#what-a-definition-is).
- **Code refers to other code by name, never by its content.** Unison refers
  to code by hash, so a function's hash covers its callees' hashes, and
  changing one body changes the hash of everything that reaches it. A Truss
  definition names what it uses by module path and name, so changing a body
  changes nothing about what refers to it.
- **A function's signature and body are apart.** Type checking and proofs in
  callers depend only on the signature. Changing a body without changing its
  signature, such as filling in a `todo`, re-checks no callers. Only code
  generation and the affected tests run again. The signature is itself two
  parts: its interface, which callers' types depend on, and its contract, the
  `requires`, `ensures`, `decreases`, and `cost` clauses, which only callers'
  proofs depend on. Strengthening an `ensures` re-proves callers but
  type-checks none of them again.
- **A function's body is part of its package's interface only when the
  function is `transparent`.** Inside a package, the body of a pure function
  with a `time` clause is its definition, which proofs read. In another
  package, proofs read the contract only, unless the function is declared
  `public transparent fn`. A body that other packages' proofs rely on would
  otherwise be part of the interface without being in the signature, and a
  change to it could break their proofs with no change that a reader of
  signatures sees. Verus makes the same choice with `open` and `closed`, and
  Dafny's exports with `reveals` and `provides`. A method that a trait
  provides is read everywhere, because an `impl` in any package inherits it.
  A public contract and a `transparent` body call only public functions and
  name only public constants, as a public specification and an `open`
  function's body do in Verus, and as an exported specification does in
  Dafny: the contract of a function that other packages cannot see is not
  compared between releases. Unlike Verus, a `transparent` body can read a
  hidden field, since a change to the field is a change to the body, which
  is compared.
- **The order of a type's fields is not part of its shape.** Reordering fields
  rebuilds nothing, except code that uses a derived `Ordered`, which compares
  fields in declaration order. The compiler chooses memory layout, and a record
  with more than one field is always built with named arguments, so field
  order is otherwise never observable.
- **A parameter's default is apart from the signature.** The signature
  records only that the parameter has a default. Type checking in callers
  depends only on that, so changing a default re-type-checks nothing. Callers
  that leave the argument out depend on the default itself, so their proofs
  and tests are checked again; callers that pass it are not affected. The
  default is filled in by the function, not copied into each caller, so only
  the function is compiled again.
- **Each derived implementation is its own definition.** `derives Hash` on
  `Point` stands for a separate `impl Hash for Point`. It is made from the
  trait, the shape of `Point`, and the compiler's rule for deriving `Hash`,
  and depends on nothing else. The generated code is never stored. Adding a
  derive changes nothing that already exists. Changing a field re-checks only
  code that compares, hashes, or orders the type.
- **A name is looked up in few places.** A definition depends on the parts
  of the definitions it uses, such as an interface or a shape, and on
  lookups, keyed by where and what name: the members of `List` named
  `length`, the `impl`s of `Add` for `Instant`, the constants named
  `not_found` in a file. A lookup that found nothing is depended on too.
  When a definition is added, removed, or renamed, only the lookups with its
  scope and name are made again. Swift's incremental builds keyed such
  lookups by name alone, and rebuilt far too much. Truss's rules keep each
  lookup to a few places: methods live with their type, an `impl` lives with
  its trait, its type, or a type its trait's arguments name, and an
  unqualified constant can only come from the same file.
- **Renaming or moving a definition redoes little.** Its users name it, so
  their types are checked again, which is cheap. Their proofs, their test
  results, and their compiled code are found already done, because those are
  kept by what the code is and not by what it is called.
- **Positions are relative to their definition.** Panics, `echo`, failed
  asserts, and debug information record where they are within their
  definition, and a table built at the end of the build turns that into a
  file and line. Otherwise adding a line at the top of a file would change
  the output of every definition below it.
- **Development builds do not inline across the definitions being worked
  on.** Inlining one definition into another makes the caller's code depend
  on the callee's body. Development builds inline only from the standard
  library and from registry packages, whose bodies change only with a new
  toolchain or a new version in the lock file, so inlining never widens a
  rebuild while editing. A project's own packages are being worked on,
  whichever of them a definition is in. Cargo users get the same effect by
  hand, by optimizing dependencies in development profiles. Release builds
  inline across everything.
- **Upgrading a dependency costs what the upgrade changed.** A path holds
  no version, so a new version of a package is an edit to code the project
  does not own, and is followed like any edit: a release that changed three
  bodies compiles those again and runs the tests that reach them, and a
  caller whose callees' signatures are unchanged is neither type-checked nor
  proven again. See [Packages](#packages).
- **A new compiler release redoes only what it changed.** Each stage of the
  compiler is versioned on its own: the parser, the type checker, the prover
  with its pinned solver, code generation, and each rule for deriving. A
  release that changes code generation leaves every proof valid, a new
  solver re-proves only what that solver checked, and a release that
  improves a derivation rule redoes only the implementations made with it.

### What a definition is

A definition is its kind, its structure, the names it resolves to, its local
variable names, its literal values, and the order of clauses within each
kind. A change to any of those is a change to the definition, and nothing
else is.

- **Not part of it:** whitespace and layout, the order between kinds of
  clause, its position in the file, and how a literal is written. `0xFF` and
  `255` are the same, and so are a raw string and an ordinary one with the
  same text. The file keeps how each literal was written, so `truss fmt` can
  print it back that way.
- **The order of clauses of one kind is part of it.** Each `requires` may
  rely on the ones before it, as in Dafny, so swapping two of them can
  change what they mean.
- **Field order is part of it only for types with a derived `Ordered`.**
- **Local names are part of it,** unlike in Unison, which hashes no names at
  all. Truss shows local names in compiler messages and `echo` output, and a
  result that ignored them would show an old name. Renaming a local
  re-checks one body.

### What you see is what compiles

The invisible characters behind known attacks are a compile error anywhere in
a source file, including inside strings. They have no other use in source that
an escape cannot serve.

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

This stops the known attacks, not every way of hiding data. A run of
variation selectors after an emoji, or joiners between letters, can still
carry hidden bytes in a string. Closing that would mean rules about where each
of these characters may appear for every emoji and script, which no other
language has, so Truss leaves it to review tools.

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

Statements end at a line break, following Scala's rule: a line break ends a
statement when the token before it can end one and the token after it can
begin one. Go's rule looks only at the token before. Looking at both sides
lets a line start with `.`, `else`, `with`, `|`, `=>`, `->`, the clause
keywords, or a binary operator that cannot begin an expression, and continue
the line before, since none of those can begin a statement. Inside `(` and
`[`, line breaks are ignored, as in Python.

- **It fits how Truss code is laid out.** Clauses sit on the lines after a
  signature, variants start with `|`, and the body's `{` follows the
  clauses. Go's rule alone would forbid all of these.
- **It follows from one principle,** not a hand-kept list. Which tokens
  continue a line falls out of the grammar: exactly those that cannot begin a
  statement. A closing `}` is one of them, so no special case is needed for
  a line break before it.
- **It allows the method chains LLMs write by habit,** with each `.` at the
  start of a line, as in Kotlin, Swift, and Rust.
- **It never guesses.** JavaScript continues a line whenever the next one
  could continue it, so a line starting with `(` silently calls the line
  before. Truss's rule is fixed by the tokens alone. The cases it reads as
  two statements, such as a line starting with `-`, leave an unused value,
  which is a compile error, so they are caught rather than misread.
- **`match` arms are separated by line breaks, like statements,** as in
  Kotlin's `when`, Scala, and Elixir, rather than by commas as in Rust. An
  arm reads as a statement, not as an item in a list, and Rust's commas are
  optional after a block arm, which gives two spellings. The cost is that a
  `match` cannot fit on one line. The `is` expression covers most of what
  one-line matches are used for, such as `if response is Ok(body) { ... }`.
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
  constants. Constants can appear in types, as in `Array[UInt8, digest_size]`,
  and keeping them free of calls means type checking never waits for code to
  run. Rust started with similarly limited constants and has widened them
  release by release without breaking code, and Truss can do the same.
- **Code run while compiling is compiled code.** Tagged-template checks, and
  building the tables of `Map` and `Set` values in constants, run Truss code
  while compiling. That code is compiled and run the way tests are, as Lisp
  compilers call compiled functions and Rust runs compiled procedural macros,
  rather than by a separate interpreter. There is then only one meaning of
  Truss code to keep correct, so results match the compiled program exactly,
  including the size of `USize` on the target. The functions involved are
  almost always in the standard library or a dependency, compiled once and
  cached, and each result is cached by the function and its input. What runs
  only discharges proofs and produces static data, so it never feeds type
  checking.
- **Explicit type arguments use the same square brackets as indexing,** as in
  Go and Nim: `parse[Int64](text)`. Rust needs `parse::<i64>` because `<` is
  also less-than; Truss's brackets have no such clash, so it needs no new
  punctuation. The parser builds the same tree for both, and name resolution
  decides which it is. The no-shadowing rule keeps that decision simple: a
  name means exactly one thing in scope, and only declared functions can be
  generic. For methods, type checking decides, as for every method call.
  Two costs follow. A highlighter that works only from the text can mistake
  `items[Color.Red]` for a type argument, so exact highlighting comes from
  the language server, as gopls provides for Go. And error messages for
  `f[X]` must say which reading applied.
- **Bodies are inferred.** Local variables need no type annotations, and
  lambdas never have them.
- **Each statement settles its own types.** A local's type comes from its
  own `let` or `var`, its annotation and its initializer, and is fixed from
  then on, as in Swift, Kotlin, Scala, and C#. Rust, OCaml, and Haskell
  instead infer across a whole body, so a variable's type can come from a use
  many lines later, and an error can show up far from its cause. In Truss, a
  variable's type is what its own line says, which is what a reader, an LLM,
  and the language server see, and checking stays local and fast. The cost is
  an annotation where a statement alone cannot decide, as in
  `var names: List[String] = []`.
- **Generic code is compiled once for each set of type arguments,** as in
  Rust, C++, and Go, so generics cost nothing at run time. This rules out
  polymorphic recursion: a generic function cannot call itself, or another
  function in a cycle with it, with a type argument built from its own type
  parameters, such as `Option[Element]`, and a generic type cannot contain
  itself with different arguments. Go reports this as an instantiation cycle
  while type checking, and Truss does the same, rather than failing while
  compiling copies, as Rust does.

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
  an effect, and it costs what reading a constant costs. Where the default
  must be an owned value, as for a record field or an `own` parameter, it is
  copied. That is free for numbers, strings, and empty collections, and
  costs one counted allocation for a non-empty `List`, `Map`, or `Set`.
- **Defaults are applied by the function,** as in Kotlin, not copied into each
  caller, as in C# and Swift. C# is known for callers keeping an old default
  after a library changes it. In Truss, changing a default compiles only the
  function again.

### Matching several values

`match state, event { Idle, Start => ... }` matches two values together
without making a tuple, as Racket's `match*` does. State machines and other
code that decides on a pair of values are the main reason other languages
match on tuples, and this covers it without adding tuples. Patterns
correspond to values by position, but only within one `match`, where the
values and the arms are on the screen together. Tuples carry positions through
signatures and fields, which is what Truss avoids.

### Testing patterns

`match` chooses among several patterns. Two smaller forms cover the common
cases where only one pattern matters:

- **`value is pattern` is a `Bool`,** as in C#. One construct covers tests
  (`if response is Ok(body)`), loops (`while queue.pop() is Some(task)`),
  conditions in specifications (`ensures result is Some(_)`), and
  combinations with other conditions (`is Ok(body) && body.length() > 0`).
  Rust reached the same place with three forms, `if let`, `while let`, and
  the let-chains added in Rust 2024. A name bound by `is` can be used only
  where the test is known to be true, which is C#'s rule and Rust's rule for
  let-chains.
- **`let ... else` leaves early when a pattern does not match,** as in Rust
  and Swift's `guard`. C# instead keeps a name bound by `is` usable after an
  `if (!(v is T x)) return;`, which reads awkwardly and lets a name outlive
  the `if` that introduced it. In Truss a name's scope always follows blocks.
- **Float literals are not patterns.** Float `==` treats `-0.0` and `0.0` as
  equal, so a pattern `0.0` would quietly match both. A guard says so
  explicitly.

### Type invariants

A type can declare an `invariant`, a condition that holds for every value of
the type.

- **Facts move from signatures into types.** Every `SortedList` is known to be
  sorted, so functions that take one need no `requires is_sorted(...)`, and the
  prover uses the fact for free. A fact carried by a type cannot be forgotten
  at a call site, because nothing that breaks it can have that type.
- **An invariant belongs to the whole type, never to one variant.** This
  follows Ada's and Eiffel's type invariants. It lets an invariant state
  facts about the whole value, such as a tree being balanced, and it leaves
  no doubt about which part of a type a trailing clause belongs to. A
  condition on one variant is a `match` in the type's invariant, or a field
  whose own type carries the condition, as Dafny and Lean do.
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
- **A private method that takes `mut self` is a step of an update.** The
  invariant of its `self` is neither assumed when it is called nor required
  when it returns, so `SortedList.insert` can call a private
  `SortedList.sift_into_place(mut self, index: USize)` while the list is
  half sorted. Whatever such a helper needs about `self` it states with
  `requires`, and whatever it leaves it states with `ensures`. Every other
  call, and every other parameter, needs the invariant as usual. This follows
  Ada and SPARK, whose type invariants bind only the subprograms code outside
  the package can call, and Eiffel, whose invariants bind only calls on
  another object. Truss draws the line at the narrowest place: methods
  private to a file, and only for the value they change.
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
- **Operating-system resources are released like memory.** Open files,
  connections, and processes are closed when their owner is done with them,
  as in Rust and Swift, so `?` and `return` need no cleanup code. Releasing
  one never runs Truss code: only the standard library's real capability
  implementations create such handles, since there is no foreign code, and a
  test's fake implementation returns plain values. Types cannot define
  destructors.
- **What can fail is explicit, and buffered data is never lost silently.**
  Closing a file that was only read, or a socket, loses nothing, so it
  happens silently. Flushing a buffered writer can fail, and losing its data
  would go unnoticed, which is how Rust's `BufWriter` loses writes when it is
  dropped. So a buffered writer is only ever lent, inside a scope:
  `files::write_with(path, write: fn(writer) { ... })` lends the writer
  `mut` to the function, then finishes it, and returns the first error from
  the function or from finishing. This is Python's `with`, Kotlin's `use`,
  Java's try-with-resources, and Ruby's `File.open` with a block. User code
  never owns a writer, so it can never drop an unfinished one, and `?` inside
  the function needs no cleanup. Linear types, as in Austral and Vale, could
  instead let a writer be owned and stored, but every `?` while one is open
  would drop it, and generic code would need to say which of its type
  parameters it never drops. A wrapper such as a compressing writer takes
  the output `mut` on each call, or lends a writer of its own the same way.
  Closing a connection that a pure function dropped is visible to the other
  end, as when a process exits, but never to the program.
- **There is no mutable global state.** Values defined at the top level are
  constants. Anything that changes lives in a variable, a parameter, or a
  capability implementation, so all state a function can touch is visible in
  its signature. This is also why many tests can safely share one process.
- There are no lifetime annotations. The only references are read-only views,
  and they never outlive the function that made them (see below).
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
- **A mark covers the longest place it can.** In `mut config.servers.sort()`,
  the place is `config.servers`, not all of `config`, so other fields of
  `config` stay usable at the same time. This is Rust's definition of a place
  expression, without dereferencing, which Truss does not have. The mark goes
  to the first method call after the place; later calls in the chain work on
  temporaries.
- **A field can be moved out on its own,** as in Rust. After
  `own config.name`, the rest of `config` stays usable, and `config` as a
  whole is usable again once `config.name` is assigned. Without this, taking
  one field from a record would mean copying it or giving up the whole
  record. The check stays inside one function, like every other check on
  modes and views.
- **Recursive types say where they allocate.** A `Tree` whose `Node` holds
  two `Tree`s would be infinitely large if held in place, so such a variant
  is marked `indirect` and keeps its fields on the heap, in one allocation,
  as with Swift's `indirect`. Building one costs one allocation, which cost
  clauses count. Changing it in place or moving parts out allocates nothing.
  Rust says the same thing with `Box`, which every pattern then has to reach
  through. Swift's mark keeps patterns unchanged. A cycle of types with no
  `indirect` variant, and not through a collection, is a compile error whose
  fix adds the mark, so the allocation is written where the type is
  declared.
- **Implicit copies never allocate.** A type made only of fixed-size data
  with nothing on the heap (integers, floats, `Bool`, and records or sum types
  built only from those) copies implicitly, because copying it is a plain
  memory copy. Every other type, such as `List`, `String`, or anything that
  contains them, needs an explicit `copy()`, so the cost of copying shows in
  the code. The compiler works out which types copy implicitly from their
  fields; there is nothing to declare, except on opaque types (below).
- **Some types cannot be copied at all.** Copying an open file, a connection,
  or a process would duplicate an operating-system handle, which can fail,
  and `copy()` cannot fail. So `copy()` exists for every type except the
  standard library's handles and the types that hold one. A connection pool,
  `List[Connection]`, is still an ordinary list; it just has no `copy()`.
- **Generic code says what it copies.** Two prelude traits, which the
  compiler implements and no `impl` can, state these facts: `Copyable`, which
  gives `copy()`, and `Plain`, which copies implicitly and requires
  `Copyable`. Generic code copies only when a bound says it may, as in
  `fn repeat[Element: Copyable](value: Element, count: USize)`, so a plain
  `[Element]` accepts every type, handles included. Rust's `Clone` and `Copy`
  bounds work the same way. The names avoid Rust's, because Rust's `Copy`
  means implicit while Truss's `copy()` is explicit; Mojo, which also has a
  `copy()` method, names its trait `Copyable`. A generic type has them under
  the same conditions as its parts: `List[Element]` is `Copyable` when
  `Element` is, and `any Trait` is `Copyable` only when `Trait` requires it.
- **Opaque types declare whether they copy.** Inferring it from an opaque
  type's fields would let other packages depend on fields they cannot see:
  adding a `String` field to an opaque type would break a package that
  relied on it copying implicitly. So an opaque type is `Copyable` or `Plain`
  only when it says so, with `derives Copyable` or `derives Plain`, which the
  compiler checks against its fields. Swift requires public types to declare
  `BitwiseCopyable` for the same reason. Other types show their fields, so
  changing those is visibly a change to the API already, and their copying
  stays inferred.
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
- **Being a view is a property of a type.** `Slice`, `StringSlice`, a cursor
  over a collection it does not own, and a lambda that captures locals are
  views, and so is any type that holds one anywhere: in a field, a variant,
  an element, or a type argument. `Option[Slice[Int64]]` is a view, and so is
  the record `split_at` returns. The compiler works this out from the type,
  as it does for implicit copies, so nothing is declared. Swift's
  nonescapable types (`~Escapable`) are the same idea.
- **Views never outlive the function that made them.** A value of a view
  type can be bound, held in local records and collections, and passed as an
  argument, but it cannot be returned except as below, and cannot go where
  an owned value that may be stored is required. Putting a view into a
  record or a list makes the record or list a view, so a view can never be
  stored past its function. Every type that is not a view type is
  `Storable`, a trait the compiler implements, so generic code asks for a
  value that may be stored with a bound, as in `Channel[Message: Storable]`.
  An `any Trait` does not name the type of the value it holds, so it is a
  view type unless `Trait` requires `Storable`.
- **A call's result views what its arguments view.** A function may return a
  view only of what reached it through its parameters, never of its own
  locals. The caller then treats the result as viewing everything its
  read-only and view-typed arguments view, so it needs no annotation.
  `text.trim()` views `text`, and `cached.unwrap_or(default: backup[..])`
  views both `cached` and `backup`. Rust instead names which input a result
  borrows from with lifetimes, and Swift with lifetime-dependence
  annotations. Truss's rule is coarser but needs neither, and arguments of
  plain data, such as indexes, lend nothing, so it rarely holds more than it
  must. A rule that only views of `self` can be returned would not be
  enough: generic code such as `Option.unwrap_or` returns a value of its
  parameter's type, which is a view whenever `Option` holds one.
- **A `var` can hold a view that never leaves its function.** A view still
  cannot outlive what it refers to, which is the reason for the rule against
  storing views. A cursor over a collection needs a `var`, because pulling a
  value changes the cursor.
- **`mut` access is never stored.** It is named only by a `mut` parameter, a
  `mut` loop's variable, or a lambda's `mut` parameter, and lasts only for
  that call, iteration, or `provide mut` block, so there is no mutable
  reference to track across statements. Disjoint parts of one `List`,
  `Slice`, or `Array` can still be passed `mut` side by side, because the
  prover shows the ranges do not overlap.
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
and the first change copies it to the heap. Only methods that write bytes,
such as `push`, can change a `String`, since strings cannot be indexed, and
those may allocate anyway, so cost clauses already account for that copy.

**Constants are read-only places.** Reading a constant or taking a view of
it costs nothing. An owned value from a constant is made with `copy()`, as
from any other place, so its allocation is written and counted. Rust's
`static` works the same way. Swift instead copies on the first write to any
collection, which would mean every in-place change, such as `items[i] = x`,
checks for static memory and might allocate. No `cost allocations == 0`
promise could then be proven for code that changes a collection it was
given.

### Lending and yielding methods

A method can give its caller parts of `self` without returning a stored
reference, which would need lifetimes. It does so in one of two ways, and its
signature says which:

- **`lends` gives out one part, exactly once,** and then continues, as
  Hylo's subscripts and Swift's `_read` and `_modify` accessors do. This is
  how `items[i]` and `mut grid[position].visit()` work.
- **`yields` gives out any number of parts,** one after another, as C#'s and
  Python's generators do. This is how `for` loops and cursors work.

The two behave differently for the caller, so the signature must say which.
A lending method is proven on the promise that it always continues after its
`yield`, while a loop may stop at any `yield` and never continue. A call to a
lending method in an expression is the part, while a call to a yielding
method outside a `for` loop is a cursor. If the body decided which, as by
counting its `yield`s, a body edit could change what callers mean, and
callers could break a lending method's proof by looping over it. Swift and
Hylo also keep accessors apart from sequences, and Python's
`@contextmanager` marks a generator that yields once.

- **User collections are not second-class.** `[]` and `for` work through the
  `Index` trait and `each`, so a user's `Grid` supports
  `mut grid[position].visit()` and `for cell in mut grid` exactly as a `List`
  does, with the same proof rules. The one difference is two parts lent side
  by side, below.
- **What a lending method lends need not be stored in `self`.** It may be a
  value the method made, which the method takes back after the caller's
  statement, as Swift's and Hylo's accessors may. So a collection that packs
  its elements, such as a set of bits, can still be indexed: its `at` makes
  the `Bool`, lends it, and writes it back. Rust's `Index` returns a
  reference, so there such a collection cannot be indexed at all.
- **A lending call lends the whole of what it is called on,** for the rest
  of the caller's statement: read-only when the method takes `self`, and
  `mut` when it takes `mut self`. The method is waiting to go on, and it was
  proven as if nothing else touches `self` until it does. So the statement
  makes no other use of a place it is lent from `mut`, and does not change
  one that is lent read-only. `mut grid[a].swap(mut grid[b])` is an error
  for a user's `Grid`, as it is for every collection in Swift, Hylo, and
  Rust, which offer `swapAt` and `split_at_mut` for it.
- **`List`, `Slice`, and `Array` lend two parts side by side.** Their
  elements are places the compiler knows, and their `at` has nothing left to
  do after its `yield`, so two indexes or two slices of one of them can be
  lent together, `mut` or not, when the prover shows they are apart.
- **A part that is lent is not the caller's to keep.** It cannot be given
  up, and a name cannot hold it past the statement, though a `Plain` part
  is copied as any `Plain` value is. A part lent `mut` is changed with no
  mark of its own, since the mark is already on the place it is lent from:
  `mut grid.cell(position).visit()`.
- **A lending method yields exactly once on every path, and always
  continues afterward,** even if the caller's statement leaves early, so a
  type can update what depends on the part, such as a cached total. The
  compiler checks that there is exactly one `yield` on every path, as Swift
  does for its accessors. A lending method cannot drive a `for` loop or be
  pulled.
- **A loop can stop at any `yield`, and the method does not continue.** Python
  generators run `finally` blocks when a loop stops early; Truss has no
  `finally`, and continuing to the next `yield` would do unasked-for work,
  such as reading one more line from a file after `break`. So the prover
  treats every `yield` in a loop as a point where the method may end, and
  requires invariants to hold there. A type whose invariant depends on its
  elements in a way that changing one would break, such as a sorted list or a
  cached total, offers read-only and owned loops, and changes single
  elements through a lending method.
- **The contract says what is yielded.** In a lending or yielding
  method's `ensures`, `result` names the part being yielded, so a clause
  that mentions it holds at each `yield` and is what the caller's statement
  or loop body may rely on: `List`'s `each` promises
  `ensures identical(result, self[yielded.length()])`, and a range's promises that
  each value lies within it. Clauses that do not mention `result` hold
  wherever the method ends. `yielded` names the parts yielded so far, as
  a `Sequence`, each as the caller left it, and `finished` is `true` when the
  method ran to its end rather than stopping at a `yield`. So
  `ensures finished ==> yielded.length() == self.length()` is how a loop over
  a list is known to run once per element, and a `lends mut` method states
  how `self` takes back the part with `yielded[0]`. A `for` loop's
  clauses may name `yielded` too, for the values of the iterations
  before. Dafny's iterators work the same way, with clauses for each
  `yield` and a ghost history of what was yielded, and Creusot calls the
  history `produced`. The facts of `for item in items` come from the
  contract of the list's `each`, so a user's collection gets exactly the
  same facts as a `List`. A range of integers is the one loop the prover
  knows itself, and in its clauses the loop variable names the next index,
  as in Dafny's and Why3's `for` loops: `kept <= index` in place of
  `kept <= yielded.length() + 1`.
- **Read-only and owned yields can be pulled.** Internal iteration alone, as
  in Ruby's `each`, cannot advance two sequences together, so it cannot
  write `zip`, merge, `peek`, or pause and resume. Pulling a yielding method
  through a cursor gives those, as C#'s iterators and Python's generators
  do. The same rule covers both uses: a method may end at any `yield`.
- **A pull yields an owned value.** So a read-only yield of a place,
  such as a list's element, is pulled only where the element is `Plain`.
  Anything else would be copied unasked, and is looped over with `for`
  instead, or pulled from a method that yields owned values.
- **`mut` yields cannot be pulled.** A cursor would hold `mut` access between
  pulls, which is a stored mutable reference. Changing two collections in
  lockstep goes through indexes.
- **A method that yields through recursion can be looped over but not
  pulled.** A tree's `each` that loops over its subtrees and yields what
  they yield is ordinary recursion in a `for` loop. A cursor over it would
  need room for every level of the recursion. C#, Python, and Kotlin
  allocate that room behind the scenes. Truss reports the `next()` call
  instead, and a cursor over such a structure is written as a type with an
  explicit stack, as in Rust and Swift, so its allocations are visible.
  Whether a method can be pulled is worked out from its body. It is one of
  two facts callers take from a body rather than a signature; the other is
  whether the prover reads a pure function's body as its definition (see
  [Verification](#verification)). The tools show both with the signature. Early cutoff means a body edit that keeps the
  method pullable re-checks no callers.
- **Cursor types have no name, as in Rust and Swift.** A cursor is a state
  machine the compiler makes from one method, so its type is described by the
  prelude trait `Cursor`, which hand-written cursors implement too. Code that
  holds a cursor is generic over it, which costs nothing, or uses
  `any Cursor`, which allocates once and shows it. Returning a cursor without
  allocating would need opaque result types, Rust's `impl Trait` and Swift's
  `some`. They can be added later without breaking code if they are needed;
  most of what they are used for is a yielding method in Truss.
- **Compilation needs no coroutines at run time.** A loop or a lending call
  compiles to a call that receives the caller's code as a function, which
  inlining makes as cheap as a written-out loop, as in Swift and Hylo. A
  pulled cursor compiles to a state machine, as C# and Kotlin compile their
  iterators.

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
- **A function says what it passes its callback.** A lambda's parameters
  have no annotations, so on its own a lambda knows nothing about its
  arguments, and `indices.map(fn(i) { values[i] })` could not prove its
  index. So the type of a function-typed parameter can carry a `requires`
  over named inputs and the parameters before it, as in
  `transform: (fn(element: Element) -> Output requires self.model().contains(element))`.
  The function must meet it at every call it makes through the parameter,
  and a lambda passed there may rely on it. The names exist only for the
  `requires`; calls through function values stay positional. This is the
  refinement on a function's argument that F* and Liquid Haskell write as
  `(x: int{x < n}) -> int`, and the precondition Dafny and Verus give a
  lambda, stated by the callee, since Truss's lambdas are never annotated.
  It is allowed only on a parameter's type, where a callee states what it
  passes, so it never becomes part of a type that values are stored in or
  compared by.
- **Behavior with state is a record with a trait**, not a closure. A
  `make_adder(5)` that returns a closure becomes `Adder(amount: 5)` with an
  `impl`.

- **`return` in a lambda leaves the lambda,** as in Rust, Swift, and Go. A
  lambda is a function, and Kotlin's non-local `return`, which leaves the
  enclosing function from inside an inline lambda, is a well-known source of
  confusion. `break` and `continue` cannot cross a lambda for the same reason.
- **A lambda's types come only from where it is used.** Its parameter
  types, modes, and result type are never written; they come from the
  function type it is passed as, and are worked out from the outside in.
  Elm does the same. Rust allows annotations on closure parameters and often
  needs them, because it checks a closure's body before it knows the
  parameters' types; "type annotations needed" is one of its most common
  errors. Never inferring a parameter's type from the body keeps checking
  local and fast. When there is no context, the type goes on the `let` or
  on the call's type arguments. Modes are inferred too: writing `mut` at a
  call site shows what happens to an existing value, and a lambda's
  parameter is a new name, not an existing value.
- **There is one way to write a lambda,** `fn(parameters) { body }`, as in
  Gleam. A block's value is its last expression, so a short form such as
  JavaScript's `x => x * 2` would add nothing but a second spelling, and the
  braces mark exactly where the body ends. Kotlin's `it`, Swift's `$0`, and
  trailing lambdas such as `items.map { it.name }` are popular, but `it` and
  `$0` are not whole words, and a trailing lambda is a second way to pass an
  argument.

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
- **A method is its name and how it takes `self`.** The versions of one name
  need not be written in one place. A `List` gets `each(self)` from
  `Iterable`, which generic code is written against, and has an
  `each(mut self)` and an `each(own self)` of its own, which a set or a
  range could not offer. A trait that requires another can add a version in
  the same way. A call picks its version among all of them by its mark, so
  there is still exactly one method for each name and each way of taking
  `self`. The cost is that the versions of one name can be in two places,
  a type's own methods and an `impl`.
- **Versions merge only where one author wrote them as one method.** Three
  things are one author's: a type's own methods, the methods an `impl` in
  the type's own package writes, and a trait with the traits it requires.
  Picking by mode among everything visible would let code added elsewhere
  take over a call without an error. On a temporary the `own` version is
  chosen when there is one, so if a second package could give a type's
  `label(self)` a `label(own self)` through a trait of its own,
  `Counter(3).label()` would change which method it means when that package
  was added. A method that an `impl` leaves to the body its trait provides
  is no different: a later release of the trait can add one. So an `impl`
  outside a type's package cannot use a name the type's methods have, an
  `impl` inside it can only by writing the method, and two unrelated traits
  that share a name are still told apart only by writing the call in full.
- **Traits can take type parameters, which covers what overloading is mostly
  wanted for.** `Int64.from(count)` picks an `impl` of `From[Source]` by the
  type of `count`, and `instant + duration` picks an `impl` of
  `Add[Duration]`. Free overloading by parameter type would cost what Truss
  cares about most. Swift's "expression too complex to type-check" errors
  come from overloads combined with literals typed by context, which Truss
  also has. Adding an overload anywhere can change which function an existing
  call resolves to, which widens what each definition's results depend on. And
  a reviewer cannot tell which `process` runs in `process(item)` without
  knowing the type of `item`. Traits with type parameters avoid these:
  - **Argument types are settled first.** The types of the arguments are
    worked out without looking at which `impl`s exist, and only then is the
    one matching `impl` found. A literal takes the type of the other operand
    of an operator when it can, and otherwise its default type (see
    [Integers](#integers)), so `count + 1` adds two `UInt8`s while
    `duration * 2` multiplies by an `Int64`. Adding an `impl` never changes
    an existing call.
  - **Nothing is chosen from the expected result.** Truss has no `into()`,
    whose target Rust infers from context and which is a common source of
    inference failures. The target is always named.
  - **The candidates are fixed.** An `impl` lives with its trait, its
    type, or a type its trait's arguments name, so no third package can add
    one that changes a call.
- **Mixed-type arithmetic goes through these traits.** Times, geometry,
  physics, and money need `instant + duration` and `vector * 2.0`, so the
  arithmetic operators use `Add[Right]` and similar traits, with the result
  as an associated type. Comparisons stay between values of one type,
  because the laws of `Equal` and `Ordered` relate a type to itself.
- **An operator trait says where its operation is defined.** `Int8`'s `+`
  is not defined where the sum overflows, and its `/` is not defined for a
  divisor of 0. If `Add.add` promised a result for every pair of values, an
  `impl` for a fixed-width integer would have to wrap or to crash, and
  generic code could overflow with nothing in its signature to show it. So
  each trait has a second method, such as `add_is_defined`, and the
  operation requires it. Generic code then carries the obligation that an
  operator on a built-in type has, as `Index.at` requires `contains_key`.
  Verus gives Rust's `Add` a precondition, `add_req`, for the same reason.
  A type whose operation is defined everywhere returns `true`.
- **Associated types are chosen by each implementation,** as in Rust: the
  key and result of `Index`, the element of a collection, the part type of
  `FromTemplate`. A trait's type parameters are what an `impl` is chosen by,
  and its associated types are what each `impl` decides. Swift's protocols
  have only associated types; Truss also needs type parameters for `From`
  and the operators.
- **Overloading by argument labels may come later.** `Rectangle(width:,
  height:)` beside `Rectangle(side:)` could be resolved from the call's text
  alone, but it interacts with defaults and the optional first label, and
  named constructors cover it for now.
- **Trait methods need no import.** Forgetting to import a trait is a common
  error in languages that require it. Name clashes between traits are reported
  at the call site and fixed by writing the call in full.
- **Only traits from nearby packages are found by a dot.** A dot-call
  considers traits from the standard library, the calling package, and the
  packages its manifest lists, never ones further away. Swift let extension
  members leak to every module that imported the module defining them,
  even indirectly, so a change deep in the dependency graph could break
  distant calls; its "member import visibility" change (SE-0444) limits them
  to direct imports. Truss uses the manifest for the same limit.
- **A clash between names is always an error, never a silent choice.** Rust,
  Kotlin, and C# let a type's own method win over a trait's or extension's
  method with the same name, so adding a method can silently change what an
  existing call does. In Truss, a type's own method and a trait's method
  that are the same one, by name and by how they take `self`, are an error
  at the `impl`, as is any shared name when the `impl` is outside the type's
  package, and two unrelated traits with the same method name are an error
  at the call. Upgrading a dependency can therefore
  break a call only with an error that names both sides, never by changing
  what it does. Adding a public method to a type can so break another
  package's `impl`, with an error whose fix is a rename. A release that only
  adds names is still a compatible one (see [Versions](#versions)), as in
  Go's compatibility promise and Rust's rules for minor releases: otherwise
  no type could ever gain a method.
- **Each type has at most one implementation of a trait,** for each set of
  the trait's arguments.
- **An `impl` lives with its trait or with a type it names.** It must be in
  the package of the trait, of the implementing type, or of the outermost
  type of one of the trait's arguments. So `impl Multiply[Vector] for
  Float64` can live with `Vector`, which is what `2.0 * velocity` needs, and
  `impl From[UserId] for Int64` with `UserId`, which is what
  `Int64.from(user_id)` needs. This is Rust's orphan rule, simplified.
  Packages cannot depend on each other in a cycle, so for any pairing of
  types only one package can name them all, and there is never more than one
  place an `impl` could be. Only the outermost type counts, so
  `From[List[UserId]]` cannot be implemented for `Int64` in `UserId`'s
  package, as in Rust.
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
- **Only structural equality lets the prover substitute.** A type's equality
  is *structural* when two equal values cannot be told apart by any
  function, so from `a == b` the prover may conclude `f(a) == f(b)`. That
  holds for the built-in integers, `Bool`, `Character`, `Unit`, and
  `String`, for `Integer` and the other types of specifications, and for a
  type that derives `Equal` when every one of its fields has structural
  equality. A hand-written `Equal` only promises an equivalence, so the
  prover does not substitute through it, and neither does a derived one with
  a field that is not structural: a `Point` of floats derives a lawful
  `Equal`, yet `Point(x: 0.0, y: 0.0) == Point(x: -0.0, y: 0.0)` while
  `1.0 / x` tells them apart. Outside its package, an opaque type's
  equality is never structural, since whether it is depends on fields other
  packages cannot see. This is Rust's rule for constants in patterns, which
  must be "structural-match": derived equality all the way down. Like
  copying, it is worked out from the type's shape, so nothing is declared,
  and a change to it re-checks the proofs that relied on it.
- **Float equality is lawful.** IEEE's `NaN != NaN` breaks reflexivity, and
  Truss proves its laws rather than ignoring them as Swift does. So `==` on
  floats treats all NaNs as equal and otherwise follows IEEE, which keeps
  `-0.0 == 0.0`. NaN is ordered after every number. `ieee_equal` gives exact
  IEEE behavior when numeric code needs it. Float equality is not
  structural, so the prover never substitutes through it, which matters
  because
  `-0.0 == 0.0` while `1.0 / -0.0 != 1.0 / 0.0`. The solver's floating-point
  theory, which distinguishes IEEE equality from identity in the same way,
  checks it directly. Lean instead gives floats no lawful equality, which
  would stop a `Point` of floats from deriving `Equal`. SPARK proves NaN never
  occurs, which would make every float division a proof obligation.
- **Lawful float comparison costs a little.** Treating every NaN as equal
  turns `a == b` into roughly `a == b || (a != a && b != b)`, and ordering
  NaN last adds a similar test to `<`. That is a few instructions per
  comparison, which can matter in a hot loop or for vector instructions. The
  `ieee_` comparisons are the exact, single-instruction escape hatch. Making
  floats IEEE by default would instead cost what Rust pays: floats that
  cannot be sorted, used as map keys, or compared in a derived `Equal`.
- **`serialization::Serialize` and `serialization::Deserialize` can be
  derived,** as Rust's serde, Swift's `Codable`, and Kotlin's
  `@Serializable` are. Their methods are generic over a `Serializer` or a
  `Deserializer`, so one derived implementation writes to and reads from
  every format: JSON, TOML, and any that a package adds. A record is
  written as its fields by name, in declaration order. A variant with no
  fields is written as its name, and a variant with fields as a record of
  them under its name, which is serde's default form. A field with a
  default may be missing when it is read, and a missing field of type
  `Option` reads as `None`. A format may rename every field, as
  `json::Names.CamelCase` does. A type that needs other names writes its
  `impl`, since Truss has no attributes to rename one field.
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
- **A method with a body can be replaced only by a version proven to give
  the same result.** So `a != b` always means `!(a == b)`, `max` always
  agrees with `compare`, the prover reasons from the trait alone, and adding
  an `impl` never changes what such a method means. A type can still swap in
  a faster version, as Swift's standard library does through "customization
  points" such as `underestimatedCount`. This is what Rust's specialization
  is mostly wanted for, without overlapping impls. Fast paths that depend
  only on how a type is stored, such as copying a list of plain data with one
  memory copy, need no language feature: the compiler knows which types copy
  implicitly. A replaceable method is one the prover reads as a definition
  (see [What a function means to the prover](#what-a-function-means-to-the-prover)),
  and the replacement proves that its result equals the provided body's, so
  the trait never repeats its body in an `ensures`.
- **An `impl` can promise more than its trait.** An `impl`'s method may add
  `ensures` and `cost` clauses of its own, which it proves, and may state a
  `requires` that the trait's `requires` implies. A call the type checker
  resolves to that `impl`, such as `grid[position]` on a `Grid`, is proven
  against the `impl`'s contract; a call through a bound or through `any` is
  proven against the trait's. This is behavioral subtyping, as Dafny allows
  for a class's method that overrides a trait's: a weaker precondition and a
  stronger postcondition. It is what lets a generic trait such as `Index`
  say nothing about what is lent, while `List`'s `impl` says exactly which
  element. A tag's `from_template` is the one method whose `requires` may
  ask for more than its trait's, since what it asks of a template's
  literal text is the point of the tag: a template always names its tag,
  so it is proven against the tag's `impl`, and a call of `from_template`
  through a bound or through `any`, which could not see what the tag
  asks, is an error.
- **Each type has at most one `impl` of each trait,** whatever its type
  arguments: `impl Display for List[Element: Display]` cannot sit beside
  `impl Display for List[String]`. Rust's long-stalled specialization feature
  comes from allowing such overlaps. Starting strict leaves room to relax the
  rule later without breaking code, should real code need it.

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
- **An `any` type fixes every associated type** of its trait, as in
  `any Cursor[Element = Int64]`, as Rust requires of `dyn`. A method that
  mentions an associated type could not otherwise be called.
- **Limits apply to calls, not traits.** Methods that need the concrete type,
  such as `Equal.equal(self, other: Self)` or a constructor, cannot be called
  through `any`. The compiler reports this at the call, so a trait never
  becomes unusable with `any` just because one of its methods doesn't fit, as
  with Rust's object-safety rules.
- **Dynamic calls are verified through the trait.** Contracts and costs written
  on a trait's methods bind every `impl` and are proven for each one. The
  prover handles a call through `any` from the trait's signature alone, so
  `requires`, `ensures`, laws, costs, and capabilities all still hold. Adding a
  new `impl` checks only that `impl`, never the callers. What an `impl`
  promises beyond its trait helps only calls that know its type.
- **No downcasting.** An `any Handler` cannot be tested for or converted back
  to its concrete type. Code that needs to know which type it has is dealing
  with a closed set, and a sum type expresses that better, with exhaustive
  matching.

## Operator precedence

Precedence is a partial order, as in Carbon. Operators have a relative
precedence only where languages agree on one, such as `*` over `+` and
comparisons over `&&`. Every other combination needs parentheses.

- **Bitwise operators and shifts combine only with themselves.** C puts `&`
  below `==`, so `flags & mask == 0` tests `mask == 0`; Ritchie later called
  this a mistake. Rust fixed that case but still orders `a & b | c` and
  `a << b + 1` silently, and Go and Swift order them differently again. An
  LLM trained on all of them cannot be trusted to remember one table, so
  Truss has no table for these and asks for parentheses, which Rust's Clippy
  and Go's vet already recommend.
- **`&&` and `||` cannot be mixed,** for the same reason.
- **`!` directly before the left operand of `is` needs parentheses.**
  `not x is y` negates the test in Python, and `!x is T` negates the value
  in C#, Kotlin, and Swift, as `!x instanceof T` does in JavaScript, where
  linters report it. So `!response is Ok(_)` means nothing in Truss: write
  `!(response is Ok(_))` or `(!response) is Ok(_)`.
- **Comparisons do not chain.** `a < b < c` means something different in
  Python than in C, so it means nothing in Truss.
- **`echo` covers everything after it,** like `return`, so adding `echo` in
  front of an expression shows that whole expression.
- **Ranges bind more loosely than arithmetic,** as in Swift, so
  `0..count - 1` means what it looks like.
- **Compound assignment (`+=`) exists, but `++` and `--` do not.** `+=`
  writes a place once, so a long place cannot be mistyped the second time,
  and an index is proven in bounds once. Swift removed `++` and `--` while
  keeping `+=`, because as expressions they were confusing and rarely
  clearer than `+= 1`. Rust adds separate traits such as `AddAssign` so that
  `matrix += other` can work in place. Truss needs none: the old value is
  handed to the operator as owned, and an `own self` version of the
  operator's method can reuse its memory. `truss fmt` writes `x = x + y` as
  `x += y`, so code converges on one form.
- **An assignment evaluates its right side before its target,** as Rust does
  for `=` and for compound assignment of built-in types. The operator of a
  compound assignment takes the target's old value as owned, so the target
  holds no value until the result is stored. Evaluating the operand first
  keeps every other piece of code out of that window: a `?` in the operand
  cannot return with the target moved out, and the operand cannot read or
  mutate a moved-out target. Java, C#, and Go evaluate the target first. For
  `=` either order is sound, and Truss uses one rule for both forms.
- **Integer division rounds toward zero, and `>>` on a signed integer copies
  the sign bit,** as in C, Rust, Go, and Swift and as the hardware does.
  Rounding down is available as a method, as Rust's `rem_euclid` is.

## Integers

- **`USize` is used for sizes, lengths, and indices.** A length can never be
  negative, and a bounds check is a single comparison (`index < length`).
  **`ISize` is used for offsets and the distance between two positions.**
- **Code is verified for every width `USize` can have.** `USize` and `ISize`
  have 32 or 64 bits, and the prover knows only that, so a proof holds on
  every target and its result needs no target in its key. A literal or
  constant of either type must fit in 32 bits, except in the standard
  library, which holds each platform's code and its bounds, such as
  `USize.maximum`. Verus treats `usize` the same way by default. A package that runs only on 64-bit targets says so in its
  manifest with `usize_bits = 64`, and its code may then rely on 64 bits, as
  Verus allows with `global size_of usize == 8`. Building such a package for
  a 32-bit target is an error, and a package that does not say so cannot
  depend on one that does, so a package that claims to run everywhere does.
- **Integer types never convert implicitly.**
- **Literals take their type from context, with no suffixes.** `3` can be any
  integer type, so there is one way to write it, and `let small: UInt8 = 3`
  needs no `3u8`. When nothing decides the type, it defaults to `Int64` or
  `Float64`, which keeps simple local variables free of annotations. An
  integer literal is never a float, so `1` and `1.0` always look different.
- **A literal in an operator takes the other operand's type,** as Go's
  untyped constants do. In `count + 1`, `index == 0`, and `0..count`, the
  literal has the type of the other side, when it can be that type. When it
  cannot, as in `duration * 2`, it has its default type. An expression made
  only of literals waits for the same decision, so `count + (60 * 60)` works,
  and a literal shift amount is a `USize`, as Go's is a `uint`. The rule
  never looks at which `impl`s exist, so adding one never changes which a
  call uses. Rust instead lets `impl` search decide a literal's type, so an
  `impl` added later can make an existing call ambiguous.
- **A leading zero is an error, not octal and not ignored.** `0755` is octal
  in C, Go, and shell, and the obvious use is file permissions. Reading it as
  decimal 755, as Rust and Swift do, would silently give the wrong
  permissions, so Truss rejects it as Python 3 and JavaScript's strict mode
  do, and octal is always written `0o755`.
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
   `items.get(index)` or `checked_divide`.
4. **Declare `uses Panic`**, which allows a runtime failure and shows it in the
   signature.

`requires` clauses are always proven at compile time at every call site. They
never become runtime checks.

**Tests do not wait for proofs.** A program is built only once every
obligation it can reach is proven, but a test build checks at run time
every primitive operation that could fail: each index and slice, each
operation that could overflow, each division, shift, and `unreachable`, and
each call of the C library.
Generated code never has undefined behavior, even where a proof is still
running or has failed, so tests run as soon as the code type-checks,
alongside the prover rather than after it. A failed check ends the test and
names the operation, which tells an agent at once whether a failed proof is
a real bug or a prover that needs a hint. Because a test build checks every
operation whether or not it was proven, its code and its cached results do
not depend on the state of any proof. Rust and Swift check indexes and
overflow at run time in every build; Truss does so only where a check is
still useful, in tests, and proves them away in the programs it ships.

**No clause is evaluated when a program runs.** A `requires` clause, an
`ensures` clause, and an invariant are the prover's to show. Running a
`requires` would pay for its proof a second time, at whatever the clause
costs: a test build would make `binary_search` linear by checking that its
list is sorted. Each check that a test build makes takes constant time. A
call that breaks a `requires` is caught where it reaches a primitive, as an
index past the end of a list is, and otherwise by the prover alone. A
SPARK build does the same by default: it keeps the language's own checks
and leaves contracts to the prover.

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
  as `(fn(Request) -> Response uses Database, Log)`. The compiler then
  guarantees no request can crash the process. If the whole process fails, a supervisor
  such as systemd or Kubernetes restarts it.
- **Tests cannot expect a panic.** A test that passes only when code crashes
  would treat crashing as intended behavior, which is what `Result` is for.
  Misuse that other languages test this way, such as breaking a precondition,
  cannot compile in Truss, because `requires` is proven at every call site.
  Error cases are tested as values, as in
  `assert parse(text) == Err(ParseError.Empty)`. To check that a program
  crashes on bad input, an external test runs the built program through the
  `Processes` capability and checks its exit code.
- **A failed `assert` is not a panic.** `assert` is only allowed in
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

**Float results are the same on every platform.** The operations IEEE 754
defines exactly, such as `+`, `*`, `sqrt`, and `fma`, compile to hardware
instructions and are never contracted or reordered. Functions such as `sin`
and `exp`, and converting floats to and from text, are written in Truss in
the standard library rather than taken from the platform's C library, whose
results differ between systems and versions. Java's `StrictMath` and Go's
`math` package do the same. A cached test result therefore holds on every
machine, and code run while compiling gives exactly what the compiled program
gives. `to_bits()` returns one bit pattern for every NaN, as Java's
`doubleToLongBits` does, because processors disagree about which NaN an
operation produces.

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

**Every variable must be used, and every `match` arm must be reachable.** A
binding nothing reads, or an arm earlier arms already cover, is a compile
error, where Rust and Swift only warn. Go makes unused variables errors for
the same reason: such code is almost always a mistake, often a typo. These two
rules are also what make constants safe to use by name in patterns.
Parameters are exempt, because a trait implementation may not need every
parameter the trait declares. For the same reason an unused import is an
error, as in Go.

**Unreachable code is an error,** as in Java, where Rust, Swift, C#, and
Kotlin only warn. A statement after a `return`, a `break`, a `continue`, an
`unreachable`, a call that returns `Never`, or a `while true` that is never
left can never run, and is almost always a line left behind by an edit. The
check uses types alone: after an expression of type `Never`, the rest of the
block is unreachable. It never reasons about values, so `if false { ... }` is
not reported. `todo` is the exception: code after a `todo` is unfinished, not
dead, and is still checked as far as it can be.

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
- **A view never crosses into or out of an implementation's state.** A
  capability's method keeps no view that it is given and returns no view of
  its own state. A caller cannot see which implementation its call reaches,
  so it could not know that a view it passed is still held. A view of the
  implementation's storage would be left viewing what a later call
  replaces.
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
- **A trait can leave a set of capabilities for each implementation to
  choose.** `Cursor` declares `capability Uses`, its `next` declares
  `uses Self.Uses`, and each `impl` defines the set: `FileRead` for a cursor
  over a file's lines, nothing for a cursor over a list. The cursor of a
  yielding method has the method's `uses` clause as its set. Generic code
  that advances a cursor declares `uses Source.Uses`, and a call of it needs
  the capabilities of the cursor that it passes. Otherwise a trait's method
  could use only the capabilities that the trait fixes for every
  implementation: `Cursor.next` would use none, and a cursor that reads a
  file could not be passed to `zip`, `take`, or `to_list`. Swift does the
  same for errors: `AsyncIteratorProtocol` has an associated `Failure` type,
  which its `next` throws. Koka's effect variables on every function type
  are more general, and a capability parameter already covers the case that
  they serve in Truss, a callback. An `any` type fixes every such set to the
  empty set, because code that holds the value cannot name the capabilities
  of the type that it hides.
- **A function type with clauses is written in parentheses,** as in
  `(fn(Item) uses Clock, Random cost time finite)`. Its clauses come after
  the return type, in the same order as in a definition. Swift and Koka
  write effects before the arrow instead, but they have one or two effect
  keywords, and Truss has whole clauses. The parentheses mark where the
  clauses end, so `uses Clock, Random` cannot run into the next parameter or
  type argument, and a definition that returns a function type can tell its
  own clauses from the returned function's. Function types can carry `cost`
  clauses that do not mention parameters, so a callback can promise to
  terminate, and the function that calls it can then promise a `time` bound.

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
- **Opening a handle and using a handle are separate capabilities.**
  `FileRead.open`, `NetworkClient.connect`, `NetworkServer.listen`, and
  `Processes.spawn` each return a handle. Every operation on a handle
  (read, write, accept, wait, close) requires `Handles`. A function that is
  passed a connection declares `uses Handles`. It can serve that
  connection, and it cannot open another one.
  - **The alternative fails for connections.** If a handle's methods
    required the capability that opened the handle, `Connection.read` would
    need `NetworkClient` for a connection the program opened and
    `NetworkServer` for one it accepted. A request handler would then hold
    the capability to open connections of its own.
  - **It allows one `Reader` trait and one `Writer` trait.** An `impl`'s
    methods can use only the capabilities their trait declares. With one
    capability for every handle, files, connections, and pipes all
    implement the same two traits.
  - **A handle is a token.** The provider of `Handles` decides what a read
    returns. A test's provider can simulate a file, or a network between
    two tasks, and the code under test does not change.
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
- **Every dependency has a grant, a project's own packages included.** A
  project split into packages says in its manifests what each part may do,
  so a reviewer reads there that the package that parses can touch nothing.
  Much of a project's own code is written by LLMs and not all of it is
  reviewed, so the limit matters at home as it does for a stranger's code.
- **Exceeding a grant fails the build.** The error names the dependency's
  function and the capability it used. Giving a package more power is always a
  visible change to the manifest.
- **A missing grant is never fixed automatically.** The error says which
  capability to add to which entry, and no tool adds it: `truss check --fix`
  never widens a grant. Whoever grants one, person or agent, writes a line
  in the manifest that a reviewer sees.
- **Grants are checked at signatures, wherever a dependency's code is
  named.** A call to a dependency's function is checked against the
  dependency's grant, from the callee's `uses`. So is every other way of
  handing its code on: taking its function as a value, using its `impl`
  where a bound or an `any` needs one, and a `provide` of its type.
  Otherwise a package with no grant could have its `impl` run by a package
  that has one. The dependency's bodies are already checked against its own
  signatures, so nothing it does can go further. A dependency that offers
  both a client and a server needs only the grants for what the program
  names.
- **A grant names a capability as code does:** a prelude capability by its
  name, and any other by its full path. A package needs a grant even for a
  capability it defines itself, since what the capability can do is decided
  by whoever provides it.
- **Grants nest, and signatures are what make them.** A package can hand its
  own dependencies no more than it holds. No rule about manifests checks
  that, since a published package's manifest is fixed while what it is
  granted differs from one user to the next. It follows from the signatures:
  a function a package offers under a grant carries in its `uses` every
  capability anything beneath it uses, so nothing beneath it can use more.
- **Passing through does not count.** Running a caller's callback with the
  caller's capabilities (through a `capability Granted` parameter) is not the
  dependency doing anything itself.
- **The standard library needs no grant.** It holds the real implementations.
- **A new version cannot take more for what is already called.** A release
  that adds a capability to a function's `uses` is not a compatible one (see
  [Versions](#versions)), so an upgrade under one name can change what a
  function already called computes, and never what it may touch.
- **What each package holds is written down.** The lock file records, for
  every package of the build, the capabilities its users grant it. An
  upgrade deep in the graph that hands a package the network shows as a
  changed line.
- **Nothing in a package runs when it is fetched or built.** Truss has no
  build scripts and no macros, the code that runs while compiling is pure
  (see [Tagged templates](#tagged-templates)), and a test has no
  capabilities but the fakes it provides. npm's install scripts, Cargo's
  build scripts, and Rust's procedural macros run a dependency's code on
  the developer's machine with everything the developer can reach, which is
  how a package that steals a publishing token goes on to publish itself
  under its victim's name. A dependency's external tests, which do get real
  capabilities, are never run by a project that depends on it.

What grants cannot stop is a wrong answer. A pure dependency can still
return a result that its user then acts on with capabilities of its own.
Contracts narrow that, and review of what a project depends on is still
needed.

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
- **`O(f)` holds for every input, not just large ones:** the cost is at most
  `c * f + d` for constants the prover finds. The textbook definition, "for
  large enough inputs", is about limits, which a prover handles poorly, and
  it gives wrong answers for bounds in several variables, as Rodney Howell
  showed in "On Asymptotic Notation with Multiple Variables" (2008). Verified
  complexity work in Coq and Isabelle, such as Charguéraud and Pottier's
  time credits, uses the same explicit form, as does RAML's inference of
  polynomial bounds.
- **Bounds can depend on the result,** as in `O(text.length() +
  result.length())` for a function that returns its matches. Such
  output-sensitive bounds are common in algorithms and would otherwise be
  impossible to state.
- **Cost expressions use exact integers and two functions of their own,**
  `log` and `power`. `log(n)` rounds log₂(n + 1) up, so it is defined at 0
  and stays an integer; inside `O`, the base of a logarithm makes no
  difference.
- **Amortized bounds are proven with potentials.** `List.push` is O(1)
  except when the list grows, so its honest bound holds only over many
  pushes. A type can declare a potential, as in Tarjan's potential method,
  and a method promises `cost amortized time O(1)`. This follows Automatic
  Amortized Resource Analysis (Hoffmann, Jost, and others, the basis of
  RAML), and Charguéraud and Pottier's verified amortized bounds. AARA needs
  values that are never shared, because two references to one structure
  could spend its potential twice. Mutable value semantics gives exactly
  that, so amortized bounds compose soundly in Truss. A value's potential is
  its own type's potential plus the potentials of its parts, so pushing onto
  a list inside a list is paid for by the inner list's potential, as AARA's
  types count the potential of every element. Writing potentials is mostly
  the standard library's job.
- **There are no expected-time bounds.** A hash map is O(1) only on average,
  assuming its hashes behave randomly, which no proof can promise against an
  input chosen by an attacker. Proving expected bounds needs probabilistic
  program logics that are still research. Cost clauses state bounds that
  hold for every input, and the typical case is described in documentation.
- **Costs count capability calls.** `cost calls(FileRead.read) ==
  paths.length()` states a number of file reads. That number holds no matter
  which implementation performs the reads.
- **Costs compose through signatures.** A caller's cost is proven from its
  callees' cost clauses, without reading their bodies, so changing one function
  only re-checks what depends on it.
- **Loops can state their cost.** Most loops need nothing: each iteration
  costs at most some bound, and the loop runs a known number of times. A
  loop whose iterations cost different amounts, such as one over rows of
  different lengths, states what it has spent so far as a `cost` clause, an
  invariant about the cost: `cost time O(cells(yielded))` holds at the start
  of each iteration and when the loop ends, for the rows handled so far.
  This is how Charguéraud and Pottier's time credits and Creusot's loop
  invariants over spent resources state it. A loop's cost is never
  `amortized`, since potential belongs to the values a loop changes, and
  never `finite`, since a loop shows that it ends with `decreases`.

## Termination

- **A `time` clause promises the function terminates.** `cost time finite`
  promises termination without giving a bound.
- **A function without a `time` clause might not terminate.** No separate
  marker is needed.
- **Functions used in `requires`, `ensures`, laws, or proofs must be pure
  and have a `time` clause.** Otherwise the proof system would not be sound:
  a function that might not return, or might stop the program, has no value
  to reason about.
- **Recursion over the parts of a value needs no annotation.** A recursive
  call on a part of a parameter clearly ends, as Lean accepts structural
  recursion automatically. A part is a field taken out by a pattern, or an
  element of a collection that is itself a part, as in
  `for child in children { child.display(mut output) }` over a tree's
  children. Dafny orders values the same way, with a sequence's elements
  below the sequence. Other recursion states a `decreases` measure, as in
  Dafny, F*, and SPARK, compared in order when there are several. Truss
  does not guess a measure when none is written, as Dafny does: a
  structural check plus an explicit clause is more predictable than a guess
  that may or may not work.
- **Recursion counts every way a function can reach itself.** Calls are not
  the only way: a function can also name another as a value, or use an
  `impl` where a bound needs one, and the code that receives it calls back.
  So inside an `impl`'s methods, using that same `impl`, as in passing
  `self` to a generic function bounded by the trait being implemented, is a
  recursive call to every method of the `impl`. Without this, a package
  could implement a trait with a method that calls a generic function from
  another package that calls the method back, and each `time` clause would
  be proven by assuming the other. Lean reads an instance that uses itself
  the same way. Such a use passes no arguments the prover can compare, so
  it cannot be shown to decrease, and the error says to write the
  recursion as a direct call on a part. Derived implementations are proven
  by the compiler's rule, and functions without a `time` clause need no
  termination, so neither is affected. Truss has no mutable state outside
  variables, and a value cannot hold a function that takes the value and
  promises to terminate, so a function can reach itself only through what
  its code names, and every such cycle is visible within one package.
- **A type cannot hold a function that takes the type and promises to
  terminate.** In its own fields, a type must not occur in the input of a
  function type that has a `time` clause: at any depth, through type
  arguments, and through associated types. With `type Knot(run: (fn(Knot)
  -> Bool cost time finite))`, a function that calls `knot.run(knot)` calls
  itself when `knot.run` is that function, and no name in its code says so.
  Its `time` clause would be proven although the function does not
  terminate. Coq, Lean, and Agda forbid this for every function type, as
  strict positivity. Truss forbids it only for a function type with a
  `time` clause, because a function with a `time` clause cannot call a
  function value whose type has none: `type Button(on_click: fn(Button))`
  is legal.
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
A proof block is a result of its own, apart from the code around it. Editing
a proof re-checks proofs but does not rebuild the program or rerun tests.

**Verification is modular.** The prover knows other functions by their
signatures, and reads a body only where the body is a definition, as below.
Each proof therefore looks at a small amount of code, which keeps proofs
stable and checking O(change). The prover's design is in
[PROVER.md](PROVER.md).

**Proof checking is deterministic.** The solver runs within fixed limits
measured in steps, never in wall-clock time, and its version is pinned as part
of the toolchain. Z3's `rlimit` and cvc5's `--rlimit` count work in this
way. A result is kept under the hash of the query that was sent
to the solver. A proof that passes once keeps passing, and a slow machine
never fails a proof that a fast one passes. Solver-based tools are known for
proofs that break for unrelated reasons, so Truss designs against this from
the start.

**There is no `assume`.** The only gap allowed in a proof is `todo`. A
program that can reach an unfinished proof cannot be built, just like one that
can reach unfinished code. Otherwise a missing proof that an addition cannot
overflow would allow a failure the signature does not show. If a function
claims something in its signature, the claim must be proven before it ships;
a claim that is not ready can simply be left out.

### What a function means to the prover

A function is known to the prover in one of two ways: by its contract, or
by its definition.

```truss
fn is_sorted[Element: Ordered](items: Slice[Element]) -> Bool
  cost time finite
{
  forall i in 1..items.length() => items[i - 1] <= items[i]
}
```

- **A functional body is the function's definition.** When a function is
  pure, has a `time` clause, and its body is functional, the prover reads
  the body as what the function means, so `is_sorted(items)` means exactly
  the quantifier above. A functional body uses `let`, `if`, `match`, `is`,
  calls, fields, building values, `with`, operators, and quantifiers. It has
  no `var`, no assignment, no loop, and passes nothing `mut` or `own`. This
  follows Dafny, whose `function`s are their bodies, and SPARK, whose
  expression functions are visible to the prover without being asked.
- **Every other function is known by its contract.** A body with a loop has
  no meaning the solver could use without the invariant that says what the
  loop computes, which is what the contract states anyway.
- **No keyword marks either kind.** The body already says which it is, as a
  signature that mentions `Integer` already says a function is for
  specifications. Prusti's `#[pure]` and Liquid Haskell's `reflect` mark it
  instead. Whether a body is read is a fact callers' proofs depend on, so
  their traces record it, as they record whether a method can be pulled,
  and the tools show it with the signature.
- **A definition is read only where everything it reads is visible.** A
  body that reads the fields of an opaque type is a definition inside that
  type's package, and elsewhere the function is known by its contract, so
  `opaque` keeps the representation private from proofs too. Verus makes
  the same distinction with `open` and `closed` specification functions.
- **Definitions must be well founded.** A definition is sound only for a
  function that terminates, which the `time` clause and the rules of
  [Termination](#termination) guarantee, and a function with a `requires`
  is defined only where its `requires` holds.
- **Quantifiers are expressions in code too.** `forall i in 0..count => p`
  and `exists item in items => p` run as loops that stop at the first
  answer, and cost what such a loop costs. Ada's quantified expressions and
  Dafny's bounded quantifiers are executable in the same way. A quantifier
  over a whole type, such as `forall value: Int64 => ...`, cannot run, and
  stays in specifications. The binder carries its range, so the body may
  rely on it: `items[i - 1]` above is in bounds because `i` is in
  `1..items.length()`. A lambda passed to a method would know nothing about
  its argument. So the standard library has no `all` or `any` methods, and
  testing every element has one spelling.
- **A function's body is a specification when its signature mentions a
  type that exists only in specifications.** Its arithmetic is exact, it
  may use `==>` and quantifiers over a whole type, and it is never compiled.

### Specifications

- **Specifications have no capabilities.** A function called in a
  specification is pure, with no `uses` at all, not even `Panic`: a logical
  function that might stop the program has no value to reason about. A
  function that can fail on some inputs says so with `requires`, and every
  specification is checked to be well defined, so each call in it meets its
  callee's `requires` and each index is in bounds, as in Dafny.
- **Specifications read from left to right.** In `&&`, `||`, `==>`, and
  `if`, the right side may rely on the left, so
  `index < items.length() && items[index] > 0` is well defined.

**Specifications have implication, `a ==> b`,** as Dafny, Verus, Prusti,
and ACSL write it. "If this holds, then that holds" is the most common shape
of a specification, and writing it as `!a || b` hides what it says. It binds
more loosely than `&&` and `||`, the reading every one of those languages
shares, and it does not chain, like comparisons. It exists only in
specifications, including the bodies of functions for specifications only,
because code already has `if` and `!a || b`, and two spellings there would
buy nothing. Laws take `requires` premises, as
theorems and Dafny's lemmas do, so `transitive` reads as its definition. A
quantifier can be the last operand of `&&`, `||`, or `==>`, as in Dafny,
since its body runs to the end of the expression anyway.

**Specifications use exact integer arithmetic.** In `requires`, `ensures`,
invariants, laws, and cost clauses, integer arithmetic never overflows, so a
specification cannot itself have an overflow bug. This follows Dafny, through
the prelude type `Integer`, the mathematical integers, which exists only in
specifications:

- **Every built-in integer type is a subset of `Integer`.** Arithmetic on
  built-in integers in a specification gives an `Integer`, so in
  `ensures result == a + b` the sum cannot overflow, and in
  `decreases high - low` the measure can be negative, which is exactly what
  the prover must rule out. Comparisons may mix integer types, as in
  `requires count <= items.length()`, since nothing can overflow.
- **An `Integer` can stand where a built-in integer is expected,** as in
  `items[i + 1]`, with a proof obligation that it fits. Specifications need
  no casts. Verus asks for an explicit `as` there, which adds only noise,
  since the obligation is proven either way.
- **A function whose signature mentions `Integer` is for specifications
  only.** It can be called only from specifications and is never compiled,
  which is how a function such as `fn sum(items: Slice[Int64]) -> Integer`
  is written. Verus marks these with `spec fn`; Truss needs no keyword,
  since the signature already says it. The same holds for every type that
  exists only in specifications, below.

Float arithmetic in specifications follows IEEE 754, as in code. Exact real arithmetic would
describe results the hardware does not produce, so such contracts could never
be proven. The solver checks float contracts bit for bit, which is slow, so
they are best kept rare.

### Mathematical models

A contract about a whole collection needs something to compare it with.
`List.push` promises that the list afterward is the list before with one
more element at the end, and `reverse_twice` that reversing twice gives the
same list back. Saying that through `length()` and indexing alone takes a
quantifier for every statement, and a hand-written `Equal` is not even
structural. So the prelude has mathematical collections that exist only in
specifications, as `Integer` does, and types give their values in terms of
them:

| Type | Values |
|---|---|
| `Sequence[Element]` | Finite sequences, compared element by element |
| `FiniteSet[Element]` | Finite sets |
| `FiniteMap[Key, Value]` | Finite maps from keys to values |
| `Multiset[Element]` | Finite multisets, for statements such as "the same elements, in another order" |

- **A type states its model through the prelude trait `Model`,** whose one
  method, `model(self)`, gives the value in mathematical terms and exists
  only in specifications. `List[Element]` and `Slice[Element]` are modeled by
  a `Sequence[Element]`, `String` by the `Sequence[UInt8]` of its bytes,
  `Map` by a `FiniteMap` together with the order of its keys, and `Set` by a
  `FiniteSet` with its order. A user's type can have a model too, such as a
  `Sequence` of its cells for a `Grid`.
- **Contracts are written against models,** as in
  `ensures identical(self.model(), old(self.model()).append(item))`, and against
  methods whose own contracts relate to the model, such as `length()` and
  indexing. An opaque type's model is how other packages reason about it
  without seeing its fields.
- **The mathematical types have structural equality,** so the prover can
  substitute through them even where the collection's own `Equal` is
  hand-written.
- **`identical(a, b)` is identity, for every type, in specifications.**
  Generic contracts must say that an element is a given value whatever its
  type, as `List`'s indexing does with
  `ensures identical(result, self.model()[key])`, and `==` cannot: it is
  the type's `Equal`, which `List[Element]` does not require, and for a
  type with a hand-written `Equal`, such as a set stored as an unsorted
  list, it is an equivalence rather than identity. So `==` keeps that one
  meaning everywhere, and identity has a spelling of its own. Lean
  distinguishes logical `=` from the decidable `==` the same way, and F\*
  `==` from `=`. Verus instead gives `==` a different meaning in
  specifications than in code, which would let a contract on a set mean
  identical representations where its author meant the same set.
  `identical` is a specification word, like `old`, so no function may be
  named `identical`.
- **Collection literals take these types from context too,** so `[]` is an
  empty `Sequence` where one is expected.

Verus calls the same idea a `View`, Creusot a model, and SPARK functional
containers; Dafny builds `seq`, `set`, `map`, and `multiset` into the
language. Each converged on it because contracts about collections need a
value that is not the collection's representation.

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
  code, and so the keys of the tests that can reach it, which run again and
  show the output, instead of being served from the cache. Removing it
  restores the old keys, and the cached results apply again. Tests are deterministic, so a re-run takes exactly the
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

None of these is a special case. Each comes from the contract of the `each`
method the loop calls (see [Lending and yielding methods](#lending-and-yielding-methods)):
a range's `each` promises that each value lies within the range, a list's
that it yields each element once, in order, and both have a `time` clause,
so the loop ends. A user's collection whose `each` makes the same promises
gives its loops the same facts.

`while true` is the infinite loop. A `while` whose condition is the literal
`true`, and that no `break` leaves, has type `Never`, as Java and Kotlin
treat it, so a server whose main loop runs forever can return `Never`.

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
  only exception is `Panic`. Code whose parts use capabilities at the same
  time is concurrent, and is written with `concurrent` (see
  [Concurrency](#concurrency)).
- **No `uses` needed.** A function that uses `parallel` is still pure, and
  tests that run it can still be cached.
- **Proofs and costs work as for sequential code.** Branches are disjoint, so
  their order can't matter, and the prover treats them as running in order.
  `time` measures total work, so a `parallel` block costs the sum of its
  branches.
- **`span` is to measure the work that cannot be done at once.** A
  `parallel` block's span is the largest of its branches' spans, where its
  `time` is their sum, and the span of code with no `parallel` in it is its
  time. On `p` cores a function finishes in time proportional to
  `time / p + span`, the bound a scheduler that steals work meets. So a
  signature with `cost time O(n)` and `cost span O(log(n))` promises that
  the function gets faster with each core it is given. This is the
  work-span model of Cilk and NESL, and of textbooks on parallel
  algorithms. `span` joins the grammar with the first function of the
  standard library that states it.
- **The result does not depend on the machine.** Where a computation is
  split into branches is decided by its input, never by the number of
  cores. A parallel sum of floats therefore groups its additions the same
  way on every machine and gives the same bits, so a cached test result
  holds everywhere.
- **Branches run on a pool of threads that steal work.** The pool has one
  thread for each core. A thread with nothing to do takes a branch that
  another thread has not started, as in Cilk, Rust's rayon, Go's
  scheduler, and Java's fork-join pool. The pool starts the first time a
  program runs code at once, so a program that never does has no thread
  but its own.
- **Tests run branches in order.** The test runner already runs one test on
  each core, so a test gains nothing from more threads. In order, a check
  that fails is the same check on every run.
- **Panics end the program, as anywhere else.** If more than one branch could
  panic, which message is printed may vary.
- **Early exit is not allowed.** A branch uses no capabilities, so it cannot
  be asked to stop. Leaving with `return` or `?` would have to abandon the
  other branches partway, or wait for work whose result is thrown away.
  Branches return values instead, and the code after the block decides what
  to do with them.

The design follows Rust's scoped threads and rayon, Swift's `async let`, and
Hylo, which also uses mutable value semantics.

## Concurrency

Concurrency means doing several things whose order is not fixed, such as
serving a server's connections, or waiting for a reply and a timer at once.
What such code does can depend on what happens first, so concurrency is an
effect: code that does it declares `uses Tasks`.

- **`concurrent` runs its branches as tasks.** A `concurrent` block runs
  each of its statements as a task and ends when every one has ended. A
  `concurrent for` runs each iteration as a task. They are written as
  `parallel` and `parallel for` are, and differ in one way: a branch may
  use the capabilities of the code around it, which is why the function
  needs `Tasks`.
- **No data races, by the same rule as `parallel`.** Any branch may read any
  place, and a place that one branch changes cannot be used by another. A
  branch hands its result to the code after the block through a `let`, or
  through its own element of the collection it loops over.
- **A branch leaves each place whole.** When a branch leaves early, the
  code after the block does not run. So a branch that takes a value out of
  a place that outlives the block gives one back itself, where a
  `parallel` branch may leave that to the code after the block.
- **A task never outlives the block that started it,** as with Trio's
  nurseries, Kotlin's `coroutineScope`, Swift's task groups, and Java's
  `StructuredTaskScope`. This is what lets a branch read the places around
  it without lifetimes, and use the capabilities provided around it, whose
  implementations are the enclosing code's variables. A task started with
  Go's `go` can outlive everything it was given, so in Truss it could be
  given neither.
- **A task borrows only what outlives the loop.** An iteration of a
  `concurrent for` outlives the `yield` that started it. A place inside a
  parameter that the method takes read-only cannot change or be freed
  while the method runs, so a task may borrow it: `concurrent for item in
  items` lends each element for the whole loop. A value that the method
  yields `own`, or computes for the `yield`, goes to the task, and a
  `Plain` value is copied. A place in a local of the method or in a `mut`
  parameter could change or be freed when the method resumes, so yielding
  it to a task is rejected: it would be a use after free. A method that
  yields `mut` access can drive a `concurrent for` only if its body is one
  loop over a range that yields at each index. Each task then runs one
  iteration of that loop and changes its own element. Rust draws the same
  line between an iterator, whose items outlive the step that produced
  them, and a lending iterator, whose items do not.
- **`yield` is not allowed in concurrent code.** It would run the caller's
  loop body as a task, at the same time as the method's other tasks, and
  the caller's loop body is checked as sequential code.
- **It is a construct, not a function that is passed a function.** A
  `spawn(work)` would have to keep `work` until the task runs, and only a
  function that captures nothing can be kept (see [Closures](#closures)).
  Such a task could read nothing around it, and would hand its result back
  through a handle for the caller to join. A branch needs no handle and no
  join, and the one rule about places covers it.
- **Blocking calls, no async.** Code waits by calling a capability method
  that returns when the result is ready, as in Go, Java's virtual threads,
  and Zig's `Io` interface. There is no `async` or `await`. `uses` already
  separates the code that can wait from the code that cannot, and a second
  mark for the same fact would split functions into two kinds that can't
  easily call each other. This fits the rule that a capability method
  always returns.
- **How a task waits can change without any code changing.** Truss has no
  foreign code, so every call that waits is in the standard library's real
  capability implementations. They can give each task a thread of the
  operating system, or run many tasks on the pool's few threads and switch
  between them where a task waits, and no caller can tell which. Go and
  Java cannot switch away from a task that waits inside foreign code.
- **Leaving early cancels the other branches.** A `?`, `return`, or `break`
  that leaves a `concurrent` block or loop cancels every other branch,
  waits for each to end, and then leaves. A branch that has not started
  does not start. The first branch to leave decides where control goes and
  with what value; a later one's is dropped. Kotlin, Swift, Trio, and
  Java's scopes cancel sibling tasks the same way.
- **Cancellation is an error value.** In a cancelled task, the standard
  library's implementation of a call that would wait returns at once with
  the value that says it did not finish: `SystemError.Cancelled` where the
  method returns a `Result`, and `None` where it returns an `Option`. A
  method that returns nothing, such as `Clock.sleep`, returns early. `?`
  carries the error out like any other, so a cancelled task ends by
  returning, along a path that is written in its code. `Tasks.cancelled()`
  tells a loop that calls nothing that waits.
- **Cancellation breaks no contract.** The cancelled value is returned by
  an implementation, which is proven against its method's `ensures` like
  any other result, so a caller's proof holds whether or not the task was
  cancelled. An implementation written on calls that wait passes their
  error on. A cancelled task that is blocked on the mutex of a `mut`
  implementation stays blocked until it acquires the mutex, since the call
  has no other result to return.
  This is Go's `Context` without the parameter, since whatever provides
  `Tasks` knows which task is calling. Trio and Kotlin raise an exception
  at the call instead, and Rust drops a future at whichever `await` it had
  reached, which abandons a computation partway. Truss has neither
  exceptions nor abandoned computations (see
  [Capabilities](#capabilities)).
- **A time limit and a race are ordinary code.** `tasks::with_timeout(limit,
  work)` runs `work` in one branch and a timer in another, and each branch
  returns from `with_timeout` when it finishes, which cancels the other. Nothing
  like Go's `select` is needed for either.
- **A channel is how one task waits for another.** A `Channel[Message]` is
  a queue with a fixed capacity: `send` waits while it is full, `receive`
  waits while it is empty, and `close` ends the loops of the tasks that
  receive from it. A channel of capacity 0 holds no message, and its
  `send` returns when a task has received the message, as on Go's
  unbuffered channels and Kotlin's rendezvous channels. The messages of
  one sender are received in the order it sent them, as on Go's and
  Rust's channels; the messages of two senders interleave in any order. A message is
  owned, so sending one moves it and copies nothing. Its type is `Storable`, so never a view type, since what a view
  views could be gone before the message is received. A function's type
  does not say what the value holds, and neither does an `any` type whose
  trait does not require `Storable`, so they are view types too (see
  [Views](#views)). A message is a record or a sum type of owned data, or
  an `any` of a trait that requires `Storable`.
  A channel is a reference to its queue. `channel.copy()` makes another
  reference to the same queue, and the queue is freed when the last
  reference is dropped, so a channel can be stored in a record or held by
  a capability implementation that outlives the function that made it. A
  channel's methods take `self` read-only, so every branch can also use
  one channel that is declared before the block. A task that waits for
  several kinds of message receives one sum type from one channel, as an
  Erlang process reads one mailbox.
- **How many tasks run at once is bounded by a value, not by syntax.** A
  `tasks::Limiter` holds a number of permits, and `limiter.hold(work)`
  runs `work` once it has one. This is Kotlin's `Semaphore.withPermit` and
  Trio's `CapacityLimiter`, and it is written with a channel of permits, as
  in Go.
- **State that tasks share lives in a capability implementation.** Whatever
  changes lives in a variable, a parameter, or a capability implementation
  (see [Memory](#memory)), and two tasks cannot share a variable that
  either changes. So state that several tasks change is an
  implementation's: a table of sessions is a type that holds a `Map` and
  implements a `Sessions` capability, provided `mut` around the code that
  serves requests. `uses Sessions` then marks every function that can touch
  the table.
- **Calls into a `mut` implementation are mutually exclusive.** Where the
  code inside a `provide mut` can use `Tasks`, the implementation has a
  mutex. Each call of its methods holds the mutex from start to end, and a
  task that calls meanwhile blocks. This is a monitor: Ada's protected
  objects, Java's `synchronized` methods, and an Erlang `gen_server` work
  the same way. A check and the change that depends on it therefore go in
  one method. Within a call nothing else changes the state, and between
  two calls anything may. No task is left holding a view of the state,
  since a method returns none. An implementation provided without `mut` is
  only read, so it has no mutex.
- **Proofs already allow for it.** The prover never models an
  implementation's state: a capability call gives a value of which only
  the method's `ensures` is known. No proof ever assumed that the state
  stays the same from one call to the next, so every proof still holds when
  other tasks' calls come between.
- **These mutexes cannot deadlock.** An implementation's methods can call
  only capabilities provided outside it, so every task acquires the
  mutexes in one order, from the innermost implementation outward. One
  rule keeps this true: an implementation with a mutex has no method with
  a parameter that can hold a function, or an `any` value, that uses a
  capability, since calling it could acquire the mutex of a nested
  implementation out of order.
- **Mutual exclusion costs nothing where there are no tasks.** Whether the
  code inside a `provide mut` can use `Tasks` is known where the `provide`
  is written, from the signatures of what it calls. Code that uses a
  capability parameter of the enclosing function counts, since the
  parameter may be instantiated with `Tasks`. Only such a `provide` gets a
  mutex.
- **A mutex is not a value.** Rust's `Mutex` and Go's `sync.Mutex` change
  what a read-only place holds, which mutable value semantics rules out,
  and two tasks that take two of them in different orders deadlock. A task
  that owns the state and answers messages, as in Erlang, needs nothing new
  and stays possible, but every use of the state then switches tasks twice
  and waits behind every other use. Erlang added shared tables and atomic
  counters for that reason.
- **A cell with a pure update is what a channel is built on.** The cell,
  `intrinsic::Shared`, holds a value behind a reference count and a mutex.
  Its one operation runs a pure function on the value while it holds the
  mutex, as an update of a Clojure atom does. A pure function cannot wait,
  use another cell, or do I/O, so two updates cannot deadlock, and no task
  holds the mutex across a call that can wait. Updating a cell requires
  `Tasks`, because which task updates first differs from run to run. Only
  the standard library can name the cell, and a channel's queue is one. A
  public cell, for state that one implementation's mutual exclusion is too
  coarse for, such as a cache in many parts, is added when a program needs
  it.
- **Data races cannot happen, and waiting forever can.** A task can wait
  for a message that no task will send. Go, Rust, and Erlang do not rule
  that out either.
- **Tests stay deterministic.** A test provides a `Tasks` implementation
  that runs one task at a time and chooses by a seed which runs next. It
  switches tasks only at capability calls. Tasks share no memory that
  changes, so nothing a task does between two capability calls is visible
  to another, and the orders of those calls are all the orders there are. A
  race is then a failure that one seed repeats, not a rare, flaky one.
  FoundationDB, TigerBeetle, and AWS's Shuttle test this way.
- **A test's clock moves when every task waits.** Time then jumps to the
  next timer, as in Go's `testing/synctest` and Trio's test clock. A test
  of a timeout takes no real time, and its result can be cached.
- **A test in which no task can go on fails,** and reports what each task
  was waiting for.
- **Tasks and `parallel` branches run on one pool.** A program has one set
  of threads, as Go and Java have, so code that computes and code that
  waits do not compete with two pools for the same cores.
- **Waiting may never end.** A function that waits on a channel cannot be
  proven to terminate, so it has no `time` clause.

## Collections

- **Each collection has one way to be written.** `[a, b, c]` is a `List`, and
  `[]` is the empty list, so there is no `List.new()` or `List.of(...)`. Maps
  use Swift's `[key: value]`, with `[:]` for the empty map; `{ }` already
  means blocks.
- **A `[...]` literal takes its type from context, defaulting to `List`,** as
  number literals do. Where an `Array` or a `Set` is expected, the literal
  is one, as Swift's array literals are. The expected type is always written
  nearby, in a signature or an annotation, so a reader can see what the
  literal makes.
- **`Array[Element, count]` holds a fixed number of elements in place.** A
  digest, a small matrix, or a lookup table should not need the heap, and as
  plain data it copies like an integer. Rust, Go, C, and Zig all have such a
  type, and Swift added `InlineArray` in 2025 after a decade without one.
  Its length is a generic parameter of type `USize`. Arithmetic on such
  parameters inside types is left out for now: Rust has worked on it for
  years without settling it, and it can be added later without breaking
  code.
- **Literal allocation is counted.** A non-empty list literal in a function
  body counts as one allocation in `cost` clauses, and an empty one as
  none. The compiler may keep a literal that is only read in static
  memory, but cost clauses don't depend on that. Constants are different:
  they always live in static memory, so reading one costs nothing.
- **A set or map literal is a sequence of calls.** `[a, b]` as a `Set`
  means: make an empty set with room for two elements, then `insert` each
  element in order. A map literal does the same with its entries. The
  literal costs what those calls cost, in time and in allocations, so a
  `cost` clause on a function that contains one is checked against the code
  that runs. The standard library reserves room for every element first,
  so the literal does not reallocate as it fills.
- **Constant collections are built while compiling.** The compiler builds a
  `Map` or `Set` constant by running the standard library's own insertion
  code while compiling, so its table is ready in static memory and lookups
  cost what they always cost. Hashing has no random key, so the table comes
  out the same on every build. Constants are read-only places, so the table
  is only ever read; an owned, changeable copy is made with `copy()`.
- **Duplicate keys in a map literal are a proof obligation.** Each entry of
  a map literal is inserted by a method whose precondition is that the key
  is not in the map yet, so the obligation is an ordinary `requires`.
  Letting the last
  one win would silently hide a mistake.
- **`Map` and `Set` iterate in insertion order,** like Python's `dict` and
  JavaScript's `Map`. Iteration order never varies from run to run, so tests
  stay deterministic and their results can be cached.
- **Maps resist hash flooding deterministically.** An attacker who can choose
  keys that collide can turn each map operation into a scan of the whole map,
  which Klink and Wälde used in 2011 to stall servers in many languages.
  Python, Rust, and Go defend with a hash key chosen at random for each
  process or map. In Truss that would be randomness no signature shows: it
  would change timing, allocation counts, and profiles from run to run, and
  make a test near its time limit flaky. Truss instead does what Java 8 does
  (JEP 180): a bucket that fills up becomes a balanced tree, so the worst case
  is O(log n) per operation, which cost clauses can promise. An attack can
  then slow a map by a factor of about log n, not make it quadratic. This is
  why keys must be `Ordered` as well as `Hash`.
- **Random hashing is available through a capability.** `Map.seeded()` takes
  its key from `Random`, so code that must stay fast while under attack can
  have it, and its signature shows `uses Random`. Every source of randomness
  in Truss goes through a capability.
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

## No foreign code

Truss has no foreign function interface. Only the standard library reaches the
operating system, through means internal to the compiler.

- **A young ecosystem grows by being written in Truss.** If packages could
  call C, the quickest way to get a library would be to wrap an existing one,
  and LLMs would take that shortcut every time. The ecosystem would then be a
  layer over C code that no Truss proof, capability, or cost clause covers.
  Without foreign calls, each library is written in Truss, verified, and held
  to its capabilities. Elm made the same choice in 0.19, when it limited
  native code to its own core packages.
- **Foreign code would escape every guarantee.** A C function can do
  anything, so its capabilities, contracts, and costs could only be assumed,
  and Truss has no `assume`. A supply chain with C inside it is exactly what
  GOALS.md sets out to avoid.
- **The cost is reach.** Anything that needs the operating system or special
  hardware, such as new system calls, graphics, or processor instructions for
  cryptography, comes only through the standard library. `extern` and
  `unsafe` stay reserved in case foreign calls are ever added, once the
  ecosystem stands on its own.
- **Code for one platform lives only in the standard library.** Since nothing
  else touches the operating system, nothing else needs conditional
  compilation. Code that wants to know the platform asks the `Environment`
  capability, so the answer is tracked, and a test can supply a different
  one.

## The standard library and prelude

The standard library's root module is `standard`. Truss aims to include
enough in it, plus a set of approved packages, that most programs need few
outside dependencies. Every dependency is a possible target for a supply-chain
attack.

- **The standard library is part of the toolchain.** It has no version of
  its own and is in no manifest and no lock file: every package may use it,
  and it is the toolchain's.
- **A package says which Truss it is written for,** with `truss = "1.4"` in
  its manifest, as Go's `go` line does. That one number is the language
  version the package's files are read as, and the least toolchain that can
  build it, since the standard library it may use is that toolchain's. A
  build needs a toolchain at least as new as the newest of its packages
  asks for, and a toolchain reads each package as the language version it
  names, so a package written for an older Truss builds unchanged beside
  one written for a newer, as Rust's editions and Go's per-module language
  versions allow.
- **The standard library never breaks within a language version.** It
  follows the rule every published package follows (see
  [Versions](#versions)), and has no second name to move to.
- **It holds only what will not need a breaking change.** That is three
  kinds of code:
  - **Code that needs the compiler or the operating system:** the prelude,
    the built-in types and collections, the capabilities and their real
    implementations, and platform-specific code.
  - **Types that packages must share to interoperate:** `Reader` and
    `Writer`, `Path`, `Instant`, network addresses, `json::Value`.
  - **Implementations of published standards:** JSON, CSV, Base64, URLs,
    UUIDs, Unicode, SHA-2. A standard that is frozen cannot make its
    implementation stale, which is how Python's standard library modules
    went stale. This is what lets the library be large.

  The cryptographic primitives are in it for a second reason. They need
  processor instructions, and only the standard library can reach those
  (see [No foreign code](#no-foreign-code)). The standard library is also
  the only package that needs no grant (see
  [Dependencies](#dependencies)).
- **Anything still evolving is an approved package.** HTTP, TLS,
  compression formats, database clients, and markup languages change with
  practice, so a library for one of them will need breaking changes.
- **The approved packages are the registry's packages owned by `truss`,**
  such as `truss::http` and `truss::toml`. They are plain Truss, written on
  the standard library's capabilities and granted them like any dependency,
  and are held to the review and release rules of the toolchain itself. Go's
  `golang.org/x` and Deno's `@std` are kept the same way. They are apart
  from the standard library so that each can have versions of its own, and a
  second name when it must break, which the standard library never can:
  Python's standard library holds modules that could neither be fixed nor
  removed for decades. A package another owner wrote becomes approved by
  moving to `truss`, which is a rename for its users.

A small prelude of names that nearly every program needs (built-in types,
`Option`, `Result`, the core collections and traits, and the standard
capabilities) is in scope
in every file. The prelude is the same everywhere: projects cannot define their
own, and code cannot hide a prelude name with its own definition. A reader or
an LLM can therefore rely on `List` or `Result` meaning the same thing in every
file of every project.

A package cannot define a type with a prelude name. So a name is in the
prelude only if signatures in most programs use it. `Path` and `SystemError`
are in the prelude. `Pair`, `Indexed`, and `Literal` are not, because a
package may want those names for its own types. They are `core::Pair`,
`core::Indexed`, and `text::Literal`.

### Standard library conventions

- **Each module is one subject, one level below `standard`:**
  `standard::json`, `standard::files`, `standard::time`. Code always
  writes a name with its module, so a type's name does not repeat the
  module's: `collections::Deque`, `time::Date`, `json::Value`. Go nests
  modules by category, as in `encoding/json` and `crypto/sha256`. The
  category is not written at the use site, so it only adds something to
  remember. An LLM that wants JSON writes `use standard::json` without
  knowing a category.
- **Subdirectories hold files that no one imports:** the methods and
  `impl`s of types declared in the parent module, and the real capability
  implementations in `standard::system`.
- **Every method of a view also exists on its owner.** `Slice` and
  `StringSlice` define the methods that read elements or change them in
  place. `List`, `Array`, and `String` define the same methods and forward
  to the view, so `mut names.sort()` works without writing `names[..]`.
  Rust gets this from auto-dereferencing at method calls. Truss converts an
  owner to its view only at a parameter, so the standard library declares
  the methods. Methods that change the length, such as `push` and
  `truncate`, exist only on the owner.
- **Methods that work on any collection are provided methods of
  `Iterable`.** `fold`, `map`, `filter_map`, `count`, and `find` are
  written in terms of `each`. A user's collection gets all of them by
  implementing `each`. Methods that need an index are `Slice`'s.
- **A collection method takes a pure callback. An `Option` or `Result`
  method takes a callback that may use capabilities.** `map`, `filter`,
  and `sort_by` call the callback once per element and may later run it in
  parallel, so the callback is pure. `Option.map`, `Result.and_then`, and
  `unwrap_or_else` call the callback at most once, in place of an `if`, so
  they take a capability parameter. To run an effect for each element,
  write a `for` loop.
- **A lookup that can miss lends an `Option`.** `items.first()`,
  `ports.get(name)`, and `heap.peek()` have the result `lends
  Option[Element]`. The caller reads the element for one statement and
  nothing is copied, whatever the element type. A method that removes the
  element, such as `pop` or `take`, returns an owned `Option`.
- **A capability declares only primitive operations.** `FileWrite` has
  `open`. `files::write_with`, `files::copy`, and
  `files::write_atomically` are ordinary functions that call it. A
  narrowing implementation or a test fake then has few methods to write,
  and every helper works with every implementation.
- **Every operating-system failure is a `SystemError`,** whichever
  capability made the call. Code that reads a file and sends it over a
  connection handles one error type. Each parser has its own error type,
  which carries the position of the error in the input.
- **Text in an embedded language is a tagged template.** `Regex`,
  `json::Value`, `url::Url`, `files::Glob`, `time::Layout`, and
  `processes::Command` are tags. The compiler validates the literal text,
  and an interpolated value cannot be parsed as syntax. A
  `processes::Command` is a program and an argument list. It is never a
  string passed to a shell.
- **`Type.parse(text)` parses text,** through the `Parse` trait. `From`
  and `TryFrom` convert between types. `Display` formats a value for
  people.
- **A generic method's time counts its bounds' methods.** `contains` on a
  slice promises `O(self.length() * time(Element.equal))`, and `sort`
  promises `O(n * log(n) * time(Element.compare))`. A bound of
  `O(self.length())` would be false for a list of strings, where one
  comparison is not one step. The two other ways to make it true were
  worse. A promise of `O(1)` on `Equal.equal` could not be kept by `String`.
  A second trait for types that compare in constant time would give every
  generic method two versions. With the term, a `List[Int64]` gets the
  plain bound, because `Int64`'s comparison promises `O(1)`, and a
  `List[String]` gets an honest one.
- **A write reports at most the bytes it was given.** `Handles.write` and
  `streams::Writer.write` ensure it, so it is proven for every
  implementation: the operating system's, a fake's, and a package's own
  writer. `write_all` relies on it to find the bytes that are left. When a
  write that was given bytes takes none, `write_all` returns
  `SystemError.NothingWritten` and does not try again, as Rust's
  `write_all` returns `WriteZero`.
- **Each capability ships with its test fakes,** in the capability's
  module: `time::ManualClock`, `random::SeededRandom`,
  `files::MemoryFiles`, `console::CapturedConsole`, `log::CapturedLog`.
  The narrowing implementations are there too, such as
  `files::FilesWithin` and `network::HostsAllowed`.
- **`files::MemoryFiles` is a file system, not a table of contents.** It
  has directories, symbolic and hard links, permissions, modification
  times, and open files with positions, and it returns the error that the
  operating system returns for each misuse: `NotFound`, `IsADirectory`,
  `NotADirectory`, `DirectoryNotEmpty`, `AlreadyExists`,
  `PermissionDenied`. A test of error handling is only as good as the
  errors the fake can produce. A file that is removed while it is open
  stays readable through its handle, as on POSIX systems. It implements
  `Handles` for its own files, so `FileReader` and `File` work on it as
  they do on the real file system.
- **`simulation::World` fakes every capability at once.** It is an
  in-memory machine: a file system, a network between its own hosts, a
  clock that advances when every task is blocked or when the test says,
  programs that return what the test scripted, tasks scheduled by a seed,
  and fault injection. FoundationDB tests its database this way. A test
  that opens both files and connections provides a `World`, because one
  provider must implement `Handles` for every handle, as the operating
  system does.
- **A `World` is a reference to its state.** It implements `Tasks`, so its
  methods are not made mutually exclusive by a mutex, and several tasks
  call them. Its state is therefore in the cell that a channel's queue is
  in, and each capability method is one pure update of the cell. The
  method first lets the seed switch to another task, so a test explores
  the orders of the calls. A plain record, `simulation::Setup`, holds what
  the world starts with, because the cell can be read only where `Tasks`
  is available.

## Visibility

- **Private (the default):** visible only within the file.
- **`internal`:** visible anywhere in the package.
- **`public`:** visible to other packages.

Defaulting to private makes keeping code modular the easiest option.

A public signature cannot mention a private or `internal` type, and neither
can a public type's visible fields, as in Rust and Swift. Code in other
packages could never name such a type.

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

There is no level between `internal` and `public`, such as one for the
packages of one project. Swift's `package` level and Go's `internal`
directories work because the code they span is versioned as one unit. Truss
versions each package on its own, so two packages that shared more than
their public definitions could be paired at versions that were never
checked together. Code that shares its internals belongs in one package,
which costs nothing, since a package is not a unit of building (see
[Packages](#packages)). Within a project nothing is lost: `public` there
promises nothing until a package is published.

## Packages

A package is the unit of every boundary Truss checks. It is the first part of
every path into it, the reach of `internal` and of `opaque`, where a type's
methods and a trait's `impl`s may live, what a manifest grants capabilities
to, and what is published and given a version. A package with a `main`
builds one program.

- **A package is not a unit of building.** Results are kept for each
  definition, so splitting a package makes no build faster and joining two
  makes none slower. Rust's crates and Bazel's targets are split to keep
  builds quick, which puts boundaries where the build wants them. A Truss
  package is split only where someone wants a boundary checked.
- **Every kind of package works one way.** A package is named by a path
  that is the same in every file of every project, and where its code comes
  from follows from the name:

  | Kind | Named | Its code | Its version |
  |---|---|---|---|
  | The standard library | `standard` | Part of the toolchain | The toolchain's |
  | A project's own | Its manifest's name | Under the project's directory | None |
  | From the registry | `owner::name` | Fetched, and kept by the hash of its content | In the project's lock file |

- **A package's program starts at the `main` of its `main` module,** so
  finding it is one lookup and not a search of the package, as with Cargo's
  `src/main.rs`. A package builds at most one program, so a project with
  several programs has a package for each, and a library is a package with
  no `main` module.

### Projects

A project is the packages that are worked on together: every package in the
directory tree under a manifest that has a `[project]` table. A package with
no such manifest above it is a project by itself, so a single package needs
nothing more than its own manifest.

- **Every package under the project's root belongs to it.** There is no
  list of members, as Cargo's `[workspace]` and Go's `go.work` have. A list
  is one more file that every agent adding a package must edit, and so one
  more place for two agents to collide.
- **Packages find each other by name, never by a path.** A dependency names
  a package, and if the project has a package by that name, that is the one.
  Cargo's `path = "../geometry"` breaks when a directory moves, and says in
  every manifest where another package is kept. This is the rule for
  modules, which have no relative paths either.
- **A project's package takes the place of the registry's package of the
  same name.** A copy of `acme::geometry` put in the project is the
  `acme::geometry` every package of the build uses. That is how a
  dependency is fixed ahead of its owner, and how a library is worked on
  together with a program that uses it. Cargo's `[patch]` and Go's
  `replace` are tables for this. In Truss the name already says which
  package is meant, so there is nothing more to write, and the copy is in
  the repository for a reviewer to see.
- **A project has one lock file,** at its root, with the version of every
  registry package any of its packages uses, as a Cargo workspace has.
- **A project's own packages have no versions.** They are the code being
  worked on. A version is what the registry gives a package when it is
  published.

### Package names

- **A registry package is named `owner::name`,** and is written that way in
  code, as in `use acme::geometry::vector`. An owner is an account on the
  registry, and only its owner publishes under it. crates.io and PyPI have
  one flat list of names, where a name is whoever took it first, and a
  package whose name is one letter from a well-known one is how much
  malware arrives. LLMs make this worse: they make up names of packages
  that do not exist, and attackers publish under the names they make up.
  With an owner in the name, who published the code is in every path that
  uses it, and a reviewer who trusts `truss` and `acme` can see at once a
  path that starts with neither.
- **The name in code is the registry's name, with no other.** Cargo lets a
  manifest give a package a different name, and Go an import. Either is an
  alias, which Truss has none of: a path is written the same everywhere and
  found by searching for it. Go's import paths and npm's `@scope/name`
  put the registry's name in the code in the same way, and Java's and PHP's
  conventions do.
- **A project's own package may have a name of one part,** such as
  `weather`, and must have an owner in its name before it is published. A
  name of one part cannot be the owner of another package of the build, so
  that every path reads one way.
- **A name is one package for good.** The registry never hands a name, or an
  owner, to someone else, and never removes or replaces a version that was
  published under one.
- **`standard` is the standard library, and the owner `truss` is the Truss
  project's,** for its approved packages (see
  [The standard library and prelude](#the-standard-library-and-prelude)).

### Versions

- **A build holds one version of each package.** Definitions are named by
  path, and a path means one thing. Cargo and npm let two versions of one
  package into a build, and then one path names two types: Rust's "expected
  `Vector`, found `Vector`" is the error that results.
- **So a release never breaks what an earlier one of the same name
  offered.** A change that would is published under a new name, the old one
  with `_v2` after it, as Go requires `/v2` in the import path of a module's
  second major version. `acme::geometry` and `acme::geometry_v2` are two
  packages. Both can be in one build, and one file can use both while its
  code moves over. Cargo and npm instead leave this to each author's care,
  and breaking changes in releases that claimed to be compatible are
  routine.
- **The registry checks it, from the signatures.** GOALS.md has the
  signature say everything important about a definition, so whether a
  release keeps its promises can be read from the two releases. A release
  is compatible with the one before when:
  - every public definition is still there, at the same path
  - a function, method, or theorem has the same parameters and result, no
    capability more in its `uses`, a `requires` that the old one implies,
    an `ensures` that implies the old one, and no cost greater than before,
    which is how an `impl`'s method may differ from its trait's (see
    [Traits that require other traits](#traits-that-require-other-traits)),
    and a method that could be pulled still can be
  - a type that shows its fields has the same fields, variants, and
    invariant; an opaque type may change everything inside it
  - a trait or capability has the same methods, associated types, required
    traits, and laws, and at most gains methods that have bodies, since
    anything else it gained would have to be added to every `impl` in
    another package
  - every `impl` is still there
  - a constant has the same type and value, since a constant's value
    reaches the types and patterns of its users
  - a package that ran on every target still does (see
    [Integers](#integers))

  Elm's registry checks releases the same way, from types alone, and
  `cargo-semver-checks` and Go's `gorelease` check what they can outside
  their registries. Truss's signatures hold more, so the check covers more.
- **Bodies are not promised.** A release may change what a function
  computes within its contract, and that is how a fix reaches its users,
  under the same name. A body the prover reads as its function's definition
  (see [What a function means to the prover](#what-a-function-means-to-the-prover))
  is no exception, nor is a parameter's default: a proof in another package
  that leaned on one is checked again after an upgrade, and may need
  repair. What a package's users are meant to rely on goes in an `ensures`,
  where it is promised.
- **The registry gives each release its number.** The first is 1.0.0. After
  that, a release whose public signatures are all unchanged gets the next
  patch number, and one that added to them gets the next minor number, as
  Elm's tools work a release's number out from what changed. The first part
  is the number in the
  package's name, 1 where the name has none, so `acme::geometry_v2` starts
  at 2.0.0. An author never chooses a number, so a number is never wrong
  about what changed.
- **There are no 0.x versions,** as in Elm. A version that may break at any
  release cannot be the one version of its name in a build. A package whose
  shape is still changing publishes `_v2`, then `_v3`, and its users move
  when they choose.
- **A compatible release can still surface two kinds of error.** A name it
  added can clash with one a user of it defined, such as a method added to
  a type for which another package implements a trait with a method of the
  same name (see [Methods](#methods)). And a contract that got stronger is a
  different question for the solver, which is not certain to answer it
  within its limits. Both are errors that say what is wrong, never a change
  in what code does. A project that meets one holds the upgrade back, or
  keeps a fixed copy of the package it breaks in the project until its
  owner publishes one.

### Choosing versions

- **A build uses the newest version that any of its packages was checked
  with,** and nothing newer. Every published package records the version of
  each registry package it was published with, its dependencies and theirs,
  and a project's lock file records the same for the project. The version
  of a package in a build is the highest that the project or any package of
  the build records. This is Go's minimal version selection.
- **Nothing new enters a build until someone asks.** Cargo and npm choose
  the newest release that a range allows, each time versions are chosen
  afresh. A release published an hour ago is then in every such build,
  which is how a compromised release of a popular package reaches
  thousands of machines before anyone has read it. Under Truss's rule a
  release reaches a build only when someone upgrades to it, or to a package
  that was published with it.
- **There are no ranges and no solver.** Every version under one name is
  compatible with those before it, so "at least this one" is all a
  requirement can say, and the highest of several is the answer. Choosing
  versions among ranges is NP-complete, and its answer changes as packages
  are published. This rule's answer depends only on the lock file and the
  records of the packages it names, so it is the same on every machine, on
  every day.
- **Versions are written only in the lock file.** A manifest names a
  package's dependencies and what each may do. `truss add` and
  `truss upgrade` look versions up and write the lock file. An LLM does not
  know which versions exist today, and one written from memory is stale or
  made up, so no file a person or an agent writes by hand holds one.
- **The lock file names content.** Beside each version is the hash of the
  package's files. A build fetches what the lock file names when it does
  not have it, and uses nothing whose hash differs. Fetching by hash changes
  no answer, so it needs no command. Choosing versions never happens unless
  asked for.
- **Two changes to a lock file always merge.** For each package the merged
  line is the higher version, and the rest follows from the rule above.
  A lock file written by a solver is one of many valid answers, so two of
  them cannot be merged without solving again, which may bring in versions
  neither side had.
- **An upgrade is tried before it is made.** `truss upgrade` checks the new
  versions in a state of their own, as a rename is checked, and reports
  what the change reaches: the signatures the project reads that changed,
  the packages that enter the build, and each package that would hold a
  capability it did not. The upgrade is then a decision made with its
  consequences in view.

### The registry

- **A package is published as its source,** and that is all the registry
  holds of it: its manifest, its modules, its lock file, and the
  documentation beside them. There is nothing built and nothing generated,
  so what a reviewer reads in the registry is exactly what compiles. A
  release whose published files differed from its repository's is how the
  xz backdoor was shipped.
- **Content is checked against a public log.** The registry keeps an
  append-only log of every version's hash, as Go's checksum database does,
  and the toolchain checks that the hash it puts in a lock file is in the
  log. So the registry cannot give two users different code under one
  version, a copy from a mirror needs no trust, and a company's own
  registry or mirror is a directory of files.
- **A package is published only when it is finished:** it has no
  diagnostics, every proof is done, it has no `todo` and no `echo`, its
  tests that have no `uses` pass, and every dependency is a registry
  package. The registry checks all of this again itself, which is safe to
  do with a stranger's code, because nothing that runs while checking,
  proving, or testing has a capability.
- **Proofs are shared, signed.** The registry signs the solver's answers
  and the test results it computed for a release, under the keys those
  results always have (see [DATABASE.md](DATABASE.md)). A build needs the
  proofs of the dependency code it can reach, as it needs its own, and
  finds them signed or else proves them itself. The toolchain trusts the
  registry's key unless a project says otherwise. Proving a whole
  dependency tree on a machine that starts with nothing is the cost
  GOALS.md sets out to remove, and an agent in a new container is such a
  machine. The trust is in a claim anyone can check: every signed result
  is a function of its key, so a registry that signed a false one is caught
  by whoever computes it again.
- **A new toolchain proves the registry again,** as far as it changed what
  is proven, since a proof is kept under the solver and the question that
  made it. A toolchain that can no longer prove what the last one proved
  of the approved packages is not released.
- **A release can be marked as one not to use,** by its owner or the
  registry, with the reason. It stays where it is, and builds that use it
  still build: a mark that broke them would let one compromised account
  stop every project that depends on it. `truss upgrade` never chooses a
  marked release, and says so when a project is on one.

### What packages do without

- **Optional parts of a package,** such as Cargo's features. They exist to
  keep unwanted code and dependencies out of a build. In Truss code that
  nothing reaches is never compiled, a package that nothing reaches is
  never granted anything and runs nothing, and a grant covers only what a
  program names, so there is nothing for a switch to save. Features cost
  Cargo's users builds that work only with some sets of switches.
- **A second list of dependencies for tests.** A package has one list.
  Which of its dependencies only its tests reach is worked out when it is
  published, from what its definitions read, and a project that uses the
  package does not take those on.
- **Dependencies on a git repository or a directory.** A package is one of
  the project's or one of the registry's. Code that is not published is
  worked on in the project that uses it.
- **Build scripts and code generators.** Nothing in a package runs to
  build it (see [Dependencies](#dependencies)).

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
looks like with `requires`, such as `is_valid_template(template.literals)`. The
literal text is a constant, so the compiler proves the clause by running the
check on it, as compiled code, the way a test runs. This is possible because
functions used in specifications are pure and must terminate, so a check
always finishes and needs no step limit. Each result is cached by the check
and the literal text. This gives:

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
narrow place: `result` in `ensures`, `old` and `identical` in specifications, `yielded` and
`finished` in the contracts of lending and yielding methods, and the words
of `cost` clauses, such as `time`, `calls`, `finite`, and `log`. Reserving
those would ban names like `result` and `time` from all code to serve a few
specifications. They are not contextual keywords in the lexer either: the
lexer reads them as names, and the parser recognizes them by their spelling
where a clause expects them, as C#, Kotlin, Swift, and Rust do with their
contextual keywords. A lexer mode for them would have to know where each
clause ends, which is the parser's job. Words that other languages use as keywords, such
as `loop`, `async`, and `where`, are reserved now, so that adding one later
breaks no code and borrowed code gets a clear error.

**Names are ASCII,** as in Zig and Gleam. A name that looks like another but
is spelled with different characters, such as a Cyrillic `а` in place of a
Latin `a`, is a known way to slip a malicious change past review, and it
matters for a language built for supply-chain safety. Allowing every script
safely takes a large mechanism that still leaves gaps: normalization, rules
about mixing scripts, Unicode's list of look-alike characters checked across
every name in a package, and all of it changing with each Unicode version.
ASCII names rule the attack out instead. Within ASCII, look-alikes such as
`l` and `1` are a matter of fonts. The cost is that a team cannot name things
in its own language. Text in any language still goes in strings, including
test names and messages, and in documentation. Keywords and the standard
library were ASCII already.

**Each language version pins a Unicode version.** Which characters are
invisible, and so forbidden in source files, comes from Unicode data, and the
data changes every year. If the compiler used whatever version its libraries
had, as Rust and Go do, whether a file compiles would depend on which build of
the compiler checked it, and the first compiler in OCaml and the later one in
Truss could disagree. Java names a Unicode version in each language
specification, and Truss does the same. Moving to a new Unicode version comes
with a new language version, like a change to the prelude. Strings are not
limited: a string can hold any character that is not forbidden, including
ones from later versions.

**Constants are values, so they are `lower_snake_case`:** `math::pi`,
`UInt8.maximum`, `Instant.epoch`. A separate case for constants, such as
`MAX_SIZE`, would give the lexer a third kind of name, and an
`UpperCamelCase` constant could not be told apart from a type or
constructor.

**A constant in a pattern is written by its name.** A bare name that names a
constant in scope means that constant; any other bare name binds. This is
Rust's rule, and in Rust it is a known trap: a misspelled or missing constant
silently becomes a binding that matches everything. Truss closes the trap with
rules Rust has only as warnings. A misspelled constant that matches everything
makes later arms unreachable, which is an error. If it is the last arm, it
leaves an unused binding, which is also an error, since a real constant can
almost never be the last arm of an exhaustive `match`. Adding a constant to a
file can turn an existing binding into a comparison, but the `match` then no
longer covers every case, which is an error too. The no-shadowing rule already
means a name that is a constant cannot also be a binding, so reading it as the
constant is the only reading consistent with that rule. Python's `match`
instead lets only qualified names be constants, which would leave a file's own
constants needing guards. A constant used in a pattern must have a type with
structural equality (see [Equality, ordering, and deriving](#equality-ordering-and-deriving)),
so that matching it and comparing it with `==` agree, as Rust requires. A
hand-written `Equal`, or a derived one over floats, could disagree with what
the pattern matches.

**Imports bring in modules, not individual names.** After
`use standard::json`, code writes `json::parse(text)`. Every
name that is not local or from the prelude shows where it comes from, right
where it is used. Two modules can both define `ParseError` without a clash,
so Truss needs no import aliases. Aliases would let the same thing go by different
names in different files, which makes code harder to search, rename, and
predict.

**Every module path starts with a package name,** including inside the
package itself: a file in the `weather` package writes
`use weather::forecast::hourly`, as other packages do, following Go's full
import paths. A path is then written the same everywhere and can be found by
searching for it. Rust's `crate::` would survive renaming the package, but
code inside a package would look different from code outside it, and
relative paths such as `super::` make one module look different depending on
where it is named from. Renaming a package is rare and is a mechanical
rename. A registry package's name has its owner in front, so a path into one
starts `acme::geometry` (see [Package names](#package-names)), and holds no
version, so an upgrade changes no path.

**Modules in a package may depend on each other in a cycle.** Each top-level
definition is kept on its own, so dependencies are tracked between
definitions, not files, and a cycle between files costs nothing. Packages
cannot depend on each other in a cycle.

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
