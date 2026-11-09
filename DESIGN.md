# Truss Design Decisions

This document records what Truss code means and why. For how code is written,
see [SYNTAX.md](SYNTAX.md). For the goals behind these decisions, see
[GOALS.md](GOALS.md). Nothing is built yet. This is the design agreed so far.

## Source code

- **Text files are the source of truth.** Programmers and tools edit ordinary
  files.
- **The compiler stores each top-level definition by its content.** It parses
  each definition, resolves its names, and hashes the result. Whitespace and
  the order of different kinds of clause do not affect the hash, so
  reformatting never triggers a rebuild. The order of clauses of one kind
  does: each `requires` may rely on the ones before it, as in Dafny, so
  swapping two of them can change what they mean.
- **Each result records what it depended on.** This lets builds, tests, and
  proofs redo only the work a change actually affects. See
  [Incremental builds](#incremental-builds).
- **A function's signature and body are hashed separately.** Type checking and
  proofs in callers depend only on the signature. Changing a body without
  changing its signature, such as filling in a `todo`, re-checks no callers.
  Only code generation and the affected tests run again. The signature is
  hashed in two parts: its interface, which callers' types depend on, and its
  contract, the `requires`, `ensures`, `decreases`, and `cost` clauses, which
  only callers' proofs depend on. Strengthening an `ensures` re-proves
  callers but type-checks none of them again.
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

### Incremental builds

A definition's hash is a key, and the work done on the definition is stored
under it. Each definition is parsed, has its names resolved, and is hashed
once per change; the hash is what tells whether it changed. Type checking then
produces the definition's checked form: the type of every expression, and the
exact method, variant, field, `impl`, or associated type each name turned out
to mean. The checked form is stored under the hash together with a *trace* of
everything type checking relied on, and proofs, code generation, and tests are
stored the same way. A result is reused as long as every entry in its trace
is unchanged. "Build Systems à la Carte" (Mokhov, Mitchell, and Peyton Jones,
2018) calls these verifying traces, and Shake and Rust's incremental compiler
use them.

- **A hash names other definitions by their module path and name, never by
  their hash.** Unison refers to code by hash, so a function's hash covers its
  callees' hashes, and changing one body changes the hash of everything that
  reaches it. Truss keeps a definition's hash to its own text, and records
  what it depends on in its trace instead.
- **A trace records two kinds of dependency:** the signature hash of each
  definition used, and each lookup made, keyed by where and what name: the
  members of `List` named `length`, the `impl`s of `Add` for `Instant`, the
  constants named `not_found` in a file. When a definition is added, removed,
  or renamed, only the lookups with its scope and name are made again. Swift's
  incremental builds keyed such lookups by name alone, and rebuilt far too
  much. Truss's rules keep each lookup to a few places: methods live with
  their type, an `impl` lives with its trait, its type, or a type its trait's
  arguments name, and an unqualified constant can only come from the same
  file.
- **Work stops as soon as an output comes out the same.** When a re-checked
  definition's signature is unchanged, its callers are not checked again;
  when generated code is unchanged, tests are not run again. This *early
  cutoff* is what makes editing a body cost O(change).
- **Proofs and tests are keyed by forms with names replaced.** References in
  a proof obligation or a compiled test are numbered rather than named, so
  renaming a definition or moving it to another module re-checks its callers'
  types, which is cheap, but finds their proofs and test results already
  done.
- **Positions are relative to their definition.** Panics, `echo`, failed
  asserts, and debug information record where they are within their
  definition, and a table built at the end of the build turns that into a
  file and line. Otherwise adding a line at the top of a file would change
  the output of every definition below it.
- **Every stored result is deterministic and canonical,** with no fresh
  numbering, no hash-map iteration order, and no timestamps. Early cutoff
  compares outputs, so any instability would defeat it.
- **Optimizations record the bodies they read.** Inlining one definition into
  another makes the caller's code depend on the callee's body, so it is
  recorded in the caller's trace. Development builds do not inline across
  definitions of the packages being worked on, which keeps rebuilds narrow.
  They do inline from the standard library and from dependencies, whose
  bodies change only with a new toolchain or a new version in the manifest,
  so this never widens a rebuild while editing. Cargo users get the same
  effect by hand, by optimizing dependencies in development profiles.
  Release builds inline across everything.
- **Each stage of the compiler is versioned on its own:** the parser, the type
  checker, the prover with its pinned solver, code generation, and each rule
  for deriving. A release that changes code generation leaves every proof
  valid, and a new solver re-proves only what that solver checked.

### The hash format

Content hashes last: they are stored in caches, shared between machines, and
used to tell whether code changed. So they are defined over a specified
encoding, not over any compiler's data structures.

- **The encoding is specified and versioned,** so the first compiler, written
  in OCaml, and later compilers written in Truss produce the same bytes for
  the same definition. Deterministic CBOR (RFC 8949, section 4.2), which has
  exactly one byte form for each value, is a suitable base. Git and Nix
  specify their formats the same way.
- **Every hash names its encoding version and hash algorithm** in a prefix,
  as multiformats does, so either can change later through an explicit
  migration rather than silently.
- **The hash format has its own version,** apart from the versions of the
  compiler's stages, so a new compiler release changes no content hash
  unless the language itself changes.
- **What is hashed:** the kind of definition, its structure, its resolved
  names, local variable names, literal values, and the order of clauses
  within each kind. Field order is hashed only for types with a derived
  `Ordered`.
- **What is not:** whitespace and layout, the order between kinds of
  clause, positions in the file, which are kept apart and relative to their
  definition, and how a literal is written. `0xFF` and `255` hash the same,
  and so do a raw string and an ordinary one with the same text. The parsed
  tree keeps how each literal was written, so `truss fmt` can print it back
  that way.
- **Local names are hashed,** unlike in Unison, which hashes no names at all.
  Truss shows local names in compiler messages and `echo` output, and a
  result cached under a hash that ignored them would show an old name.
  Renaming a local re-checks one body.

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
  test's fake implementation hands out plain values. Types cannot define
  destructors.
- **What can fail is explicit, and buffered data is never lost silently.**
  Closing a file that was only read, or a socket, loses nothing, so it
  happens silently. Flushing a buffered writer can fail, and losing its data
  would go unnoticed, which is how Rust's `BufWriter` loses writes when it is
  dropped. So a buffered writer is only ever lent, inside a scope:
  `FileWrite.write_with(path, fn(writer) { ... })` lends the writer `mut` to
  the function, then finishes it, and returns the first error from the
  function or from finishing. This is Python's `with`, Kotlin's `use`,
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
  stored past its function.
- **A call's result views what its arguments view.** A function may return a
  view only of what reached it through its parameters, never of its own
  locals. The caller then treats the result as viewing everything its
  read-only and view-typed arguments view, so it needs no annotation.
  `text.trim()` views `text`, and `found.unwrap_or(default: backup[..])`
  views both `found` and `backup`. Rust instead names which input a result
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
  reference to track across statements. Disjoint parts of one collection
  can still be passed `mut` side by side, because the prover shows the
  ranges do not overlap.
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
  does, with the same proof rules.
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
- **Read-only and owned yields can be pulled.** Internal iteration alone, as
  in Ruby's `each`, cannot advance two sequences together, so it cannot
  write `zip`, merge, `peek`, or pause and resume. Pulling a yielding method
  through a cursor gives those, as C#'s iterators and Python's generators
  do. The same rule covers both uses: a method may end at any `yield`.
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
  Whether a method can be pulled is worked out from its body. It is the one
  fact callers take from a body rather than a signature, and the tools show
  it with the signature. Early cutoff means a body edit that keeps the
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
- **Traits can take type parameters, which covers what overloading is mostly
  wanted for.** `Int64.from(count)` picks an `impl` of `From[Source]` by the
  type of `count`, and `instant + duration` picks an `impl` of
  `Add[Duration]`. Free overloading by parameter type would cost what Truss
  cares about most. Swift's "expression too complex to type-check" errors
  come from overloads combined with literals typed by context, which Truss
  also has. Adding an overload anywhere can change which function an existing
  call resolves to, which widens what each definition's hash depends on. And
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
  existing call does. In Truss, a type's own method and a trait method with
  the same name is an error at the `impl`, and two traits with the same
  method name is an error at the call. Upgrading a dependency can therefore
  break a call only with an error that names both sides, never by changing
  what it does. Adding a public method to a type can break another package's
  `impl`, so tools that check versions treat it as possibly breaking.
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
- **Lawful float comparison costs a little.** Treating every NaN as equal
  turns `a == b` into roughly `a == b || (a != a && b != b)`, and ordering
  NaN last adds a similar test to `<`. That is a few instructions per
  comparison, which can matter in a hot loop or for vector instructions. The
  `ieee_` comparisons are the exact, single-instruction escape hatch. Making
  floats IEEE by default would instead cost what Rust pays: floats that
  cannot be sorted, used as map keys, or compared in a derived `Equal`.
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
  implicitly.
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
  new `impl` checks only that `impl`, never the callers.
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
- **Integer division rounds toward zero, and `>>` on a signed integer copies
  the sign bit,** as in C, Rust, Go, and Swift and as the hardware does.
  Rounding down is available as a method, as Rust's `rem_euclid` is.

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
- **Grants are checked at signatures.** A call to a dependency's function, or
  a `provide` of its type, is checked against the dependency's grant, from
  the callee's `uses`. The dependency's bodies are already checked against
  its own signatures, so nothing it does can go further. A dependency that
  offers both a client and a server needs only the grants for what the
  program calls.
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
  that, so amortized bounds compose soundly in Truss. Writing potentials is
  mostly the standard library's job.
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

## Termination

- **A `time` clause promises the function terminates.** `cost time finite`
  promises termination without giving a bound.
- **A function without a `time` clause might not terminate.** No separate
  marker is needed.
- **Functions used in `requires`, `ensures`, laws, or proofs must have a `time`
  clause.** Otherwise the proof system would not be sound.
- **Recursion over the parts of a value needs no annotation.** A recursive
  call on a field taken out of a parameter by a pattern clearly ends, as Lean
  accepts structural recursion automatically. Other recursion states a
  `decreases` measure, as in Dafny, F*, and SPARK, compared in order when
  there are several. Truss does not guess a measure when none is written, as
  Dafny does: a structural check plus an explicit clause is more predictable
  than a guess that may or may not work.
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

**Specifications have implication, `a ==> b`,** as Dafny, Verus, Prusti,
and ACSL write it. "If this holds, then that holds" is the most common shape
of a specification, and writing it as `!a || b` hides what it says. It binds
more loosely than `&&` and `||`, the reading every one of those languages
shares, and it does not chain, like comparisons. It exists only in
specifications, because code already has `if` and `!a || b`, and two
spellings there would buy nothing. Laws take `requires` premises, as
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
  since the signature already says it.

Float arithmetic in specifications follows IEEE 754, as in code. Exact real arithmetic would
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
- **Literal allocation is counted.** A non-empty list or map literal in a
  function body counts as one allocation in `cost` clauses, and an empty one
  as none. The compiler may keep a literal that is only read in static
  memory, but cost clauses don't depend on that. Constants are different:
  they always live in static memory, so reading one costs nothing.
- **Constant collections are built while compiling.** The compiler builds a
  `Map` or `Set` constant by running the standard library's own insertion
  code while compiling, so its table is ready in static memory and lookups
  cost what they always cost. Hashing has no random key, so the table comes
  out the same on every build. Constants are read-only places, so the table
  is only ever read; an owned, changeable copy is made with `copy()`.
- **Duplicate keys in a map literal are a proof obligation.** Letting the last
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
narrow place: `result` in `ensures`, `old` in specifications, and the words
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
constants needing guards. A constant used in a pattern must have a type whose
equality is built in or derived, so that matching it compares structure, as
Rust requires. A hand-written `Equal` could disagree with what the pattern
matches.

**Imports bring in modules, not individual names.** After
`use standard::file_system`, code writes `file_system::read_text(path)`. Every
name that is not local or from the prelude shows where it comes from, right
where it is used. Two modules can both define `Path` without a clash, so Truss
needs no import aliases. Aliases would let the same thing go by different
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
rename.

**Modules in a package may depend on each other in a cycle.** Each top-level
definition is hashed on its own, so dependencies are tracked between
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
