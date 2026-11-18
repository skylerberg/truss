# Truss Design Decisions

Truss is a language for a time when LLMs write code faster than tools can
build, test, and verify it. Development time then goes to builds, test
suites, bugs, conflicts between agents, and security problems. Truss is
designed to make each of those cheap ([GOALS.md](GOALS.md)).

This document gives the reasons for the design.
[SPECIFICATION.md](SPECIFICATION.md) states the rules of the language, and
[PACKAGES.md](PACKAGES.md) the rules of packages.

## Overview

Four decisions shape the rest of the design.

**Every definition is checked alone, against the signatures it names.** A
signature carries the types, the capabilities, the contract, and the cost of
a function, and the compiler proves that the body meets them:

```truss
public fn binary_search(sorted: Slice[Int64], target: Int64) -> Option[UInt64]
  requires is_sorted(sorted)
  ensures match result {
    Some(index) => sorted[index] == target
    None => !contains(sorted, target)
  }
  cost time O(log(sorted.length()))
  cost allocations == 0
```

This signature has no `uses` clause, so the function is pure. A caller's
types and proofs depend on the signature and never on the body. A reviewer
therefore reads signatures instead of bodies, and an edit to a body
invalidates no caller. The cost is that a signature must state every effect
and every failure of a call: an operation that can fail is a proof
obligation or a declared `Panic`, and there is no `assume`. See
[Proofs](#proofs) and [Incremental builds](#incremental-builds).

**No two names alias a value that either can mutate.** This is mutable value
semantics. A call can then mutate only its `mut` arguments and the state
behind the capabilities it uses, code that runs in parallel has no data
races, and a value is freed when its owner's scope ends, with no garbage
collector. The cost is that a reference cannot be stored. Views, lending
methods, and cursors do the jobs of stored references. See
[Values and ownership](#values-and-ownership).

**Effects are capabilities.** A function that acts outside pure computation
lists the capabilities it `uses`, and its caller provides their
implementations. A test provides fakes, so its result is deterministic and
is cached until the code it runs changes. A dependency has only the effects
that its signatures and its grant allow. The cost is a `uses` clause on
every function that has an effect. See [Capabilities](#capabilities).

**There is no foreign code.** A C function can do anything, so its
capabilities and contract could only be assumed, and the three
decisions above would hold for only part of a program. The cost is reach:
the operating system and special hardware are available only through the
standard library. See [No foreign code](#no-foreign-code).

These reasons recur. A later section cites one by name instead of restating
it:

| Principle | Statement |
|---|---|
| O(change) | Building, testing, and proving an edit cost in proportion to the edit, not to the project. |
| Determinism | A test and a proof give the same result on every run and every machine, so results are cached and no test is flaky. |
| Local reasoning | A statement's types, a function's ownership, and a definition's proofs are decided from that unit and the signatures it names. |
| Nothing hidden | An allocation, a mutation, an effect, a failure, and a transfer of control are each written where they happen. |
| One spelling | A construct has one written form. A second form would make files differ until they are formatted. |
| LLM habits | LLMs write the syntax of other languages by habit. A habit that Truss would read differently is an error, never a different meaning. |
| Parallel agents | Several agents edit one codebase at once. A routine edit touches few files, and two correct edits merge into a correct program. |

## Source files

Rules: [Source files](SPECIFICATION.md#source-files).

The invisible characters behind known attacks are an error anywhere in a
source file, including inside a string literal. A string that needs one
writes it as an escape.

| Characters | Attack |
|---|---|
| Bidirectional controls | Code is displayed in a different order from the order it compiles in: the "Trojan Source" attack (CVE-2021-42574). Truss has no comments, so a string literal is where the attack would hide. |
| Control characters, such as escape and backspace | A terminal hides or rewrites lines in the output of `cat` or `git diff`. |
| Other invisible characters, such as zero-width spaces and Unicode tag characters | Two strings look identical, or a file carries text that a human reviewer cannot see and an LLM reads: a prompt injection. |

The zero-width joiner, the zero-width non-joiner, and the variation
selectors stay legal, because emoji and scripts such as Persian need them.
The rule therefore stops the known attacks and not every covert channel: a
run of variation selectors can still carry hidden bytes in a string. Closing
that channel needs rules for where each character may appear in every
script, so it is left to review tools.

Each language version pins a Unicode version, as Java's specifications do.
The forbidden characters come from Unicode data that changes every year.
Without the pin, whether a file compiles would depend on the build of the
compiler.

## Lexical elements

Rules: [Lexical elements](SPECIFICATION.md#lexical-elements).

### Comments

Truss has no comments. A comment goes stale without the compiler noticing, and
LLMs fill code with comments. The content of a comment moves into a form that
the compiler checks:

| Content of a comment | Form in Truss |
|---|---|
| The purpose of a definition | Its name |
| The behavior of a function | Its signature, `requires`, and `ensures` |
| A fact that always holds | An invariant or a law |
| The cost of a call | A `cost` clause |
| An example of use, or a requirement | A test and its name |
| The reason for a piece of code | A name, such as `treat_missing_account_as_empty` |

### Names

Rules: [Names](SPECIFICATION.md#names).

**Names are ASCII.** This avoids confusable character attacks and is simple.

### Keywords

Rules: [Keywords](SPECIFICATION.md#keywords).

| Rule | Reason |
|---|---|
| Keywords of other languages, such as `loop` and `async`, are reserved for later use. | Adding one later breaks no code. |

### Number literals

Rules: [Number literals](SPECIFICATION.md#number-literals).

| Rule | Reason |
|---|---|
| A literal takes its type from its context, and has no suffix. | *One spelling:* `3` is written one way for every integer type. |
| A literal operand takes the type of the other operand. | Go's untyped constants work this way. The rule never consults the set of `impl`s, so adding an `impl` never changes the type of an existing literal. Rust lets the search for an `impl` decide, so an `impl` added later can make an existing call ambiguous. |
| A literal that no use decides takes the first default type that its uses allow. | A shift amount and a literal too large for `Int64` need no rule of their own. |
| Only the sealed integer traits take part in choosing a default. | No package can implement them, so adding an `impl` never changes the default of an existing literal. Haskell limits its defaulting to the standard classes for the same reason. |
| A literal has the methods of a trait that every type of its kind implements. | `count.saturating_add(1)` would otherwise fix `count` at `Int64` before a later use decides it, and the type of a local would depend on the order of its uses. |
| A leading zero is an error. | `0755` is octal in C and the shell, where it sets file permissions. Read as decimal, it would silently set the wrong permissions (*LLM habits*). |

[Functions](#functions) explains how a local that is declared from a literal
gets its type.

### String literals

Rules: [String literals](SPECIFICATION.md#string-literals).

```truss
let script = Shell$$"""
  echo "${HOME}/$${folder}"
  """
```

In `script`, `${HOME}` is text and `folder` is interpolated.

| Rule | Reason |
|---|---|
| A raw string has no escapes. | A regular expression or a Windows path keeps its backslashes, without the doubling that causes bugs. |
| The closing `"""` sets the indentation, and every line starts with it. | A raw string is indented with the code around it. A line that mixes tabs and spaces is an error instead of a silent change to the text. |
| An interpolation starts at `${`. | A single `{` or `$` as the marker would need escapes throughout JSON, regular expressions, and shell text. `${` is rare in ordinary text, as JavaScript's template literals show. |
| Text that contains `${` opens the string with more `$`s. | A longer delimiter is already the remedy for text that contains `"""`. A fixed escape such as `$${` would make one sequence special in a string that has no escapes. |

### Rejected sequences

Rules: [Rejected sequences](SPECIFICATION.md#rejected-sequences).

`--x` could mean `-(-x)`, and `//` could be two divisions. Both are errors, so a
habit from another language never compiles to a different program. Rejecting a
sequence also keeps it free: a later language version can give `//` a meaning
without changing existing code.

A stray `;` is rejected, not ignored.

### Line breaks

Rules: [Line breaks](SPECIFICATION.md#line-breaks).

A line break ends a statement when the token before it can end a statement
and the token after it can begin one. This is Scala's rule. It accepts the
layout that Truss code uses:

```truss
type Shape =
  | Circle(center: Point, radius: Float64)
  | Empty

fn area(shape: Shape) -> Float64
  cost time O(1)
{
  todo
}

let active_names = users
  .filter(fn(user) { user.is_active })
  .map(fn(user) { user.name.copy() })
```

| Rule | Used by | Effect on this layout |
|---|---|---|
| The tokens on both sides decide. | Scala, Truss | Accepted. |
| The token before the break decides. | Go | Rejects a variant that starts with `\|`, a clause on the line after a signature, a `{` after the clauses, and a method chain with `.` at the start of a line, which LLMs write by habit. |
| A line continues whenever the next line can continue it. | JavaScript | Accepted, but a line that starts with `(` silently becomes a call of the line before. |

Truss reads a line that starts with `-` as a new statement. If the author
meant a subtraction, the statement leaves an unused value, which is an error,
so the misreading never compiles.

## Files and definitions

Rules: [Files and definitions](SPECIFICATION.md#files-and-definitions).

Nothing about a definition depends on its file or on its position in the
file. [Incremental builds](#incremental-builds) gives the reasons, and
[Modules and visibility](#modules-and-visibility) the reasons for modules.

### Scope

Rules: [Scope](SPECIFICATION.md#scope).

| A binding shadows | Allowed | Reason |
|---|---|---|
| A local or a parameter of an enclosing scope | No | The inner binding loses an update or reads a stale value, as an inner `err :=` does in Go. C# and Java reject it too. |
| A function, a constant, or a theorem of its module | Yes | The shadowing is safe: a call of the shadowed function no longer type-checks. Rejecting it would make it an error to add a definition to one file when another file of the module has a local of that name. Two correct edits could then merge into a broken build (*parallel agents*). |
| A type, a trait, or a capability of its module, shadowed by a generic parameter | No | The head of an `impl` declares the names in its brackets, so `impl Shown for Box[Marker]` would mean every `Box` where the type `Marker` was meant. |

## Types

Rules: [Types](SPECIFICATION.md#types).

### Built-in types

Rules: [Built-in types](SPECIFICATION.md#built-in-types).

**A size, a length, and an index are `UInt64`, and an offset is `Int64`.**
Truss has no integer type of the pointer's width. A proof about a size
therefore holds on every target, and every package runs on every target. A
target with 32-bit pointers, such as 32-bit WebAssembly, keeps 64-bit sizes.

| Rule | Reason |
|---|---|
| A size, a length, and an index are unsigned. | A length is never negative, and a bounds check is one comparison. A subtraction that may go below zero is a compile error, so an unsigned index does not wrap. |
| A `Character` is a Unicode scalar value. | It has a fixed size, so it is `Plain`, and its definition does not change between Unicode versions. A grapheme cluster has no fixed size, and its boundaries change as Unicode adds rules, so a grapheme is a slice of its string. |

### Type definitions

Rules: [Type definitions](SPECIFICATION.md#type-definitions).

**A record with one field is how Truss writes a newtype.** Values with
different meanings get different types, as in
`type UserId(number: UInt64)`.

### Recursive types

Rules: [Recursive types](SPECIFICATION.md#recursive-types).

A recursive variant is marked `indirect`, so the allocation is written where
the type is declared (*nothing hidden*).

### Generic parameters

Rules: [Generic parameters](SPECIFICATION.md#generic-parameters).

Generic code is monomorphized, so a generic function costs nothing at run
time. Monomorphization rules out polymorphic recursion.

### Invariants

Rules: [Invariants](SPECIFICATION.md#invariants).

```truss
public type DateRange(start: Date, end: Date)
  invariant start <= end
```

An invariant moves a fact from signatures into a type. Every `SortedList` is
sorted, so a function that takes one needs no `requires is_sorted(...)`, and
no call site can forget the fact.

**An invariant holds wherever other code can observe the value, and a body
may break it in between.** `SortedList.insert` appends an element and then
moves it into place. No code observes the list while it is unsorted: the
list has no alias, a panic ends the program, and a capability call always
returns to its caller. A private method that takes `mut self` neither
assumes the invariant on entry nor establishes it on return, so `insert` can
call a helper while the list is unsorted. The helper states its own
precondition and postcondition.

| Rule | Reason |
|---|---|
| An invariant belongs to the whole type, never to one variant. | It can state a fact about the whole value, such as a tree being balanced, and a clause after the last variant is unambiguous. A condition on one variant is a `match` in the invariant, or a field whose type carries the condition. |
| A type with an invariant can still expose its fields. | An invariant protects facts about the contents of a value. `opaque` does a different job: it controls where a value is constructed and hides the representation ([Visibility](#visibility)). |

## Values and ownership

Rules: [Values and ownership](SPECIFICATION.md#values-and-ownership).

Truss has mutable value semantics: every variable holds its own value, and
no two names alias a value that either can mutate. A value is freed when its
owner's scope ends, so there is no garbage collector and no runtime beyond
libc. There is no mutable global state either: a top-level `let` is a
constant, so tests can share one process.

Four guarantees made elsewhere in the design depend on this:

| Guarantee | Failure with aliasing |
|---|---|
| A call mutates only its `mut` arguments and the state behind the capabilities it `uses`. | A callee mutates a value through an alias that its signature does not mention. |
| A method may break its type's invariant partway through an update ([Invariants](#invariants)). | An alias observes the half-updated value. |
| The branches of a `parallel` or `concurrent` block have no data races ([Parallelism](#parallelism)). | Two branches mutate one value through two names. |
| Amortized cost bounds compose ([Cost clauses](#cost-clauses)). | Two references to one structure each spend its potential. |

Rust also forbids aliased mutation. It keeps references that can be stored,
and pays with lifetime parameters in signatures and types. Truss gives up
stored references instead, as Hylo does. No signature carries a lifetime,
and the ownership check reads one function at a time: its body and the
signatures it calls (*local reasoning*).

The cost falls on every use of a reference in other languages. Each use has
a replacement, and the rest of this section gives the reasons for each:

| Use of a reference | Replacement |
|---|---|
| Pass an argument by reference | [Parameter modes](#parameter-modes) and [views](#views) |
| Return a reference to a part of a value | [Lending methods](#lending-methods) |
| Iterate with an iterator that borrows its collection | [Loops](#loops) by position, and [cursors](#cursors) |
| Capture a variable in a closure | Capture by view ([Lambdas](#lambdas)) |
| Share mutable state between threads | A capability implementation ([Concurrency](#concurrency)) |

### Parameter modes

Rules: [Parameter modes](SPECIFICATION.md#parameter-modes).

A parameter is read-only unless it is declared `mut` or `own`. The call site
repeats the mode keyword on the argument:

```truss
sort(mut scores)
push(mut names, item: own name)
push(mut names, item: name.copy())
```

| Rule | Reason |
|---|---|
| The call site repeats `mut` and `own`. | *Nothing hidden.* The call shows which arguments it mutates or moves, and a search for `mut scores` finds every call site that can mutate `scores`. |
| A temporary takes no mode keyword. | A temporary has no other owner, so the keyword would tell the reader nothing. |
| `own` can move one field out of a record. | Without a partial move, taking one field means copying it or moving the whole record. |

### Copying

Rules: [Copying](SPECIFICATION.md#copying), [Strings](SPECIFICATION.md#strings).

A copy that can allocate is explicit: a call of `copy()` (*nothing hidden*).
Only a `Plain` value copies implicitly. A `Plain` value has a fixed size and
owns no heap memory, so its copy is a bitwise copy.

The compiler derives `Plain` and `Copyable` from a type's fields. An opaque
type declares them instead. If they were derived from fields that other
packages cannot see, those packages would depend on the fields: adding a
`String` field would break every package that copied the type implicitly. A
type that is not opaque shows its fields, so the same edit is a visible
change to its API.

| Rule | Reason |
|---|---|
| A name bound to a `Plain` value is a copy, not a view. | A `Plain` value is copied wherever it is moved: into a `var`, an `own` parameter, or a field. If a `let` viewed it, `point.x = 7` would be an error while a `let` of `point` is live, where the same code on an integer is accepted. |
| A handle is not `Copyable`. | Copying one would duplicate an operating-system handle, which can fail, and `copy()` cannot fail. |
| Generic code copies only under a `Copyable` bound. | An unbounded type parameter then accepts every type, handles included. |
| A string literal is a `String` constant, copied where an owned `String` is needed. | Every `String` that code mutates or drops then owns its buffer. Copy-on-write needs a run-time test of whether the buffer is static before each write, drop, and copy. |

### Views

Rules: [Views](SPECIFICATION.md#views).

A view is a read-only reference to a value that another variable owns. A
read-only parameter, a `let` bound to a place or to a string literal, the
variable of a `for` loop, and a slice are views:

```truss
let middle = items[1..4]
let total = middle.sum()
mut items.push(9)
```

While a view is live, that is, until its last use, its original cannot be
mutated or moved. This prevents a dangling view: `push` may reallocate
`items`, and `middle` would then view freed memory. The `push` above is
accepted because `middle` is not used after it.

Three decisions let views exist without lifetimes.

**Making a view does not make a copy.** A view is observationally equivalent
to a copy: its original cannot be mutated while the view is live, so a read
through the view returns the value that a copy would hold.

**A view is second-class, as in Hylo.** It can be bound, passed as an
argument, and held in a local record or collection, but it cannot escape the
function that made it. The ownership check therefore never relates a view to
anything outside one function (*local reasoning*), and an edit to one body
invalidates the check of that body alone (*O(change)*). The cost is that no
data structure holds a view after the function returns. Code that keeps a
value takes it as `own` or copies it.

**A returned view is assumed to view every read-only and view argument.** A
signature therefore never says which argument the result views. Rust says
which with a lifetime parameter. Truss's rule over-approximates: an argument
that the result does not view stays immutable while the result is live. The
rule excludes `Plain` arguments, such as indexes, so that case is rare.

| Rule | Reason |
|---|---|
| Whether a type is a view is derived from its fields, and a record that holds a view is a view. | Nothing is declared, and a view cannot escape inside a record. |
| Generic code that keeps a value requires `Storable`. | A type parameter may stand for a view, and the bound stops generic code from storing one. |
| An `any Trait` is a view unless `Trait` requires `Storable`. | `any` hides the type, so the compiler cannot see whether the value holds a view. |
| `mut` access is never stored. | It lasts for one call, one iteration, or one `provide mut` block, so the ownership check tracks no mutable reference from one statement to the next. |
| A view is passed as its owning type to a read-only parameter whose declared type is a type parameter or an associated type. | Generic code cannot name the view of its type parameter, so `Map.get`, which takes `key: Key`, would make a lookup in a `Map[String, Int64]` allocate a `String`. A callee cannot mutate, move, drop, or store a read-only parameter, so it cannot tell a view from an owned value. Rust needs the `Borrow` trait and a blanket `impl` for this lookup. |
| A parameter declared as `List` or `String` takes no view. | Its signature can declare `Slice` or `StringSlice`, which takes both. If it took a view too, the two declarations would accept the same arguments, and every signature would choose between them for no reason. |

### Lending methods

Rules: [Lending methods](SPECIFICATION.md#lending-methods),
[Indexing](SPECIFICATION.md#indexing).

A method cannot return `mut` access to a part of `self`, because `mut`
access is never stored. `scores[i] += 1` needs that access. A lending method
provides it: `lends` in place of a result type lends one part of `self` to
the caller for the rest of the caller's statement.

```truss
fn Grid.cell(mut self, position: Position) lends mut Cell {
  mut self.cells[position.row * self.width + position.column]
}

mut grid.cell(position).visit()
```

Indexing is a lending method of the prelude trait `Index`, so a user's
`Grid` gets the syntax and the proof rules of a `List`.

**No code of a lending method runs after the lend.** Swift's `_read` and
`_modify` accessors also lend a part for one access, but they are
coroutines: the accessor suspends at the lend and resumes when the access
ends, so it can, for example, update a cached total. Truss gives up the
resumption for two reasons:

1. A reader of a call would have to follow code that runs after the
   caller's statement.
2. The ownership check and the prover would need rules for a statement that
   exits early while the accessor is suspended.

The cost falls on a type that must update other state when a part is
mutated. Such a type takes the new value in an ordinary method, as
`IndexAssign.assign` does for `bits[i] = true`.

| Rule | Reason |
|---|---|
| Reading an element and mutating it in place are separate traits, `Index` and `IndexMut`. | A collection that packs its elements, such as a `BitSet`, has no place to lend `mut`. It implements `Index` to read an element and `IndexAssign` to replace one. Rust's `Index` returns a reference, so such a collection cannot be indexed there. |
| A method may lend a value that it computes, and a mutation of that value is not written back. | Writing back would be code after the lend. |
| A method lends a part of its first parameter, or a whole value that it made, and never a part inside a value it owns. | Nothing of the method then has to outlive its call except the part, which the caller holds. So the method can be compiled as a function, be called through `any`, and call itself. Rust has the same rule for a reference into a local. Swift's accessors lend such a part by keeping the accessor's frame alive. |
| A lending call lends its whole receiver. | The method was proven on the assumption that nothing else uses `self` while the part is lent. |

### Loops

Rules: [Loops](SPECIFICATION.md#loops).

A `for` loop over a collection visits it by position. The loop evaluates
`count()` once, and each iteration is lent `element(position)`. A type
supports `for` by defining those two methods:

```truss
fn Grid.count(self) -> UInt64
fn Grid.element(self, position: UInt64) lends Cell
```

The alternative is a generator: a method that is suspended between
iterations. A generator keeps its locals alive across the loop's body, and
it needs rules for the code that runs when the loop exits early. That is
the coroutine that lending methods avoid.

In a loop by position, the collection's code runs only inside `count` and
`element`. The ownership check, the prover, and code generation therefore
treat the loop as a loop over a range of positions, and it compiles to a
plain loop. The prover takes the loop's facts from the contract of
`element`: each position is in bounds, each element is visited once, and the
loop terminates. Most loops therefore need no annotation, and a user's
collection gives its loops the same facts as a `List` by stating the same
contract.

The cost is that a loop by position visits one collection, and the
collection must have positions. Such a loop cannot advance two sequences
together, so it cannot express `zip`, a merge, or `peek`. A tree has no
positions. [Cursors](#cursors) cover both cases.

### Cursors

Rules: [Cursors](SPECIFICATION.md#cursors).

A cursor gives values one at a time through `next`. It is a value of a type
that the program declares, and its state is in its fields. Its size, its
allocations, and whether it is a view are therefore in its type, and it can
be stored, passed, and returned.

| Rule | Reason |
|---|---|
| A cursor never holds `mut` access. | `mut` access is never stored. A `mut` loop mutates elements in place, by position. |
| A tree is visited by recursion, by `fold`, or by a cursor that holds an explicit stack. | *Nothing hidden.* The stack's allocations are written. C# and Python allocate the same stack behind a recursive generator. |

### Lambdas

Rules: [Lambdas](SPECIFICATION.md#lambdas),
[Function types](SPECIFICATION.md#function-types).

A lambda captures local variables by view, and it cannot mutate them:

```truss
let passing = scores.filter(fn(score) { score >= threshold })
```

Read-only capture makes every lambda safe to call from parallel branches, so
any lambda can be passed as a comparator, to `map`, or as a `parallel`
callback. It also leaves one kind of function type, where Rust has `Fn`,
`FnMut`, and `FnOnce`. The cost is that a closure cannot accumulate state.
State that is updated from one call to the next goes in a `for` loop or a
method such as `fold`, and behavior with state is a record that implements
a trait.

A lambda's parameters have no annotations, so its body can prove a fact
about an argument only if the callee states one. The function type of a
parameter can therefore carry a `requires`:

```truss
fn List[Element].generate(
  count: UInt64,
  make: (fn(index: UInt64) -> Element requires index < count),
) -> List[Element]

let reversed = List.generate(values.length(), make: fn(index) { values[values.length() - 1 - index] })
```

The `requires` gives the lambda the fact `index < count`. From it, the
lambda proves that `values.length() - 1 - index` does not underflow and
indexes `values` in bounds. A `requires` is allowed only on the type of a
parameter, so no type that values are stored in or compared by carries one.

| Rule | Reason |
|---|---|
| Only a lambda that captures nothing can be stored. A function-typed parameter is non-escaping unless it is `own`. | A lambda that captures is a view, and a view cannot escape. |
| A lambda's parameter types and result type come from its expected function type, never from its body. | *Local reasoning.* Rust checks a closure's body before it knows the parameter types, and "type annotations needed" is one of its commonest errors. |
| A lambda's parameter modes come from the expected type too. | A mode keyword at a call site shows the mutation of an existing place. A lambda's parameter is a new binding, so a keyword there would show nothing. |
| `return` exits the lambda. | Kotlin's non-local `return` from an inline lambda is a known source of confusion. |
| A lambda has one form, `fn(x) { ... }`, passed inside the call's parentheses. | *One spelling.* A block's value is its last expression, so `x => x * 2` would be a second form, and a trailing lambda a second way to pass an argument. |
| A lambda names its parameters. | An implicit parameter such as `it` or `$0` is not a descriptive name ([Names](#names)). |

### Handles

Rules: [Handles](SPECIFICATION.md#handles).

A handle stands for a resource of the operating system, such as an open
file. A handle is released as memory is: when its owner's scope ends, on
every path. `?` and `return` therefore need no cleanup code.

Truss has no destructors: no type defines code that runs when its value is
released. None is needed. There is no foreign code, so only the standard
library's capability implementations create handles. Releasing a value
therefore runs no Truss code and cannot fail.

A buffered writer is a resource whose release could lose data. Closing a
file that was only read loses nothing, but flushing a buffer can fail, and a
release has no way to report the failure. Rust's `BufWriter` loses writes
this way when it is dropped. So a writer is only lent: `write_with` lends
the writer to a function, flushes it afterward, and returns the first error.
User code never owns a writer that it could drop unflushed.

## Constants

Rules: [Constants](SPECIFICATION.md#constants).

| Rule | Reason |
|---|---|
| A constant expression calls no function. | A constant can appear in a type, as in `Array[UInt8, digest_size]`, so type checking never waits for code to run. |
| Code that runs at compile time is compiled and run as a test is, not interpreted. | Truss then has one implementation of its semantics, and a result computed at compile time equals the result in the compiled program. Such code only discharges proofs and produces static data, so type checking never depends on it. |

## Functions

Rules: [Functions](SPECIFICATION.md#functions).

**Type inference stops at the statement.** A signature is written in full,
and inside a body a variable's type is decided by its own `let` or `var`.
Rust, OCaml, and Haskell infer across a whole body, so a variable's type can
come from a use many lines later, and an error can be reported far from its
cause. In Truss the type is readable on the variable's own line, by a
person, an LLM, and the language server, and type checking stays fast
(*local reasoning*). The cost is an annotation where the statement alone
cannot decide, as in `var names: List[String] = []`.

A local declared from literals alone is the exception: it takes its type
from its uses, whatever their order. Otherwise `let limit = 10` would fix
`limit` at `Int64`, and code that works in `UInt8` or `UInt64` would annotate
every such local.
Only the type of a literal is left undecided, and it can only become a
number type, so the declaration still tells the reader that the local is a
number.

### Calls and arguments

Rules: [Calls and arguments](SPECIFICATION.md#calls-and-arguments).

```truss
copy(original, destination: backup)
copy(source, destination)
let connection = connect(host, port: 8080)?
```

One set of rules covers calls, construction, and patterns: a record is
declared as parameters are, constructed as a function is called, and matched
in the same shape.

| Rule | Reason |
|---|---|
| An argument after the first is labeled. | Two arguments of one type can otherwise be swapped silently. A newtype prevents that only when the types differ. A label also tells `source: Path` from `destination: Path`. |
| The first argument may be bare. | The function's name usually identifies it, as in `sqrt(area)`. |
| A variable with the parameter's name needs no label. | A label costs nothing when the names agree, which is the common case, and is written exactly when they disagree, which is when a swap is possible. A bare name goes to the parameter it names, so `copy(destination, source)` is reported as out of order. |
| The same rules apply to every function. | Swift lets each parameter opt out of its label, so the syntax of a call depends on the choices of the callee's author. |
| A call through a function value is positional. | Labels in function types would make types that differ only in labels convert into each other. |
| Only a record with one field takes a bare value. | Field order has no meaning, so a bare first argument would make it part of the record's API. |
| Construction uses parentheses. | `{` then always starts a block in an expression. With braces, `if kind == Kind.Unit { x }` is ambiguous between a record and a block, which Rust and Go resolve with a special rule. |

A parameter can have a default:

| Rule | Reason |
|---|---|
| An argument for a parameter with a default can be omitted. | Adding a parameter is then an edit in one place. Without defaults every call site is edited, which in a codebase shared by agents is a large diff that conflicts with their work (*parallel agents*). Truss has no overloading by parameter type, so a default is also the alternative to near-duplicates such as Rust's `sort`, `sort_by`, and `sort_by_key`, and to option structs and builders. |
| A default is a constant expression. | It is the same at every call, has no effect, and costs one read of a constant. |
| The callee applies the default. | C# copies a default into each caller, and a caller keeps the old value after a library changes the default. |

### Explicit type arguments

Rules: [Explicit type arguments](SPECIFICATION.md#explicit-type-arguments).

Explicit type arguments use the brackets of indexing, as in
`parse[Int64](text)`. Rust needs `parse::<i64>` because `<` is also the
less-than operator. Brackets have no such conflict. The kind of the name
before the brackets decides between the two readings, and the rules of
[Scope](#scope) keep that kind easy to see.

### Termination

Rules: [Termination](SPECIFICATION.md#termination), [Loops](SPECIFICATION.md#loops),
[Recursive types](SPECIFICATION.md#recursive-types).

**Running forever is a capability.** A function may run forever only where
its `uses` names `RunForever`: a loop without a measure uses it, and so does
a call of a function that uses it. Every other rule is the capability check.
A function type without `RunForever` takes only functions that terminate, a
capability parameter holds `RunForever` where a function passed for it may
run forever, and a specification, which uses no capability, calls only
functions that terminate. Koka tracks divergence as the effect `div` in the
same way, and Truss writes it as it writes every capability. The
alternative is that a function without a `time` clause may run forever.
That default gives an omitted clause two meanings: a function type that
names a capability parameter has to leave termination to the parameter, and
the type of a function that uses the parameter's capabilities and runs
forever has no written form.

**The recursion check follows every edge of the call graph.** A function
reaches itself by a direct call, and by supplying code to a callee: by
naming a function as a value, by passing an `impl` where a bound needs one,
by converting a value to `any`, and by providing an `impl`, because the
code that receives the function or the `impl` can call back. If the check
ignored the supplied code, a package could implement a trait with a method
that calls a generic function that calls the method back, and each
termination proof would assume the other. Every such cycle is visible within
one package, because Truss has no mutable state outside variables and
because of the next rule.

**A type cannot hold a terminating function that takes the type.** With
`type Knot(run: fn(Knot) -> Bool)`, a function that calls `knot.run(knot)`
calls itself, and no name in its code says so. Coq and Lean forbid this for
every function type, as strict positivity. Truss forbids it only for a
function type without `RunForever`, so
`type Button(on_click: (fn(Button) uses RunForever))` is legal.

**An associated capability set passes on whether an `impl`'s method runs
forever.** `Cursor.next` uses `Self.Uses`. A cursor over lines read from a
socket puts `RunForever` in its `Uses`, and a list's cursor does not, so
`skip` over a list's cursor terminates and `skip` over the socket's may
not.

| Rule | Reason |
|---|---|
| Structural recursion needs no annotation, and other recursion states `decreases`. | Lean accepts structural recursion in the same way. Dafny infers a measure. A structural check with an explicit clause is more predictable than an inference that may fail. |
| Code that supplies other code to a callee answers for the calls made to the supplied code. The suppliers are a type argument's `impl` given to a bound, a function named as a value, a value converted to `any`, and a provided `impl`. A recursion through supplied code is rejected. | A generic callee is checked once, for every type argument, so it cannot know the code that it is given, and a call through a bound passes the supplier no arguments to compare with a measure. If neither side answered, an `impl`'s method could call a generic function that calls the method back, and each termination proof would assume the other: a function without `RunForever` would never return. |
| A recursion through a method that an `impl` derives or inherits is rejected. | A derived method is generated, and an inherited method is the trait's provided body, which is checked once for every `impl`. Neither states a measure for the `impl`, so a caller on the cycle has nothing to compare, and accepting the call would assume that the cycle ends. A method written in the `impl` states the measure. The alternative is to check each provided body again for each `impl` that inherits it, which proves the same code once per `impl` and gives a trait's author errors in code that the author did not write. |
| A `while` loop whose condition compares two sides with `<`, `<=`, `>`, or `>=` has the distance between them as its default measure, and a `for` loop over a cursor has the cursor's `remaining()`. | Most loops count toward a bound that their condition names, so `decreases high - low` would only repeat the condition. The default is one measure read from the loop's own code, never chosen by a search among candidates, so a reader knows the measure that the proof uses. Dafny takes the same default for a loop. A cursor's `remaining()` states its measure once, in its type, for every loop over it. |
| A written measure holds in every function, including one that uses `RunForever`. | A reader takes a written `decreases` as a fact. If `RunForever` switched measures off, a function that declares it for one loop would leave the measures of its other loops unchecked. A cursor's `remaining()` is written too, in the cursor's type, and no loop body can change the cursor. |
| A `while` loop's default measure and structural recursion are checked only in a function without `RunForever`. | Both are inferred from code that may not be meant to end. A loop that draws samples until it has accepted enough, as `sample_ntt` does, compares toward a bound that an iteration may not approach. |
| A loop without a measure uses `RunForever`. | The capability check then covers the loop in every body, as it covers a call. A lambda's loop needs no rule of its own: the lambda's capabilities are inferred from its body. |
| Nothing implements `RunForever`. | A `provide` of it would let a function that does not declare `RunForever` run forever. |
| A function that uses `RunForever` has no `time` clause. | A written clause holds, and the time of a function that may run forever has no bound. |
| A manifest grants `RunForever` to a dependency as it grants any other capability. | A dependency that is granted nothing then terminates, as well as reaching nothing outside its arguments. |
| A capability method that waits for the world terminates unless it declares `RunForever`. | A capability method returns to its caller once the world answers. If waiting counted as running forever, nearly every function that reads input would declare `RunForever`, and the capability would no longer separate a loop that has no measure from one that has. |

### Cost clauses

Rules: [Cost clauses](SPECIFICATION.md#cost-clauses).

```truss
public fn load_configs(paths: List[Path]) -> Result[List[Config], ConfigError]
  uses FileRead
  cost calls(FileRead.read) == paths.length()
  cost time O(paths.length())
```

A caller's cost is proven from the cost clauses of its callees, so an edit
to one function invalidates only the bounds of its dependents (*O(change)*).

**Amortized bounds are proven with potentials,** following Automatic
Amortized Resource Analysis (AARA). AARA is sound only for values that are
never shared: two references to one structure could each spend its
potential. Mutable value semantics guarantees that no value is shared, so
amortized bounds compose. A value's potential includes the potential of its
parts, so a push onto a list inside a list is paid for by the inner list.

**There are no expected-time bounds.** A hash map is O(1) only on average,
on the assumption that hashes behave randomly. No proof can promise that
against input chosen by an attacker, and proving expected bounds needs
logics that are still research. [Maps and sets](#maps-and-sets) bound the
worst case instead.

| Rule | Reason |
|---|---|
| A countable resource takes an exact bound, and time takes only `O(...)`. | An exact bound can state that each item is processed exactly once. A concrete time cannot be proven across machines. |
| `O(f)` bounds the cost for every input, not only for large inputs. | The textbook definition is a limit, which a prover handles poorly, and it gives wrong answers for bounds in several variables. |
| A bound can mention `result`. | An output-sensitive bound, such as the bound of a function that returns its matches, cannot be stated otherwise. |
| The `time` of a generic function counts the methods of its bounds. | `O(self.length())` would be false for `contains` on a list of strings, where one comparison is not one step. `String` could not keep a promise of `O(1)` on `Equal.equal`, and a second trait for constant-time comparison would give every generic method two overloads. |
| A function that calls a callback bounds its allocations with `allocations(visit)`, and its allocated bytes with `allocated_bytes(visit)`. | `Option.map` allocates what its callback allocates. Without the term it states no allocation bound, and a function with `cost allocations <= 0` then calls no combinator, even with a lambda that allocates nothing. The alternative is an allocation clause on the type of every callback, which rejects each function that states none. |

### Function types

Rules: [Function types](SPECIFICATION.md#function-types).

A function type puts its clauses after its result, inside parentheses, as in
`(fn(Request) -> Response uses Database, Log cost time O(1))`. Truss has
whole clauses, not one or two effect keywords, so the clauses come in the
order they have in a definition, and the parentheses mark where they end.

| Rule | Reason |
|---|---|
| A call of a function value passes the caller's capabilities as one table, and the function finds each capability it uses in the table by name. | A value of `fn()` can be passed where `(fn() uses Clock)` is allowed, and stored or returned there, with no wrapper and no change to how it is called. A wrapper would need storage that lives as long as the value, which a function value that captures nothing does not have. |

## Methods

Rules: [Methods](SPECIFICATION.md#methods).

| Rule | Reason |
|---|---|
| A method is defined in the package of its type. | A method is easy to find, and two packages can never add conflicting methods to one type. |
| Every call uses parentheses. | *Nothing hidden.* A reviewer can tell that `names.length()` runs code and that `point.x` reads a field. |

### Overloads by receiver mode

Rules: [Overloads by receiver mode](SPECIFICATION.md#overloads-by-receiver-mode),
[Method lookup](SPECIFICATION.md#method-lookup).

A method can be overloaded on the mode of `self`, and on nothing else. One
`enumerate` serves read-only, `mut`, and `own` loops, where Rust needs
`iter`, `iter_mut`, and `into_iter`.

**An overload set has one author.** The overloads of a name come only from
the type's own methods, from the methods of its view, from the methods that
an `impl` in the type's package writes, and from a trait together with the
traits it requires. A type and its view are defined in one package. If
overloads were collected from every visible `impl`, a package added to a
build could capture an existing call.

**There is no overloading by parameter type.** It would cost three things:

1. Type checking would stop being local and fast. Swift's "expression too
   complex to type-check" errors come from overloads combined with literals
   that take their type from context, and Truss has such literals.
2. An overload added anywhere could change an existing call.
3. A reader could not tell which `process` runs in `process(item)`.

A trait with type parameters covers most uses of overloading:
`BigInteger.from(count)` selects an `impl` of `From[Source]` by the type of
`count`. It avoids all three costs, because the argument types are inferred
first, nothing is selected by the expected result type, and the candidate
`impl`s live in known packages ([Implementations](#implementations)).

## Statements and blocks

Rules: [Statements and blocks](SPECIFICATION.md#statements-and-blocks).

**Every value is used.** A statement whose value is not `Unit` is an error.
This one rule catches three mistakes:

| Mistake | Example |
|---|---|
| A dropped error | The `Result` of a write is ignored. |
| A call with no effect | `names.sorted()` is written where `mut names.sort()` was meant: the call is pure, and its result is discarded. |
| A misread line break | A line that starts with `-` begins a new statement, which leaves an unused value. |

Rust and Swift warn only for marked types or functions, so they catch only
those. A rule for every value needs no warnings and no attributes. It pushes
an API toward returning `Unit` when the result is usually not needed.

| Rule | Reason |
|---|---|
| Every variable is used, and every `match` arm is reachable. | Such code is almost always a mistake, often a typo. The two rules also catch a constant that is written as a bare name in a pattern ([Patterns](#patterns)). A parameter is exempt, because an implementation of a trait may not need every parameter. |
| Unreachable code is an error. | It is almost always a line left behind by an edit. The check uses types alone, so it never reasons about values. Code after a `todo` is unfinished, not unreachable. |
| A comparison of a place with itself is an error outside specifications. | `x != x` tests for NaN in C, Java, and JavaScript, and is always false in Truss, where every NaN equals every NaN (*LLM habits*). Any other comparison of a place with itself is a typo, since the laws of `Equal` and `Ordered` decide its result. A law states such a comparison on purpose. |

### Patterns

Rules: [Patterns](SPECIFICATION.md#patterns).

**A bare name in a pattern binds, and a constant is written with its module
or its type,** as in Python's `match`. In Rust a bare name is a constant if
one is in scope and a binding otherwise. Adding a constant to one file of a
module then silently changes the semantics of a pattern in another file, and
every binding in a pattern depends on the names of the module. In Truss, a
constant written as the bare name `limit` still compiles, as in Python, but
the binding matches every value. It therefore makes a later arm unreachable
or is itself unused, and both are errors.

| Rule | Reason |
|---|---|
| A constant in a pattern has a type with structural equality. | The checks that a `match` covers every case and that every arm is reachable compare constants by their contents. Under float equality or a hand-written `Equal`, two constants with different contents can be equal, so an arm that never runs, such as one for a constant `-0.0` after one for a constant `0.0`, would pass as reachable. |
| A variant is written under its type in an expression, and bare in a pattern. | The name shows its type, and two types can share a variant name. In a pattern the variant is resolved in the type of the scrutinee, as a method is resolved in the type of its receiver. |
| A float literal is not a pattern. | `-0.0 == 0.0`, so a pattern `0.0` would silently match both. A guard states which is meant. |

### `match`

Rules: [`match`](SPECIFICATION.md#match).

| Rule | Reason |
|---|---|
| `match state, event` matches several values with no tuple. | State machines are the main use of a match on a tuple. Patterns correspond to values by position only within one `match`, where the scrutinees and the arms are in view together. |
| Arms are separated by line breaks, as statements are. | *One spelling.* Rust makes the comma optional after a block arm. The cost is that a `match` does not fit on one line. `is` covers most one-line uses. |

### `is` and `let ... else`

Rules: [`is`](SPECIFICATION.md#is), [`let ... else`](SPECIFICATION.md#let--else).

`value is pattern` is a `Bool` expression. One construct covers conditions,
loops, specifications, and conjunctions with other conditions, where Rust
has three: `if let`, `while let`, and let-chains.

A name that `is` binds is in scope only where the test is known to be true,
so it is never in scope after the `if` that bound it, and scope follows
blocks. `let ... else` is the form for a binding that outlives the test: its
names are in scope for the rest of the enclosing block, and its `else` block
must exit.

### Errors

Rules: [Errors](SPECIFICATION.md#errors).

A recoverable error is a value of type `Result`, and `?` returns it from the
enclosing function. `Panic` is for bugs ([Failure](#failure)).

**`?` never converts the error.** In Rust, `?` calls a `From` implementation
that is selected by type. The call is hidden, it can allocate, and it is a
known source of inference failures. In Truss every conversion is a written
call with a proven cost (*nothing hidden*):

```truss
let text = FileRead.read_text(file).map_error(ConfigError.Unreadable)?
```

The conversion stays short, because a variant with one field can be used as
a function. Each error also gets a name in the terms of its own function,
such as `Unreadable` or `Malformed`.

### Ranges and collection literals

Rules: [Ranges](SPECIFICATION.md#ranges),
[Collection literals](SPECIFICATION.md#collection-literals),
[Indexing](SPECIFICATION.md#indexing).

| Rule | Reason |
|---|---|
| A range with no start or no end appears only in brackets. | `0..` anywhere else would allow a `for` loop with no end. |
| Each collection has one literal form, `[a, b, c]` or `[key: value]`, which takes its type from its context. | *One spelling:* a collection that takes a literal has no `new()` and no `of(...)`. A map uses brackets because `{` starts a block. |
| A type takes a literal by implementing `FromElements` or `FromEntries`. | Indexing, `for`, the operators, and tagged templates each belong to a prelude trait, so a package's collection is written as a standard one is. A literal for the compiler's types alone leaves every other collection to name a constructor of its own. |
| Distinct keys are the `requires` of `from_entries`. | A duplicate key is a failed proof for every map type. Letting the last key win would hide a mistake. A repeated element of a set drops nothing, so `from_elements` requires nothing. |
| A string cannot be indexed. | In UTF-8, byte `i` and character `i` differ, so code says which one it means. |

## Expressions

Rules: [Expressions](SPECIFICATION.md#expressions).

### Operators

Rules: [Operators](SPECIFICATION.md#operators).

**Precedence is a partial order.** Two operators have a relative precedence
only where languages agree on one, such as `*` over `+`. Every other
combination needs parentheses. An LLM trained on languages that disagree
cannot be trusted to remember one table (*LLM habits*).

| Rejected without parentheses | Disagreement |
|---|---|
| A bitwise operator or a shift beside any other operator | C puts `&` below `==`, so `flags & mask == 0` tests `mask == 0`. C, Rust, Go, and Swift order the bitwise operators differently from one another. |
| `&&` beside `\|\|` | The same risk: an author or a reader who misremembers the order gets a different condition. |
| `!` as the left operand of `is` | `not x is y` negates the test in Python, and `!x is T` negates the value in C# and Swift. |
| A chain of comparisons | `a < b < c` is a chained comparison in Python and a comparison with a `Bool` in C. |

| Rule | Reason |
|---|---|
| A range binds more loosely than arithmetic. | `0..count - 1` means `0..(count - 1)`. |
| `+=` exists, and `++` and `--` do not. | `a += b` evaluates the place `a` once, so a long place expression is not mistyped the second time, and an index is proven in bounds once. As expressions, `++` and `--` are confusing and rarely clearer than `+= 1`. |
| A compound assignment passes the old value to the operator as owned. | `matrix += other` can update in place, with no separate trait such as Rust's `AddAssign`. |

**An arithmetic operator calls a trait with a type parameter for its right
operand,** because times, geometry, and money need mixed types, as in
`instant + duration`. A comparison takes one type on both sides, because the
laws of `Equal` and `Ordered` relate a type to itself.

**An operator trait states the domain of its operation.** If `add` promised
a result for every pair of values, the `impl` for a fixed-width integer
would have to wrap or panic, and generic code could overflow with nothing in
its signature to show it. So `add` requires `add_is_defined`, and generic
code carries the same proof obligation that an operator on a built-in type
carries.

### Integers

Rules: [Integers](SPECIFICATION.md#integers).

Code for every integer width is written once, against the integer traits, as
Swift's extensions of `FixedWidthInteger` are. The traits are sealed, so
generic code over one is proven once for each built-in type, with that
type's range and bit width. For the same reason, a literal under such a
bound must fit every type that implements the trait.

**A conversion between built-in scalars is a method of the target type,
not an `impl` of `From` or `TryFrom`.** `Int64.from_integer(count)` requires
that `count` fits, and `Int64.try_from_integer(count)` returns a `Result`.
Each is one method of `FixedWidthInteger`, generic over the source and proven
for every pair of integer types, with one contract. Impls would need one per
pair. `From` and `TryFrom` are for conversions that involve a library type,
as in `BigInteger.from(count)`.

### Floats

Rules: [Floats](SPECIFICATION.md#floats).

**Float equality is lawful.** IEEE 754's `NaN != NaN` breaks reflexivity,
and Truss proves the laws of `Equal`. So every NaN equals every NaN, and NaN
is ordered after every number.

| Option | Consequence |
|---|---|
| IEEE 754 comparison as `==` | Floats cannot be sorted, used as map keys, or compared by a derived `Equal`. This is Rust's limitation. |
| No `Equal` for floats | A `Point` of floats cannot derive `Equal`. |
| Lawful `==`, with `ieee_` comparisons beside it | A lawful comparison costs a few instructions more, which can matter in a hot loop. The `ieee_` comparisons are the exact, single-instruction alternative. |

**Float results are the same on every platform** (*determinism*). Functions
such as `sin` and `exp`, and the conversions between floats and text, are
implemented in the standard library, as Java's `StrictMath` is. The
platform's C library gives results that differ between systems. A cached
test result therefore holds on every machine, and a value computed at
compile time equals the value in the compiled program.

## Failure

Rules: [Failure](SPECIFICATION.md#failure).

Code panics only where it has `Panic`. The exceptions are running out of
memory and overflowing the stack, which no language rules out.

Every operation that can fail is a proof obligation: an integer overflow, a
division by zero, an index out of bounds, a shift that is too large, and
`unreachable`. Code meets an obligation in one of three ways. It establishes
the fact locally, requires the fact of its caller, or calls a checked variant
that returns an `Option` or a `Result`.

**`Panic` permits a crash and changes nothing else.** `uses Panic` lets code
call `Panic.crash`, directly or through a callee such as `expect`, as
`uses Clock` lets it call `Clock`. The body's operations are proven as
anywhere else. Code that crashes on a failure writes the crash where it
happens: `total.checked_add(price).expect("the total fits Int64")`
(*nothing hidden*). If declaring `Panic` turned unproven operations into
run-time checks, the declaration would stand in for every proof in the body,
and a crash would hide at each operator.

**A panic cannot be caught.** Code that caught a panic could hold a value
whose invariant was broken partway through an update. A program that must
keep running proves that it cannot panic instead: a server requires a
handler type without `Panic`, so no request can end the process. If the
process fails anyway, a supervisor restarts it.

`unreachable` must be proven. Code that claims a point is unreachable must
not panic when the point is reached. Code that panics on purpose calls
`Panic.crash`, which its signature shows.

## Capabilities

Rules: [Capabilities](SPECIFICATION.md#capabilities).

A capability is a named set of methods for acting outside pure computation.
A function lists the capabilities it `uses`, and its caller provides the
implementations:

```truss
capability Random {
  fn next() -> UInt64
}

fn roll_die() -> UInt64
  uses Random
{
  Random.next() % 6 + 1
}

type LoadedDie(face: UInt64)

impl Random for LoadedDie {
  fn next(self) -> UInt64 { self.face }
}

let rolled = provide LoadedDie(face: 5) {
  roll_die()
}
```

A function without `uses` is pure. Two goals rest on that rule:

- **Deterministic tests.** A test provides fakes of files, clocks, and
  networks, so its result is the same on every run and is cached
  ([Tests](#tests)).
- **A confined supply chain.** A dependency has only the effects that its
  signatures allow, which limits the damage that a compromised package can
  do ([Grants](#grants)).

**A capability method returns to its caller once, unless its result type
is `Never`.** A capability call therefore compiles as a function call, Truss
needs no stack unwinding, and no computation is abandoned with a value half
updated. `Panic.crash` returns `Never` and ends the program, so no code
observes the values it abandons. An early exit goes through `Result` and
`?`, where each step is written. For the same reason there is no `exit`.

**A view never crosses into or out of an implementation.** A caller cannot
see which implementation its call reaches, so it cannot know whether a view
that it passed is still held. A view of an implementation's storage would
dangle when a later call replaced that storage.

**Narrowing is ordinary code.** An implementation of a capability can check
each call and pass it to the next provider out. The code that makes the call
cannot tell that the capability was narrowed. A signature and a narrowing do
different jobs: a signature limits which capabilities code has, and a
narrowing limits the reach of one capability.

| Rule | Reason |
|---|---|
| A callback uses capabilities only through a capability parameter. | One rule stays true: no `uses` means pure. A callback is pure by default, which is the safe default for a comparator and for code that runs in parallel. |
| Providing a type provides every capability that the type implements. | A type that narrows both reading and writing cannot leave one of them unnarrowed by mistake. |
| An `impl` of a capability can declare `uses`, and a `provide` of it requires those capabilities. | Capabilities layer instead of inheriting. `ReadDatabase` is implemented with `NetworkClient`, which is required where the implementation is provided. A dependency that is granted `ReadDatabase` alone never reaches the network. |

### Standard capabilities

Rules: [Standard capabilities](SPECIFICATION.md#standard-capabilities).

The standard capabilities are fine-grained where trust differs: a config
loader that has only `FileRead` cannot delete anything.

**Opening a handle and using one are separate capabilities,** for three
reasons:

1. If the methods of a handle required the capability that opened it,
   reading a connection would need `NetworkClient` or `NetworkServer`, and a
   request handler would hold the power to open connections of its own.
2. One capability for every handle, `Handles`, lets files, connections, and
   pipes implement the same `Reader` and `Writer` traits.
3. A handle is a token, and the provider of `Handles` decides the result of
   a read, so a test can simulate a file or a network.

### `main`

Rules: [`main`](SPECIFICATION.md#main).

`main` gets exactly the capabilities that it declares, so its signature
states every effect of the program. Its arguments are a parameter, so a test
can call `main` with fake arguments and fake implementations.

### Grants

Rules: [Grants](PACKAGES.md#grants).

A signature does not limit a dependency whose caller already holds the
capability. If a package uses `NetworkClient` and calls `json::parse`, a new
release of `json` could start using the network, and the package would still
compile, because it has the capability to pass along. So a manifest grants
each dependency its capabilities.

| Rule | Reason |
|---|---|
| Every dependency has a grant, the project's own packages included. | Much of a project's code is written by LLMs, and not all of it is reviewed, so the limit matters for the project's own code as it does for a stranger's. |
| No tool adds a grant. | Giving a package more capabilities is always a line in a manifest that a reviewer sees. |
| A grant is checked wherever a dependency's code is named, not only at calls. | Otherwise a package with no grant could have its `impl` run by a package that has one. The dependency's bodies are already checked against its signatures, so its code has no effect beyond them. |
| A package needs a grant even for a capability that it defines. | The provider of the capability decides its behavior. |
| The lock file records the capabilities that each package holds. | An upgrade deep in the dependency graph that gives a package the network shows as a changed line. |
| Nothing in a package runs when it is fetched or built. | An install script, a build script, or a procedural macro runs a dependency's code with everything the developer can reach. That is how a package that steals a publishing token goes on to publish itself under its victim's name. The code that runs at compile time is pure, and a dependency's external tests are never run by its users. |

Grants need no rule for transitive dependencies. The `uses` of a function
includes every capability that its callees use, so a package cannot pass its
own dependencies more than it holds. A new release cannot give a function
that is already called more capabilities unnoticed: each caller's `uses` must
name them, so the upgrade fails to compile until the caller's author adds
them.

Grants cannot stop a wrong answer: a pure dependency can still return a
result that its user acts on. Contracts narrow that risk, and a project's
dependencies still need review.

## Parallelism

Rules: [Parallelism](SPECIFICATION.md#parallelism).

Parallelism uses several cores to finish a computation sooner. In Truss it
is deterministic: a `parallel` block has the result of running its branches
in order.

```truss
let halves = players.split_at(players.length() / 2)
parallel {
  let left = sum_scores(halves.first)
  let right = sum_scores(halves.second)
}
left.saturating_add(right)
```

| Rule | Reason |
|---|---|
| A place that one branch mutates is used by no other branch. | This is the rule for calls, where a place passed `mut` is used by nothing else during the call: `swap(mut first, second: mut first)` is rejected. Applied across branches, it prevents every data race. |
| A branch uses no capability except `Panic` and `RunForever`, and uses each only where the enclosing function has it. | Two branches that called one stateful implementation would race, and the order of their calls would vary from run to run. No code can `provide` `Panic` or `RunForever`, so no branch calls a stateful implementation of either. A branch that panicked in a function without `Panic` would end a program that relies on the function's signature, such as a server whose handler type has no `Panic` ([Failure](#failure)). A function that contains `parallel` is therefore still pure, and a test that runs it is cached. Code whose branches use capabilities is [concurrent](#concurrency). |
| The input decides where a computation is split, never the number of cores. | The result does not depend on the machine: a parallel float sum gives the same bits everywhere (*determinism*). |
| A branch cannot exit the block early. | A branch uses no capability except `Panic`, so it cannot be asked to stop. An early exit would have to abandon the other branches, or wait for work whose result is discarded. |

## Concurrency

Rules: [Concurrency](SPECIFICATION.md#concurrency).

Concurrency is doing several things whose order is not fixed, such as
serving connections, or waiting for a reply and a timer at once. The
behavior of such code can depend on the order of events, so concurrency is
an effect: code that does it declares `uses Tasks`.

```truss
fn profile(id: UserId) -> Result[Profile, DatabaseError]
  uses Tasks, Database
{
  concurrent {
    let user = Database.user(id)?
    let orders = Database.orders(id)?
  }
  Ok(Profile(user: own user, orders: own orders))
}
```

A `concurrent` branch differs from a `parallel` branch in one way: it may
use the capabilities of the code around it. The rule about places that
prevents data races in `parallel` therefore prevents them here.

**A task never outlives the block that started it.** This is structured
concurrency, as in Trio's nurseries. A branch can therefore read the places
around it, with no lifetimes.

**A call blocks, and there is no `async`.** Code waits by calling a
capability method that returns when the result is ready. `uses` already
separates code that can wait from code that cannot. A second marker for the
same fact, such as `async`, would split functions into two kinds that cannot
easily call each other.

Blocking calls also leave the scheduler free. Every call that waits is in
the standard library's capability implementations, because there is no
foreign code. The runtime can therefore give each task a thread, or switch
many tasks on a few threads, with no change to any code. Go and Java cannot
switch away from a task that waits inside foreign code.

**Cancellation is an error value.** In a cancelled task, a call that would
wait returns a value that says it did not finish, and `?` propagates that
value. A cancelled task therefore ends by returning, along a path that is
written in its code. An exception raised at the call, or a computation
dropped at the `await` it had reached, would abandon the computation
partway, which Truss never does. A timeout and a race need no feature of
their own: each is two branches, and the first to return cancels the other.

### Shared state

Rules: [Shared state](SPECIFICATION.md#shared-state).

**State that tasks share lives in a capability implementation,** because two
tasks cannot share a variable that either mutates. `uses Sessions` then
marks every function that can reach a shared table of sessions.

**A `mut` implementation is a monitor.** Within one call, nothing else
mutates the state. Between two calls, anything may. The prover never models
the state of an implementation, so no proof assumes that the state is
unchanged between calls.

**These monitors cannot deadlock.** The methods of an implementation call
only capabilities that are provided outside it, so every task acquires locks
in one order, from the innermost implementation outward. A callback that
uses a capability could acquire a lock out of that order, so a method of
such an implementation takes no callback that uses a capability. `Panic`
and `RunForever` are exempt: no `provide` implements either, so a callback
that uses only them acquires no lock.

**A mutex is not a value.** Locking a mutex mutates a read-only place, which
mutable value semantics rules out, and two tasks that lock two mutexes in
opposite orders deadlock.

A data race cannot occur, but a task can still wait forever, for a message
that no task will send.

**A test of concurrent code is deterministic.** A test's `Tasks` runs one
task at a time, chosen by a seed, and switches tasks only at capability
calls. Tasks share no mutable memory, so the interleavings of those calls
are the only interleavings. A race is then a failure that one seed
reproduces, not a flaky test. A test's clock advances when every task waits,
so a test of a timeout takes no real time.

## Strings

Rules: [Strings](SPECIFICATION.md#strings).

| Rule | Reason |
|---|---|
| Strings have no concatenation operator. | `+` stays numeric, and each allocation is written as an interpolation or a call (*nothing hidden*). |
| Adjacent literals do not join. | A missing comma in `["a" "b", "c"]` would silently merge two elements. |

### Tagged templates

Rules: [Tagged templates](SPECIFICATION.md#tagged-templates).

```truss
let query = SqlQuery"select name from users where id = ${user_id}"
```

A tagged template keeps its literal text separate from its interpolated
values, which makes an injection attack impossible by construction:

1. Only the compiler creates literal text, so text produced at run time
   never passes as trusted query text.
2. Each interpolated value is converted to the `Part` type of the tag, so a
   value with no meaning in SQL is a type error.
3. An API takes the type of the template, not `String`, and `SqlQuery` is
   opaque, so other packages cannot construct one.
4. An unsafe case is explicit, such as `SqlQuery.from_trusted_text`, which
   is easy to find in review.

| Rule | Reason |
|---|---|
| The tag is a type. | The tag names the type of the result, and a plain string is the case where the tag is `String`. |
| Malformed literal text is a compile error. | A tag states the rules for its literal text as the `requires` of `from_template`. A function in a specification is pure and terminates, so the compiler can run the check at compile time, and constructing the value cannot fail. The feature reuses `requires`, purity, and termination. |
| `from_template` is the one method whose `requires` may be stronger than its trait's. | A tag exists to constrain the literal text of a template, and a template always names its tag. |
| A check cannot read anything outside the code, such as a live database schema. | A build has no capabilities. |
| A character and a byte are tagged templates: `Character"é"` and `UInt8"\n"`. | They need no lexer rule of their own and no second set of escapes. |

## Traits and laws

Rules: [Traits and laws](SPECIFICATION.md#traits-and-laws).

```truss
trait Ordered: Equal {
  fn compare(self, other: Self) -> Ordering

  fn max(own self, other: own Self) -> Self {
    if self.compare(other) == Ordering.Less { other } else { self }
  }

  law transitive(first: Self, second: Self, third: Self)
    requires first <= second
    requires second <= third
  {
    first <= third
  }
}
```

**A provided method states its result in the trait's `ensures`, and an
override keeps it.** `Equal.not_equal` ensures `result == !self.equal(other)`,
so `a != b` always means `!(a == b)`, the prover reasons from the trait
alone, and generic code knows the result through a bound. A type can still
override a provided method with a faster one. This covers most uses of
specialization, with no overlapping `impl`s.

**An `impl` can promise more than its trait:** a weaker precondition and a
stronger postcondition, which is behavioral subtyping. `Index` can then say
nothing about the lent part, while the `impl` for `List` says which element
it is.

| Rule | Reason |
|---|---|
| A trait can require other traits. | A law can then span traits. `Ordered` requires `Equal`, so its law `agrees_with_equal` states that `compare` returns `Ordering.Equal` exactly when `==` holds. Rust's `Ord` requires `Eq` too, but that agreement is only documentation. |
| `Hash` has no law relating it to `Equal`. | A law is a specification, and a specification cannot call `hash`, which mutates its `Hasher`. Stating the law would take a `hash` that returns its hash, which gives up a keyed hasher provided through a capability, or a specification form for the state a mutating call leaves. A derived `Hash` agrees with a derived `Equal` by construction. |
| A type has one `impl` of each trait. | Two traits that both require `Equal` share that `impl`, so there is no diamond problem. |
| An `impl`'s method has its trait's signature, which the `impl` restates. | The body of the method and every call of it are checked against the same types. A method with a signature of its own would have a body checked against types that no call is checked against. |

### Implementations

Rules: [Implementations](SPECIFICATION.md#implementations).

| Rule | Reason |
|---|---|
| Every `impl` is written out for its type, and no two overlap. | A blanket `impl`, which covers every type that meets a bound, makes it hard to tell which implementation applies. |
| An `impl` lives in the package of its trait, of its type, or of a type that the trait's arguments name. | This is Rust's orphan rule, simplified. Packages cannot depend on each other in a cycle, so only one package can name the trait and all the types, and an `impl` has one possible home. |

### Associated types

Rules: [Associated types](SPECIFICATION.md#associated-types).

An associated type is chosen by each `impl`, and a type parameter selects
the `impl`. Truss needs both: associated types for `Index` and the
collections, and type parameters for `From` and the operators.

### Associated capability sets

Rules: [Associated capability sets](SPECIFICATION.md#associated-capability-sets).

A trait can leave a set of capabilities to each `impl`. Otherwise
`Cursor.next` would use no capability in every `impl`, and a cursor that
reads a file could not be passed to `zip` or `to_list`. Swift's
`AsyncIteratorProtocol` leaves its error type to each implementation in the
same way. `any` fixes the set to the empty set, because code that holds the
value cannot name the capabilities of the type that `any` hides.

### Equality

Rules: [Equality](SPECIFICATION.md#equality).

**Only equality that is identity lets the prover substitute.** From `a == b`
the prover concludes `f(a) == f(b)` only when equal values are `identical`,
so that no function can distinguish them. Four kinds of equality are not
identity:

| Equality | Reason |
|---|---|
| A hand-written `Equal` | It promises only an equivalence relation. |
| Float equality | `Point(x: 0.0, y: 0.0) == Point(x: -0.0, y: 0.0)`, and `1.0 / x` distinguishes the two. |
| `String`'s equality | Two equal strings can differ in `capacity()`. |
| The equality of an opaque type, outside its package | It would depend on fields that other packages cannot see. |

A constant in a pattern needs only structural equality, which compares
contents and which `String` has ([Patterns](#patterns)). Whether a type's
equality is structural, and whether it is identity, is derived from its
fields, as `Plain` is.

### Deriving

Rules: [Deriving](SPECIFICATION.md#deriving).

| Rule | Reason |
|---|---|
| Deriving is opt-in. | An `Equal` on a public type is a promise to its users, and structural equality is wrong for some types, such as a set stored as an unsorted list. |
| A derived `Ordered` or `Hash` needs a derived `Equal`. | The laws of `Ordered` relate it to `Equal`, and a map finds a key only when its hash agrees with `Equal`. Two derived implementations agree by construction. A hand-written `Equal`, such as that of a set stored as a list, would not agree with a field-by-field `Ordered` or `Hash`. |
| One derived `Serialize` serves every format. | Its methods are generic over a `Serializer`. A type that needs other field names writes the `impl`, because Truss has no attributes. |
| Every type has debug output, with no derive. | The test runner can show any value. Text for people goes through `Display`, which is written by hand, because a structural dump is rarely fit for a user. |

### Method lookup

Rules: [Method lookup](SPECIFICATION.md#method-lookup).

| Rule | Reason |
|---|---|
| A trait method needs no import. | A forgotten import is a common error in the languages that need one. |
| A method call finds only the traits of the standard library, of the calling package, and of the packages that its manifest lists. | An edit deep in the dependency graph cannot break a distant call. |
| A call skips a method that its module cannot see before it chooses an overload, and reports a hidden method only when it finds nothing it can see. | A private or `internal` method is a detail of its module or package, so adding, renaming, or removing one changes no call outside it. Every other name is looked up the same way. The cost is that one call can reach different methods in different modules: if `String` had a private `trim`, `name.trim()` would call it in its module and `StringSlice.trim` elsewhere. Both are written in one package. |
| Two candidates for one name are an error, never a silent choice. | In Rust a type's own method wins over a trait's, so adding a method can silently change an existing call. In Truss an upgrade can break a call only with an error that names both candidates. A release that only adds names is still compatible, because otherwise no type could ever gain a method. |
| A `String` has the methods of `StringSlice`, and a `List` and an `Array` those of `Slice`. | `self` is a parameter, and an argument of the owned type converts to its view. Without the rule, every method of a view needs a forwarding method on the owned type, whose contract is stated and proven a second time, and a view's method that has none cannot be called on the owned value. Rust reaches the methods of `str` from a `String` through `Deref`. |
| A type's own method hides its view's method of the same name and mode. | The owned type can do better where it owns the storage: `String.to_bytes(own self)` hands over its buffer, and `StringSlice.to_bytes(self)` copies. Both are written in one package, so no other package can change which one a call reaches. |

### Dynamic dispatch

Rules: [Dynamic dispatch](SPECIFICATION.md#dynamic-dispatch).

| Need | Use |
|---|---|
| One type, known at the call site | A generic parameter with a bound, dispatched statically |
| A closed set of alternatives | A sum type |
| An open set, mixed in one collection | `any Trait` |

| Rule | Reason |
|---|---|
| `any value` is written, and it allocates once. | *Nothing hidden.* An implicit conversion would hide the allocation. |
| An `any` type fixes every associated type of its trait. | A method that mentions an associated type could not otherwise be called. |
| The limits of `any` apply to a call, not to a trait. | A method that needs the concrete type cannot be called through `any`, and the error is at the call site. A trait never becomes unusable with `any` because one method does not fit, as a trait does under Rust's object-safety rules. |
| A dynamic call is verified against the contract of the trait. | Adding an `impl` checks only that `impl`, never the callers. |
| There is no downcast. | Code that needs to know which type it holds has a closed set of types, which a sum type expresses with exhaustive matching. |

## Tests

Rules: [Tests](SPECIFICATION.md#tests).

```truss
test "config loads with defaults" uses RunForever {
  let disk = files::MemoryFiles.new().with_text(Path.new("app.toml"), contents: "")
  let config = provide disk, log::DiscardLog() {
    load_config(Path.new("app.toml"))
  }
  assert config == Ok(Config.default())
}
```

A test provides every capability that its code uses other than `Panic` and
`RunForever`, which it declares, so its result is deterministic and is
cached until the code it runs changes.

**A test does not wait for proofs.** A program is built only when every
proof obligation that it reaches is proven. A test build instead inserts a
run-time check at every primitive operation that can fail. Generated code
therefore has no undefined behavior, even where a proof is pending or has
failed, and a test runs as soon as its code type-checks, alongside the
prover. A failed check names the operation, which tells an agent whether a
failed proof is a real bug or a prover that needs a hint. A test build
checks every operation, proven or not, so a test result does not depend on
the state of any proof.

**No clause is evaluated at run time.** Evaluating a `requires` would pay
for its proof a second time, at the cost of the clause: a test build would
make `binary_search` linear by checking that its list is sorted. Each check
in a test build takes constant time.

| Rule | Reason |
|---|---|
| A test with `uses` is external: it gets the real implementations, and its result is never cached. | Its result depends on the world. It gets no hidden isolation: a test that wants a scratch directory narrows file access where a reader can see it. |
| A test declares `Panic` and `RunForever` as a function does, and a test that declares only those is deterministic. | A test's signature states its effects like any other. Neither a panic nor a loop that runs forever depends on the world, so the suite caches the result of such a test. |
| A failed test is never retried. | A retry hides exactly the failures that an external test exists to catch. |
| A test cannot expect a panic. | That would treat a panic as intended behavior, which is the job of `Result`. The misuse that other languages test this way, such as a violated precondition, does not compile. To check that a program crashes on bad input, an external test runs the program through `Processes`. |
| A test has a time limit. | A loop that never ends fails its test. |

[Shared state](#shared-state) explains how a test of concurrent code stays
deterministic.

## Proofs

Rules: [Proofs](SPECIFICATION.md#proofs).

Every promise of a program is proven at compile time: contracts,
invariants, laws, loop invariants, and every operation that can fail.

```truss
theorem reverse_twice[Element](items: Sequence[Element])
  ensures identical(items.reversed().reversed(), items)
{
  assert forall i in 0..items.length() =>
    identical(items.reversed().reversed()[i], items[i])
}
```

**Verification is modular.** The prover knows another function by its
signature, and reads a body only in the cases that
[Bodies and contracts in proofs](#bodies-and-contracts-in-proofs) lists.
Each proof therefore reads little code, which keeps proofs stable and
proving O(change).

**Proof checking is deterministic.** The version of the solver is pinned,
and its limits are counted in steps, never in wall-clock time. A proof that
passes once keeps passing, and a slow machine never fails a proof that a
fast machine passes. Solver-based tools are known for proofs that break
after an unrelated edit, and Truss is designed against that instability from
the start.

| Rule | Reason |
|---|---|
| Each obligation goes to an automated solver, as in Dafny. | A programmer writes a proof only where the solver fails. |
| A proof is written in the language's own syntax: calls, `match`, `if`, and `assert`. | Programmers and LLMs already know that syntax. |
| A proof is a result of its own. | An edit to a proof re-checks proofs, with no rebuild of the program and no rerun of tests. A reviewer trusts a checked proof without reading it, and reads only signatures. |
| There is no `assume`. | A missing proof that an addition cannot overflow would allow a failure that the signature does not show. A claim that is not ready is left out of the signature. |

### Bodies and contracts in proofs

Rules: [Bodies and contracts in proofs](SPECIFICATION.md#bodies-and-contracts-in-proofs).

**A caller's proof reads the contract of its callee, never its body.** A
function whose body is its definition, such as `is_sorted`, states the body
in its `ensures`:

```truss
fn is_sorted(items: Slice[Int64]) -> Bool
  ensures result == (forall index in 1..items.length() => items[index - 1] <= items[index])
```

The dependency is then in the signature, where a reader sees it, and an edit
to the body re-proves that function alone. Verus knows an `exec fn` by its
contract in the same way. Truss needs no second function, for specifications
only, to state the definition.

| Rule | Reason |
|---|---|
| A method of a trait or of an `impl` is known by its contract too. | An `impl` states what it adds to the trait's contract in its own `ensures`: `Int64.compare` ensures the order of the integers. An edit to a provided body then changes no fact that callers know. An edit to an `impl`'s body re-proves that method and the `impl`'s laws alone. |
| An `ensures` that fixes a pure function's result is the call's value: `identical(result, e)`, or `result == e` where `==` is structural, as on integers. An `e` that calls the function itself is not used. | A fact about a call then needs no term of the call to take effect. `List.element` ensures `identical(result, self.model()[position])`, so a quantifier over a list's elements is a quantifier over its model, which code that indexes the list instantiates. A type's own `Equal` is not identity, so it fixes no value, and a recursive definition is not unfolded. |
| A clause applies only where every name it mentions is visible. | An `ensures` that reads the fields of an opaque type is a fact inside the type's package and no fact elsewhere, so `opaque` hides the representation from proofs too. |
| A public `requires` or `cost` names only public definitions, and an `ensures` may name a private function. | The proofs of callers in other packages read a `requires` and a `cost`, and a clause applies only where every name it mentions is visible. The `ensures` lets callers inside the package know a result in terms of private helpers. |
| A bit-level fact is requested with `assert ... by bit_vector`. | Bit-blasting is slow on most queries, so only the assertion that asks for it is proven that way, as with Verus's `by (bit_vector)`. Every other query knows a bitwise operation by a few facts, and no query falls back to bit-blasting. |
| A quantifier over a range or a collection is also an expression in code. | The binder carries its range, so the body may rely on it. A lambda passed to a method would know nothing about its argument. The standard library therefore has no `all` or `any` methods, and a test of every element has *one spelling*. |

### Writing specifications

Rules: [Writing specifications](SPECIFICATION.md#writing-specifications).

| Rule | Reason |
|---|---|
| A function called in a specification is pure: it uses no capability, not even `Panic` or `RunForever`. | A function that might not return, or might end the program, has no value to reason about, and a definition that is not well founded would make the logic unsound. |
| A specification is read left to right. | `index < items.length() && items[index] > 0` is well defined. |
| `==>` exists, and only in specifications. | "If this holds, then that holds" is the commonest form of a specification, and `!a \|\| b` hides it. `==>` binds more loosely than `&&` and `\|\|`, as in Dafny. Code already has `if`. |
| Integer arithmetic in a specification is exact. | A specification cannot have an overflow bug, and `decreases high - low` can be negative, which is the case that the prover must rule out. |
| An `Integer` converts implicitly where a built-in integer is expected. | The obligation that the value fits is proven either way. |
| A function for specifications has no keyword. | Its signature already mentions a type that exists only in specifications. |
| Float arithmetic in a specification follows IEEE 754. | Exact real arithmetic would describe results that the hardware does not produce, so such a contract could never be proven. |

**A type gives its value to specifications as a mathematical model.** A
contract about a whole collection needs a value to state it in. Stated with
`length()` and indexing alone, "`push` appends an element" takes a
quantifier in every clause, and a collection's own `Equal` may be
hand-written and so not identity. The prelude therefore has mathematical
collections that exist only in specifications, such as `Sequence`, and a
type gives its value in their terms through the trait `Model`:

```truss
fn List[Element].push(mut self, item: own Element)
  ensures identical(self.model(), old(self.model()).append(item))
```

| Rule | Reason |
|---|---|
| The equality of the mathematical types is identity. | The prover substitutes through a model where the collection's own `Equal` is hand-written. |
| An opaque type has a model. | Other packages reason about the type through its model, without its fields. |
| `identical(a, b)` is identity, and is separate from `==`. | A generic contract must say that an element is a given value, whatever its type. `==` cannot say that: it is the type's `Equal`, which `List[Element]` does not require, and which is an equivalence and not identity for a set stored as an unsorted list. `==` therefore keeps one meaning everywhere. |

## Unfinished code

Rules: [Unfinished code](SPECIFICATION.md#unfinished-code).

```truss
fn render(report: Report) -> String {
  let header = render_header(report.title)
  let body = todo
  "${header}\n${body}"
}
```

The API of a package can be designed before it is implemented, with `todo`
in place of an expression, a body, or a type definition.

| Rule | Reason |
|---|---|
| Code with a `todo` is type-checked and proven. | A caller's contracts are proven before its callees exist. |
| A release build refuses a program that can reach a `todo`. | A `todo` that panicked when reached would be a failure that the signature does not show. |
| A test that reaches a `todo` is incomplete, not failed. | Tests can be written first. |

## Debug output

Rules: [Debug output](SPECIFICATION.md#debug-output).

`echo expr` shows a value from pure code, with no `uses`.

| Rule | Reason |
|---|---|
| Proofs and cost clauses read `echo expr` as `expr`. | Adding an `echo` never changes whether code compiles or verifies. |
| A release build refuses a program that can reach an `echo`. | `echo` cannot ship, which makes it safe to allow without `uses`. |

## Modules and visibility

Rules: [Modules and visibility](SPECIFICATION.md#modules-and-visibility).

```truss
use standard::json

let settings = json::parse(text)?
```

| Rule | Reason |
|---|---|
| `use` imports a module, never a name. | Every name from another module shows its origin, and two modules can both define `ParseError`. |
| There are no import aliases. | An alias would let one definition go by different names in different files. |

### Module paths

Rules: [Module paths](SPECIFICATION.md#module-paths).

**A module is a directory, and its files share one namespace,** as the files
of a package do in Go and the files of a module do in Swift. A file names
the definitions of the module's other files as it names its own, so
splitting a module into files is a choice of layout and costs no prefixes.
Where each file is a module and an import brings in only a module, a program
of several files writes a prefix at every use of its own code. Each file
keeps its own `use` lines, so a file shows the modules that it depends on.

| Rule | Reason |
|---|---|
| Every path starts with a package name, even inside the package. | A path is written the same everywhere and is found by a text search. A relative path gives one module a different spelling at each place that names it. |
| Modules can depend on each other in a cycle. | Dependencies are tracked between definitions, not between files. |
| Module names have a namespace of their own, marked by `::`. | If a module name were an ordinary name, a variable called `url` would shadow the module for the rest of its scope, and an import could change the meaning of a name in unrelated code. |

### The prelude

Rules: [The prelude](SPECIFICATION.md#the-prelude).

The prelude holds the names that nearly every program needs. It is the same
in every file, so `List` or `Result` means one thing everywhere.

| Rule | Reason |
|---|---|
| No definition can have a prelude name. | A prelude name then never means two things. The cost is that a name is in the prelude only if the signatures of most programs use it: `Path` is in it, and `Pair` is not, because a package may want that name. |
| Every prelude name is `UpperCamelCase`. | A prelude name never conflicts with a variable or a function. |
| The prelude changes only with a language version. | A new prelude name can conflict with a type that a package defines. |

### Visibility

Rules: [Visibility](SPECIFICATION.md#visibility).

A definition is private to its module unless it is declared `internal` or
`public`, so the modular choice is the default. A public signature cannot
mention a private type, because other packages could never name the type.

**A `public opaque type` exposes its name and hides its fields,** for three
reasons:

1. Control over construction. Some types are safe only if other packages
   cannot construct them, such as `SqlQuery`, whose text must come from
   source literals.
2. Protection of low-level internals, such as the pointer and the capacity
   inside `List`.
3. Freedom to change the representation. A compatible release may change
   everything inside an opaque type ([Versions](#versions)).

A public type that is not opaque exposes its fields. The exposure is visible
in review, because the fields are written in the public declaration. The
fields of an opaque type are accessible throughout its package, not only in
one file, because the methods of a type can live in any file of the package.

**An `internal` definition that nothing in its package uses is an error,**
as an unused variable is. No other package can call it, so it is dead code,
and it keeps alive the code it calls. **A private definition that nothing
uses is a warning.** A private helper is often written before its first
caller, and an error would fail the check while that caller is unwritten.

**There is no level between `internal` and `public`.** Swift's `package`
level works because the code it spans is versioned as one unit. Truss
versions each package separately, so two packages that shared more than
their public definitions could be paired at versions that were never checked
together. Code that shares its internals belongs in one package. That costs
nothing, because a package is not a unit of building.

## No foreign code

Rules: [No foreign code](SPECIFICATION.md#no-foreign-code).

Truss code cannot call code written in another language.

**Foreign code would escape every guarantee.** A C function can do anything,
so its capabilities and contract could only be assumed, and Truss has no
`assume`.

**An ecosystem that could wrap C would be built on C.** Wrapping an existing
library is the quickest way to get one, and an LLM would take that shortcut
every time. The result would be an ecosystem over C code that no proof,
capability, or cost clause covers. Without foreign code, a young ecosystem
grows by being written in Truss.

Other decisions rely on the absence of foreign code:

| Decision | Reliance |
|---|---|
| Truss has no destructors ([Handles](#handles)). | Only the standard library creates handles. |
| The runtime chooses how tasks are scheduled ([Concurrency](#concurrency)). | Every call that blocks is in the standard library. |
| No package needs conditional compilation. | Code for one platform lives only in the standard library. Other code asks `Environment`, so the answer is tracked and a test can supply a different one. |

The cost is reach. Anything that needs the operating system or special
hardware is available only through the standard library.

## The standard library

Truss is batteries included, so most programs need no other dependency. Every
dependency is a target for a supply-chain attack.

A client for a product, such as `truss::postgres`, is an approved package
instead, owned by `truss` on the registry.

The standard library is part of the toolchain: it has no version of its own, and
it appears in no manifest and no lock file. A package instead names the language
version that it is written for, as in `truss = "1.4"`. Packages written for
different versions build together, as Rust's editions allow.

### Maps and sets

`Map` and `Set` iterate in insertion order. The order never varies from run
to run, so tests stay deterministic and their results can be cached.

**A `Map` resists hash flooding deterministically.** Keys that are chosen to
collide can turn each operation into a scan of the whole map. The usual defense
is a random hash key for each process. That would change timing and allocation
counts from run to run, and make a test near its time limit flaky. Instead, a
bucket that fills up becomes a balanced tree, so the worst case is O(log n),
which a `cost` clause can promise. This is why a key is `Ordered` as well as
`Hash`.

### Conventions

| Convention | Reason |
|---|---|
| A method that needs no ownership of the storage is declared once, on the view type. | A `String`, a `List`, and an `Array` have the methods of their views ([Method lookup](#method-lookup)), so `mut names.sort()` works without `names[..]`, and a second declaration on the owning type would only forward. The owning type declares a method of that name where it uses its storage: `List.reverse` keeps the list's capacity. |
| A capability declares only primitive operations. | A narrowing implementation or a fake has few methods to write. |
| Every failure of the operating system is a `SystemError`. | Code that reads a file and sends it over a connection handles one error type. |
| Text in an embedded language is a tagged template, and a `processes::Command` is a program and a list of arguments. | Neither is a string that is passed to an interpreter, so neither allows an injection. |
| A fake of a standard capability, such as `files::MemoryFiles`, returns the error that the operating system returns for each misuse. | Keeps error handling in tests consistent. |

## Packages

Rules: [PACKAGES.md](PACKAGES.md).

A package is the unit of every boundary that Truss checks: paths, `internal`
and `opaque`, the homes of methods and `impl`s, grants, and versions.

| Rule | Reason |
|---|---|
| A package is not a unit of building. | Results are cached per definition, so splitting a package makes no build faster. A package is split only where a boundary should be checked. |
| A project lists no members. | A list is one more file that every agent that adds a package must edit, and so one more place for a merge conflict (*parallel agents*). |
| A dependency names a package, never a path to it. | Moving a directory breaks no dependency. |
| A project's package replaces the registry's package of the same name. | This is how a dependency is patched before its owner releases a fix, with the patched copy in the repository for a reviewer to see. |
| A registry package is named `owner::name`. | Much malware arrives by typosquatting: a name one letter away from a well-known name. LLMs make it worse by inventing package names, which attackers then publish. With an owner in the name, every path that uses the code says who published it. |

### Versions

Rules: [Choosing versions](PACKAGES.md#choosing-versions),
[Versions](PACKAGES.md#versions).

**A build holds one version of each package,** because a path means one
thing. Where two versions share a build, one path names two types, which is
Rust's "expected `Vector`, found `Vector`".

**A build uses the newest version that any of its packages was checked with,
and nothing newer.** This is Go's minimal version selection. Selecting the
newest release that a range allows puts a release that was published an hour
ago into every build, which is how a compromised release reaches thousands
of machines before anyone has read it.

| Rule | Reason |
|---|---|
| There are no version ranges and no solver. | Selecting versions under ranges is NP-complete, and its answer changes as packages are published. The answer of minimal version selection depends only on the lock file, so it is the same on every machine, every day. |
| Two edits to a lock file merge by taking the higher version of each package. | A solver's lock file cannot be merged without solving again (*parallel agents*). |
| A release may change a function's result within its contract. | This is how a fix reaches its users. A guarantee that users are meant to rely on goes in an `ensures`. |

### The registry

Rules: [The registry](PACKAGES.md#the-registry).

| Rule | Reason |
|---|---|
| A package is published as its source. | The code that a reviewer reads in the registry is the code that compiles. |
| The registry keeps an append-only public log of the hash of every version, as Go's checksum database does. | The registry cannot give two users different code under one version. |
| The registry signs the proofs and test results that it computed for a release. | Proving a whole dependency tree on a machine that starts with nothing, such as an agent's new container, is the cost that GOALS.md sets out to remove. Each signed result is a function of its key, so a registry that signed a false result is caught by anyone who recomputes it. |

## Incremental builds

GOALS.md asks that building, testing, and proving cost O(change), not
O(project). Text files stay the source of truth: programmers and tools edit
ordinary files. A code database holds each definition of a project and the
facts derived from it, such as its interface, its contract, its checked
body, its proof, and its compiled code. Each of these facts is a *part*. A
change to the files propagates through the database as far as it changes a
part, and no further, and the rules of the language keep that distance
short.

A definition's identity is its kind, its structure, the names it resolves
to, the names of its local variables, the values of its literals, and the
order of its clauses within each kind. An edit that changes none of these
changes no definition.

| Edit | Recomputes | Reason |
|---|---|---|
| Reformat a file, or move a definition within its file or to another file of its module | The parts that hold positions, of the definitions whose text changed. Nothing that another definition reads. | Identity excludes the file, the position in the file, the surrounding definitions, and the layout. |
| Edit a body, such as replacing a `todo` | The check, the proof, and the code of that body, and the template checks that run it. No caller is re-checked or re-proven. | A definition names its dependencies by module path and name, never by content, and callers depend on the signature alone. |
| Strengthen an `ensures` | The proofs of callers. No caller is type-checked. | A signature has two parts: the interface, which the types of callers depend on, and the contract, which only the proofs of callers depend on. |
| Change the default of a parameter | The proofs and tests of the callers that omit the argument, and the code of the callee alone | The interface records only that the parameter has a default, and the callee applies it. |
| Reorder the fields of a record | Nothing, unless the type derives `Ordered` | The compiler chooses the layout, and a record with more than one field is constructed with labeled arguments. |
| Add a `derives` | Nothing that exists | Each derived implementation is a definition of its own, generated from the trait and the fields of the type. |
| Add, remove, or rename a definition | The parts that refer to its name, whether or not a definition held the name before | Each reference names one fully qualified name, so no lookup searches (see [References to names](#references-to-names)). |
| Rename a definition, or move it to another module | The type checks and the code of its users. Their proofs and test results are cache hits. | A user names the definition. A solver query and a test's key hold no names. |
| Rename a local variable | One body | Local names are part of identity, because diagnostics and `echo` output show them, and a cached result would show the old name. |
| Change the spelling of a literal, such as `0xFF` to `255` | Nothing | Identity holds the value of the literal. |
| Reorder clauses | Nothing between kinds of clause. The definition, within one kind. | Each `requires` may rely on the `requires` before it. |
| Upgrade a dependency | The dependents of the dependency's diff | A path holds no version, so a new version of a package is an edit to code that the project does not own, and is tracked as any edit is. |

### The code database

**The database is a function of the files and the compiler.** A database
that propagated a thousand edits equals one built from the same files from
scratch. Nothing in it depends on the order of the edits, so a copy of one
worktree's database is a correct start for another, and a hot build and a
cold one agree.

**A definition is identified by its name, not by its content.** Unison
identifies a definition by a hash of its content and of its dependencies'
hashes, so an edit gives every transitive dependent a new identity, and every
result keyed by that identity is computed again. Here an edit rewrites the
parts of one definition, and a rename rewrites the references of its users.

**Propagation stops where a part comes out unchanged.** Most changes stop
one hop from the edit, because a caller reads the callee's signature and
contract, which are written in the source.

### References to names

**A reference is to a fully qualified name, whether or not a definition
holds the name.** A name that is not local and not in the prelude belongs to
the body's module, so an unqualified name resolves without a search.

### Failing code

**A part that fails holds its errors in place of a value.** Nothing is
derived from it. A part that reads it is blocked: it is not computed, and it
reports no error of its own, so one broken signature reports one error, not
one in each of its callers. Fixing the error computes the failed part and
the parts blocked behind it, and nothing else.

**A failure belongs to the part whose syntax holds it.** A resolution error
or a type error in a body fails the body, never the interface or the
contract, so a typo in a body blocks no caller.

| Rule | Reason |
|---|---|
| The database keeps no earlier version of a failing part. | An earlier version would make the database depend on the order of the edits. A caller checked against an earlier signature would also report errors that the files do not hold. |
| A build, a test run, or a template check requires that no definition it reaches has errors. | No run executes code that the files do not hold, and a test whose code is correct runs while unrelated code is broken. |

### Caches

The user's cache holds the results that are expensive to compute: solver
answers, object files, test results, the databases of the standard library
and of registry packages, and fetched packages. Each is keyed by its whole
input.

A cache never makes a result wrong: deleting it only makes the next build
slower. Every worktree and CI share the caches. The database itself caches
nothing, so a revert or a branch switch is a change to the files like any
other. The database computes the cheap stages again, and the solver, the C
compiler, and the tests are cache hits.

## Omitted features

| Feature | Reason, or the section that gives it |
|---|---|
| Comments | [Comments](#comments) |
| Numeric literal suffixes | [Number literals](#number-literals) |
| Tuples and type aliases | [Type definitions](#type-definitions) |
| A garbage collector, lifetimes, stored references, and mutable global state | [Values and ownership](#values-and-ownership) |
| Destructors | [Handles](#handles) |
| Generators and coroutines | [Lending methods](#lending-methods) and [Loops](#loops) |
| Closures that mutate captured variables, trailing lambdas, short lambda forms, and implicit lambda parameters | [Lambdas](#lambdas) |
| Overloading by parameter type | [Overloads by receiver mode](#overloads-by-receiver-mode) |
| `into()` | Rust infers the target of `into()` from context, which is a common source of inference failures. A conversion names its target, as in `Int64.from_integer(count)`. |
| `++`, `--`, and chained comparisons | [Operators](#operators) |
| A string concatenation operator | [Strings](#strings) |
| Exceptions and catching a panic | [Failure](#failure) |
| `exit` | [Capabilities](#capabilities) |
| `async` | [Concurrency](#concurrency) |
| A mutex as a value | [Shared state](#shared-state) |
| Blanket `impl`s, overlapping `impl`s, and specialization | [Traits and laws](#traits-and-laws) and [Implementations](#implementations) |
| Downcasting | [Dynamic dispatch](#dynamic-dispatch) |
| Macros | `derives` covers the uses of Rust's `#[derive]`, and a procedural macro would run a dependency's code during a build ([Grants](#grants)). |
| Expected-time bounds | [Cost clauses](#cost-clauses) |
| `assume` | [Proofs](#proofs) |
| Import aliases and relative module paths | [Modules and visibility](#modules-and-visibility) |
| A visibility level between `internal` and `public` | [Visibility](#visibility) |
| Foreign code and conditional compilation | [No foreign code](#no-foreign-code) |
| Version ranges, a version solver, and 0.x versions | [Versions](#versions) |
| Optional features of a package, such as Cargo's features | Features exist to keep unwanted code out of a build. Truss never compiles code that nothing reaches and grants it nothing, so a switch has nothing to save. Features cost Cargo builds that work only with some sets of switches. |
| A separate list of dependencies for tests | The dependencies that only tests reach are computed when a package is published. |
| A dependency on a git repository or a directory | Unpublished code is worked on in the project that uses it. |
| Build scripts, install scripts, and code generators | [Grants](#grants) |
| Tuples | Naming by position allows users to mix up which is which. destructuring suffices |
| Type aliases | A type name always means one type |
