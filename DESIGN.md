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
public fn binary_search(sorted: Slice[Int64], target: Int64) -> Option[USize]
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
capabilities, contract, and cost could only be assumed, and the three
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

The sections on the language use the headings of SPECIFICATION.md and follow
its order, except where one argument spans several of its sections. The
standard library, packages, and incremental builds follow them. Each section
opens with a link to the rules it explains. A section states a rule before
its reason, argues in prose the decisions that cost something, and lists the
rest in a table. [Omitted features](#omitted-features) lists the features
that Truss leaves out and where each is explained.

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

Truss has no comments. A comment goes stale without the compiler noticing,
and LLMs fill code with comments that repeat it. The content of a comment
moves into a form that the compiler checks:

| Content of a comment | Form in Truss |
|---|---|
| The purpose of a definition | Its name |
| The behavior of a function | Its signature, `requires`, and `ensures` |
| A fact that always holds | An invariant or a law |
| The cost of a call | A `cost` clause |
| An example of use, or a requirement | A test and its name |
| The reason for a piece of code | A name, such as `treat_missing_account_as_empty` |
| A description of a package | A Markdown file beside the code |

### Names

Rules: [Names](SPECIFICATION.md#names).

**Names are ASCII.** A homoglyph, such as a Cyrillic `а` in place of a Latin
`a`, slips a malicious edit past review. Allowing every script safely takes
normalization, rules about mixed scripts, and Unicode's list of confusable
characters checked against every name. Those rules change with each Unicode
version and still leave gaps. The cost is that a team cannot name things in
its own language. Strings and documentation take any language.

| Rule | Reason |
|---|---|
| A name uses whole words. This is a convention, not a compiler rule. | Code is read more often than it is written, and an LLM types a long name at almost no cost. A compiler rule would reject the reasonable exceptions. |
| A constant is `lower_snake_case`, as a value is. | A third case would give the lexer a third class of name, and an `UpperCamelCase` constant would be indistinguishable from a type. |

### Keywords

Rules: [Keywords](SPECIFICATION.md#keywords).

| Rule | Reason |
|---|---|
| A keyword is reserved everywhere. | The lexer tells a keyword from a name without the parser. The lexer alone can then decide whether a line break ends a statement ([Line breaks](#line-breaks)). |
| The words of specifications, such as `result` and `time`, are contextual keywords that the parser recognizes. | Each is a common name that a clause needs in one position, and reserving it would ban it from all code. The parser recognizes these words because a lexer mode would have to know where each clause ends. |
| Keywords of other languages, such as `loop` and `async`, are reserved for later use. | Adding one later breaks no code. |

### Number literals

Rules: [Number literals](SPECIFICATION.md#number-literals).

| Rule | Reason |
|---|---|
| A literal takes its type from its context, and has no suffix. | *One spelling:* `3` is written one way for every integer type. |
| A literal operand takes the type of the other operand. | Go's untyped constants work this way. The rule never consults the set of `impl`s, so adding an `impl` never changes the type of an existing literal. Rust lets the search for an `impl` decide, so an `impl` added later can make an existing call ambiguous. |
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
| Trailing whitespace is kept. | A raw string has no escape to write it with. |
| An interpolation starts at `${`. | A single `{` or `$` as the marker would need escapes throughout JSON, regular expressions, and shell text. `${` is rare in ordinary text, as JavaScript's template literals show. |
| Text that contains `${` opens the string with more `$`s. | A longer delimiter is already the remedy for text that contains `"""`. A fixed escape such as `$${` would make one sequence special in a string that has no escapes. |
| A line break in a string is `\n`. | A string has the same value and the same hash whatever line endings its file uses. |

### Rejected sequences

Rules: [Rejected sequences](SPECIFICATION.md#rejected-sequences).

This is the *LLM habits* principle applied to tokens. `--x` could mean
`-(-x)`, and `//` could be two divisions. Both are errors, so a habit from
another language never compiles to a different program. Rejecting a sequence
also keeps it free: a later language version can give `//` a meaning without
changing existing code.

A stray `;` is rejected, not ignored. Ignoring it would give each statement
two spellings (*one spelling*).

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

The tokens that continue a line are exactly the tokens that cannot begin a
statement, so the list is derived from the grammar, and a closing `}` needs
no special case. Truss reads a line that starts with `-` as a new statement.
If the author meant a subtraction, the statement leaves an unused value,
which is an error, so the misreading never compiles.

The lexer applies the rule alone, with no type information, no parser state,
and no indentation, because keywords are reserved.

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

**Code is verified for both widths of `USize`.** The prover knows only that
`USize` has 32 or 64 bits. A proof therefore holds on every target, and a
cached proof needs no target in its key. A package that runs only on 64-bit
targets says so with `usize_bits = 64`, and only a package that says the
same can depend on it. A package without the setting therefore runs on every
target, dependencies included.

| Rule | Reason |
|---|---|
| A size, a length, and an index are `USize`, and an offset is `ISize`. | A length is never negative, and a bounds check is one comparison. |
| A `Character` is a Unicode scalar value. | It has a fixed size, so it is `Plain`, and its definition does not change between Unicode versions. A grapheme cluster has no fixed size, and its boundaries change as Unicode adds rules, so a grapheme is a slice of its string. |

### Type definitions

Rules: [Type definitions](SPECIFICATION.md#type-definitions).

**A record with one field is how Truss writes a newtype.** Values with
different meanings get different types, as in
`type UserId(number: UInt64)`, with no syntax of their own:

- Construction, field access, `with`, invariants, and `opaque` work as they
  do for any record.
- The author names the field. `port.number` names the contents of the
  record, and a built-in name such as `.value` would not.
- The new type inherits no operations, because many would be meaningless:
  adding two `UserId`s is.

**Truss has no tuples.** An element that is read by position has no name, so
nothing stops a caller from reading a width and a height in the wrong order,
and `-> Option[(Int64, Int64)]` says less than `-> Option[Extremes]`. A
record pattern omits the type name, so destructuring stays short, as in
`for (index, element) in scores.enumerate()`. The pattern matches fields by
name. `(i, item)` is therefore an error that names the fields, not a silent
positional match.

Truss has no type aliases, so a type name always means one type.

### Recursive types

Rules: [Recursive types](SPECIFICATION.md#recursive-types).

A recursive variant is marked `indirect`, so the allocation is written where
the type is declared (*nothing hidden*). Rust writes the same allocation as
`Box`, which every pattern must then dereference. `indirect` leaves patterns
unchanged.

### Generic parameters

Rules: [Generic parameters](SPECIFICATION.md#generic-parameters).

Generic code is monomorphized, so a generic function costs nothing at run
time. Monomorphization rules out polymorphic recursion. Truss reports
polymorphic recursion during type checking, as Go does. Rust reports it
later, when instantiation fails.

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
| A mode keyword applies to the longest place expression at the start of its operand. | `mut config.servers.sort()` takes `mut` access to `config.servers` alone, so the same statement can use the other fields of `config`. |
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
| A handle is not `Copyable`. | Copying one would duplicate an operating-system handle, which can fail, and `copy()` cannot fail. |
| Generic code copies only under a `Copyable` bound. | An unbounded type parameter then accepts every type, handles included. |
| A string literal is copy-on-write: it is an owned `String` with no `copy()`, copied to the heap at its first mutation. | Only the methods that write bytes mutate a `String`, and each of those may allocate anyway, so copy-on-write changes no `cost` clause. |

### Views

Rules: [Views](SPECIFICATION.md#views).

A view is a read-only reference to a value that another variable owns. A
read-only parameter, a `let` bound to a place, the variable of a `for` loop,
and a slice are views:

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
| A lending call lends its whole receiver. | The method was proven on the assumption that nothing else uses `self` while the part is lent. |
| `List`, `Slice`, and `Array` can lend two parts at once. | Their elements at different positions are disjoint places. |

### Loops

Rules: [Loops](SPECIFICATION.md#loops).

A `for` loop over a collection visits it by position. The loop evaluates
`count()` once, and each iteration is lent `element(position)`. A type
supports `for` by defining those two methods:

```truss
fn Grid.count(self) -> USize
fn Grid.element(self, position: USize) lends Cell
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

A `while true` that no `break` leaves has type `Never`, so a server whose
main loop runs forever can return `Never`.

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
fn List[Element].map[Output](
  self,
  transform: (fn(element: Element) -> Output requires self.model().contains(element)),
) -> List[Output]

let picked = indices.map(fn(i) { values[i] })
```

The `requires` tells the lambda that `i` is an element of `indices`, and
from that the lambda proves `values[i]` in bounds. A `requires` is allowed
only on the type of a parameter, so no type that values are stored in or
compared by carries one.

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
| A constant `Map` or `Set` is built at compile time by the standard library's insertion code, with no random hash key. | A lookup has the cost it has on any map, and the table is identical in every build (*determinism*). |
| Code that runs at compile time is compiled and run as a test is, not interpreted. | Truss then has one implementation of its semantics, and a result computed at compile time equals the result in the compiled program, including the width of `USize`. Such code only discharges proofs and produces static data, so type checking never depends on it. |

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
from its first use. Otherwise `let limit = 10` would fix `limit` at `Int64`,
and code that works in `UInt8` or `USize` would annotate every such local.
Only the type of a literal is left undecided, and it can only become a
number type, so the declaration still tells the reader that the local is a
number. A later use that disagrees is one error, with a note at the
statement that decided the type.

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
less-than operator. Brackets have no such conflict. The parser builds one
tree for both uses, and name resolution decides between them, which the
rules of [Scope](#scope) keep simple. Two costs follow:

1. A highlighter that works from the text alone can mistake
   `items[Color.Red]` for a type argument, so exact highlighting comes from
   the language server.
2. A diagnostic about `f[X]` must say which reading applied.

### Termination

Rules: [Termination](SPECIFICATION.md#termination),
[Recursive types](SPECIFICATION.md#recursive-types).

**The recursion check follows every edge of the call graph.** A function
reaches itself by a direct call, by naming a function as a value, and by
passing an `impl` where a bound needs one, because the code that receives
the function or the `impl` can call back. If the check ignored the last two,
a package could implement a trait with a method that calls a generic
function that calls the method back, and each `time` clause would be proven
by assuming the other. Every such cycle is visible within one package,
because Truss has no mutable state outside variables and because of the next
rule.

**A type cannot hold a terminating function that takes the type.** With
`type Knot(run: (fn(Knot) -> Bool cost time finite))`, a function that calls
`knot.run(knot)` calls itself, and no name in its code says so. Coq and Lean
forbid this for every function type, as strict positivity. Truss forbids it
only for a function type with a `time` clause, because a function with a
`time` clause cannot call one without. `type Button(on_click: fn(Button))`
is therefore legal.

| Rule | Reason |
|---|---|
| Structural recursion needs no annotation, and other recursion states `decreases`. The compiler never infers a measure. | Lean accepts structural recursion in the same way. Dafny infers a measure. A structural check with an explicit clause is more predictable than an inference that may fail. |
| A loop that runs until a capability says to stop has no termination proof. | An implementation could supply data forever. |

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
| A countable resource takes an exact bound, and time takes only `O(...)` or `finite`. | An exact bound can state that each item is processed exactly once. A concrete time cannot be proven across machines. |
| `O(f)` bounds the cost for every input, not only for large inputs. | The textbook definition is a limit, which a prover handles poorly, and it gives wrong answers for bounds in several variables. |
| A bound can mention `result`. | An output-sensitive bound, such as the bound of a function that returns its matches, cannot be stated otherwise. |
| `log(n)` is log₂(n + 1) rounded up. | It is defined at 0 and is an integer. Inside `O`, the base makes no difference. |
| The `time` of a generic function counts the methods of its bounds. | `O(self.length())` would be false for `contains` on a list of strings, where one comparison is not one step. `String` could not keep a promise of `O(1)` on `Equal.equal`, and a second trait for constant-time comparison would give every generic method two overloads. |
| A loop's cost is never `amortized` and never `finite`. | Potential belongs to the values that the loop mutates, and a loop proves termination with `decreases`. |

### Function types

Rules: [Function types](SPECIFICATION.md#function-types).

A function type puts its clauses after its result, inside parentheses, as in
`(fn(Request) -> Response uses Database, Log cost time finite)`. Truss has
whole clauses, not one or two effect keywords, so the clauses come in the
order they have in a definition, and the parentheses mark where they end.

## Methods

Rules: [Methods](SPECIFICATION.md#methods).

| Rule | Reason |
|---|---|
| A method is defined in the package of its type. | A method is easy to find, and two packages can never add conflicting methods to one type. |
| Every call uses parentheses. | *Nothing hidden.* A reviewer can tell that `names.length()` runs code and that `point.x` reads a field. |
| `Type.new(...)` is the main constructor, and other constructors have descriptive names. | `new` cannot be overloaded. |

### Overloads by receiver mode

Rules: [Versions by receiver mode](SPECIFICATION.md#versions-by-receiver-mode),
[Method lookup](SPECIFICATION.md#method-lookup).

A method can be overloaded on the mode of `self`, and on nothing else. One
`enumerate` serves read-only, `mut`, and `own` loops, where Rust needs
`iter`, `iter_mut`, and `into_iter`.

**An overload set has one author.** The overloads of a name come only from
the type's own methods, from the methods that an `impl` in the type's
package writes, and from a trait together with the traits it requires. If
overloads were collected from every visible `impl`, a package added to a
build could capture an existing call. A temporary receiver takes the `own`
overload when one exists, so a package that gave a type's `label(self)` an
`own self` overload would change the meaning of `Counter(3).label()`. A
provided method that an `impl` does not write is excluded for the same
reason: a later release of the trait can add one.

**There is no overloading by parameter type.** It would cost three things:

1. Type checking would stop being local and fast. Swift's "expression too
   complex to type-check" errors come from overloads combined with literals
   that take their type from context, and Truss has such literals.
2. An overload added anywhere could change an existing call.
3. A reader could not tell which `process` runs in `process(item)`.

A trait with type parameters covers most uses of overloading:
`Int64.from(count)` selects an `impl` of `From[Source]` by the type of
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
| A constant in a pattern has a type with structural equality. | Matching the constant and comparing with `==` then agree. |
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
| Each collection has one literal form, `[a, b, c]` or `[key: value]`, which takes its type from its context. | *One spelling:* there is no `List.new()` or `List.of(...)`. A map uses brackets because `{` starts a block. |
| A non-empty list literal counts as one allocation. | A `cost` clause does not depend on whether an optimization keeps the list in static memory. |
| A set or map literal desugars to calls of `insert`. | A `cost` clause is checked against the code that runs. Distinct keys are the `requires` of `insert`, so a duplicate key is a failed proof. Letting the last key win would hide a mistake. |
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
| `echo` takes everything after it. | Putting `echo` in front of an expression shows the whole expression. |
| A range binds more loosely than arithmetic. | `0..count - 1` means `0..(count - 1)`. |
| `+=` exists, and `++` and `--` do not. | `a += b` evaluates the place `a` once, so a long place expression is not mistyped the second time, and an index is proven in bounds once. As expressions, `++` and `--` are confusing and rarely clearer than `+= 1`. |
| A compound assignment passes the old value to the operator as owned. | `matrix += other` can update in place, with no separate trait such as Rust's `AddAssign`. |
| An assignment evaluates its right side before its target. | The target of a compound assignment holds no value from the move of its old value until the store of the result. Evaluating the operand first keeps all other code out of that interval, so a `?` in the operand cannot return with the target moved out. |

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
compile time equals the value in the compiled program. `to_bits()` returns
one bit pattern for every NaN, because processors disagree about which NaN
an operation produces.

## Failure

Rules: [Failure](SPECIFICATION.md#failure).

A function panics only if its signature declares `uses Panic`. The
exceptions are running out of memory and overflowing the stack, which no
language rules out.

Every operation that can fail is a proof obligation: an integer overflow, a
division by zero, an index out of bounds, a shift that is too large, and
`unreachable`. Code meets an obligation in one of four ways. It establishes
the fact locally, requires the fact of its caller, calls a checked variant
that returns an `Option` or a `Result`, or declares `uses Panic`.

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

**A capability method always returns to its caller, once.** A capability
call therefore compiles as a function call, Truss needs no stack unwinding,
and no computation is abandoned with a value half updated. An early exit
goes through `Result` and `?`, where each step is written. For the same
reason there is no `exit`.

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
own dependencies more than it holds. A new release cannot take more
capabilities for a function that is already called, because adding a
capability to a function's `uses` is not a compatible release
([Versions](#versions)).

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
| A branch uses no capabilities. | Two branches that called one stateful implementation would race, and the order of their calls would vary from run to run. A function that contains `parallel` is therefore still pure, and a test that runs it is cached. Code whose branches use capabilities is [concurrent](#concurrency). |
| The input decides where a computation is split, never the number of cores. | The result does not depend on the machine: a parallel float sum gives the same bits everywhere (*determinism*). |
| A test runs the branches in order. | The test runner already runs one test on each core, and a failed check is the same on every run. |
| A branch cannot exit the block early. | A branch uses no capabilities, so it cannot be asked to stop. An early exit would have to abandon the other branches, or wait for work whose result is discarded. |

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
such an implementation takes no callback that uses a capability.

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
| The tag is a type. | The tag names the type of the result, and a plain string is the case where the tag is `String`. A tag function would have a lowercase name, and the prelude holds only `UpperCamelCase` names ([The prelude](#the-prelude)). |
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

**A provided method can be overridden only by a method that is proven to
return the same result.** `a != b` therefore always means `!(a == b)`, the
prover reasons from the trait alone, and adding an `impl` never changes the
semantics of a provided method. A type can still override a provided method
with a faster one. This covers most uses of specialization, with no
overlapping `impl`s. A fast path that depends only on the representation of
a type, such as copying a list of `Plain` values at once, needs no language
feature: the compiler knows which types are `Plain`.

**An `impl` can promise more than its trait:** a weaker precondition and a
stronger postcondition, which is behavioral subtyping. `Index` can then say
nothing about the lent part, while the `impl` for `List` says which element
it is.

| Rule | Reason |
|---|---|
| A trait can require other traits. | A law can then span traits. `Hash` requires `Equal`, so its law, that equal values hash equally, is stated and proven. In Rust, `Hash` does not require `Eq`, and that law is only a comment. |
| A type has one `impl` of each trait. | Two traits that both require `Equal` share that `impl`, so there is no diamond problem. |

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

**Only structural equality lets the prover substitute.** From `a == b` the
prover concludes `f(a) == f(b)` only when no function can distinguish equal
values. Three kinds of equality are not structural:

| Equality | Reason |
|---|---|
| A hand-written `Equal` | It promises only an equivalence relation. |
| Float equality | `Point(x: 0.0, y: 0.0) == Point(x: -0.0, y: 0.0)`, and `1.0 / x` distinguishes the two. |
| The equality of an opaque type, outside its package | It would depend on fields that other packages cannot see. |

Whether a type's equality is structural is derived from its fields, as
`Plain` is.

### Deriving

Rules: [Deriving](SPECIFICATION.md#deriving).

| Rule | Reason |
|---|---|
| Deriving is opt-in. | An `Equal` on a public type is a promise to its users, and structural equality is wrong for some types, such as a set stored as an unsorted list. |
| A derived `Ordered` or `Hash` needs a derived `Equal`. | The laws of `Ordered` and `Hash` relate them to `Equal`, and two derived implementations agree by construction. A hand-written `Equal`, such as that of a set stored as a list, would not agree with a field-by-field `Ordered` or `Hash`. |
| One derived `Serialize` serves every format. | Its methods are generic over a `Serializer`. A type that needs other field names writes the `impl`, because Truss has no attributes. |
| Every type has debug output, with no derive. | The test runner can show any value. Text for people goes through `Display`, which is written by hand, because a structural dump is rarely fit for a user. |

### Method lookup

Rules: [Method lookup](SPECIFICATION.md#method-lookup).

| Rule | Reason |
|---|---|
| A trait method needs no import. | A forgotten import is a common error in the languages that need one. |
| A method call finds only the traits of the standard library, of the calling package, and of the packages that its manifest lists. | An edit deep in the dependency graph cannot break a distant call. |
| Two candidates for one name are an error, never a silent choice. | In Rust a type's own method wins over a trait's, so adding a method can silently change an existing call. In Truss an upgrade can break a call only with an error that names both candidates. A release that only adds names is still compatible, because otherwise no type could ever gain a method. |

### Dynamic dispatch

Rules: [Values of any type with a trait](SPECIFICATION.md#values-of-any-type-with-a-trait).

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
test "config loads with defaults" {
  let disk = files::MemoryFiles.new().with_text(Path.new("app.toml"), contents: "")
  let config = provide disk, log::DiscardLog() {
    load_config(Path.new("app.toml"))
  }
  assert config == Ok(Config.default())
}
```

A test provides every capability that its code uses, so its result is
deterministic and is cached until the code it runs changes.

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
| A failed test is never retried. | A retry hides exactly the failures that an external test exists to catch. |
| A test cannot expect a panic. | That would treat a panic as intended behavior, which is the job of `Result`. The misuse that other languages test this way, such as a violated precondition, does not compile. To check that a program crashes on bad input, an external test runs the program through `Processes`. |
| A panic ends one worker process, and the test runner starts another. | Tests share a process safely, because Truss has no mutable global state and a test reaches only its inputs. |
| A test has a time limit. | A loop that never ends fails its test. |

[Shared state](#shared-state) explains how a test of concurrent code stays
deterministic.

## Proofs

Rules: [Proofs](SPECIFICATION.md#proofs).

Every promise of a program is proven at compile time: contracts, cost
clauses, invariants, laws, loop invariants, and every operation that can
fail.

```truss
theorem reverse_twice[Element](items: Slice[Element])
  ensures items.reverse().reverse() == items.to_list()
  decreases items.length()
{
  match items.split_first() {
    None => {}
    Some((first, rest)) => {
      reverse_twice(rest)
      reverse_of_append(rest.reverse(), suffix: [first])
    }
  }
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

**A caller's proof reads the contract of a function, never its body.** A
function whose body is its definition, such as `is_sorted`, states the body
in its `ensures`:

```truss
fn is_sorted(items: Slice[Int64]) -> Bool
  ensures result == (forall index in 1..items.length() => items[index - 1] <= items[index])
```

The dependency is then in the signature, where a reader and the registry's
compatibility check see it, and an edit to the body re-proves that function
alone. Verus knows an `exec fn` by its contract in the same way. Truss needs
no second function, for specifications only, to state the definition.

| Rule | Reason |
|---|---|
| A method of a trait or of an `impl` is known by its body. | Its contract is the trait's, which says nothing about the implementing type, so the body is the definition: `Int64.compare` is the order of the integers. |
| A clause applies only where every name it mentions is visible. | An `ensures` that reads the fields of an opaque type is a fact inside the type's package and no fact elsewhere, so `opaque` hides the representation from proofs too. |
| A public `requires` or `cost` names only public definitions, and an `ensures` may name a private function. | The contract of a function that other packages cannot see is not compared between releases. The `ensures` lets callers inside the package know a result in terms of private helpers. |
| A bit-level fact is requested with `assert ... by bit_vector`. | The assertion is proven alone by bit-blasting, universally over the integers and booleans it names, as Verus's `by (bit_vector)` is. Elsewhere the prover knows a bitwise operation by a few facts, and it never retries a query with bit-blasting. |
| A quantifier over a range or a collection is also an expression in code. | The binder carries its range, so the body may rely on it. A lambda passed to a method would know nothing about its argument. The standard library therefore has no `all` or `any` methods, and a test of every element has *one spelling*. |

### Writing specifications

Rules: [Writing specifications](SPECIFICATION.md#writing-specifications).

| Rule | Reason |
|---|---|
| A function called in a specification is pure, without even `Panic`, and has a `time` clause. | A function that might not return, or might end the program, has no value to reason about, and a definition that is not well founded would make the logic unsound. |
| A specification is read left to right. | `index < items.length() && items[index] > 0` is well defined. |
| `==>` exists, and only in specifications. | "If this holds, then that holds" is the commonest form of a specification, and `!a \|\| b` hides it. `==>` binds more loosely than `&&` and `\|\|`, as in Dafny. Code already has `if`. |
| Integer arithmetic in a specification is exact. | A specification cannot have an overflow bug, and `decreases high - low` can be negative, which is the case that the prover must rule out. |
| An `Integer` converts implicitly where a built-in integer is expected. | The obligation that the value fits is proven either way. |
| A function for specifications has no keyword. | Its signature already mentions a type that exists only in specifications. |
| Float arithmetic in a specification follows IEEE 754. | Exact real arithmetic would describe results that the hardware does not produce, so such a contract could never be proven. A float contract is checked bit for bit, which is slow, so float contracts are best kept rare. |

**A type gives its value to specifications as a mathematical model.** A
contract about a whole collection needs a value to state it in. Stated with
`length()` and indexing alone, "`push` appends an element" takes a
quantifier in every clause, and a collection's own `Equal` may be
hand-written and so not structural. The prelude therefore has mathematical
collections that exist only in specifications, such as `Sequence`, and a
type gives its value in their terms through the trait `Model`:

```truss
fn List[Element].push(mut self, item: own Element)
  ensures identical(self.model(), old(self.model()).append(item))
```

| Rule | Reason |
|---|---|
| The mathematical types have structural equality. | The prover substitutes through a model where the collection's own `Equal` is hand-written. |
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
| The tools list every `todo` with its expected type, the names in scope, and the work it blocks. | Each `todo` is a self-contained task, so several agents can fill them in at once (*parallel agents*). |

## Debug output

Rules: [Debug output](SPECIFICATION.md#debug-output).

`echo expr` shows a value from pure code, with no `uses`.

| Rule | Reason |
|---|---|
| Proofs and cost clauses read `echo expr` as `expr`. | Adding an `echo` never changes whether code compiles or verifies. |
| A release build refuses a program that can reach an `echo`. | `echo` cannot ship, which makes it safe to allow without `uses`. |
| An `echo` changes the cache keys of the tests that reach it. | Those tests re-run and show the output. Tests are deterministic, so the rerun takes the same path as the run under investigation. |
| The keyword is `echo`. | It is a whole word, and `debug` and `trace` are common names for variables and functions. |

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

Name lookup stays cheap. The names of a module are one index, built from the
names that its files define. An edit inside a body changes no file's names,
so it invalidates no lookup.

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
so its capabilities, contract, and cost could only be assumed, and Truss has
no `assume`.

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

The Markdown files beside the modules of [`standard/`](standard) document
the library. This section gives the reasons for its scope and conventions.

Truss is batteries included: the standard library holds the modules that a
command-line tool or a network service needs, so most programs need no other
dependency. Every dependency is a target for a supply-chain attack, and the
standard library is the one package that every program already trusts.

The standard library holds the modules that most programs would otherwise
take from a package:

- code that needs the compiler or the operating system, such as
  cryptographic primitives, which need processor instructions
- types that packages share to interoperate, such as `Path` and
  `http::Request`
- implementations of published standards, such as JSON, TLS, and the
  cryptographic algorithms
- the protocols of a network service

A client for a product, such as `truss::postgres`, is an approved package
instead, owned by `truss` on the registry. A client follows the releases of
a product, not a published standard, and few programs need any one client.
An approved package is plain Truss, is granted capabilities as any
dependency is, and is held to the toolchain's review and release rules.

The standard library is part of the toolchain: it has no version of its own,
and it appears in no manifest and no lock file. A package instead names the
language version that it is written for, as in `truss = "1.4"`. That is both
the version that its files are read as and the minimum toolchain that builds
it. Packages written for different versions build together, as Rust's
editions allow.

The standard library never makes a breaking change. A module that must break
gets a successor beside it, named with `_v2`, which fixes the module without
removing it.

### Maps and sets

`Map` and `Set` iterate in insertion order. The order never varies from run
to run, so tests stay deterministic and their results can be cached.

**A `Map` resists hash flooding deterministically.** Keys that are chosen to
collide can turn each operation into a scan of the whole map. The usual
defense is a random hash key for each process. That is randomness that no
signature shows: it would change timing and allocation counts from run to
run, and make a test near its time limit flaky. Instead, a bucket that fills
up becomes a balanced tree, so the worst case is O(log n), which a `cost`
clause can promise. This is why a key is `Ordered` as well as `Hash`. Code
that must stay fast under attack gets random hashing through a capability,
as every source of randomness is a capability.

### Conventions

| Convention | Reason |
|---|---|
| Each module is one subject, one level below `standard`. | Code writes a name with its module, so the name of a type does not repeat the module: `json::Value`. A category above the module, as in Go's `encoding/json`, is not written at the use site, so it only adds something to remember. |
| Every method of a view type also exists on the owning type. | `mut names.sort()` works without `names[..]`. Truss converts an owning collection to its view only at a parameter, so the library declares the methods on both. |
| A method that works on any collection is a provided method of `Iterable`. | A user's collection gets the method by implementing `count` and `element`. |
| A collection method takes a pure callback. A method of `Option` or `Result` takes a callback that may use capabilities. | `map` and `sort_by` may later run their callback in parallel. `Option.map` calls its callback at most once, in place of an `if`. |
| A lookup that can miss lends an `Option`. | Nothing is copied, whatever the element type. |
| A capability declares only primitive operations. | A narrowing implementation or a fake has few methods to write, and every helper works with every implementation. |
| Every failure of the operating system is a `SystemError`. | Code that reads a file and sends it over a connection handles one error type. |
| Text in an embedded language is a tagged template, and a `processes::Command` is a program and a list of arguments. | Neither is a string that is passed to an interpreter, so neither allows an injection. |
| A write reports at most the number of bytes it was given, proven for every implementation. | `write_all` can find the bytes that remain. |
| `files::MemoryFiles` returns the error that the operating system returns for each misuse. | A test of error handling is only as good as the errors that the fake can produce. |
| `simulation::World` fakes every capability at once. | One provider must implement `Handles` for every handle, as the operating system does. |

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

**A release therefore never breaks the API of an earlier release of the same
name.** A breaking change is published under a new name with `_v2`, as Go
requires `/v2` for the second major version of a module. Where compatibility
is left to the care of each author, breaking changes are routine in releases
that claim to be compatible. So the registry checks compatibility from the
signatures and numbers each release itself, and a version number is never
wrong about a change. Elm's registry checks releases in the same way, from
types alone. A Truss signature holds more, so the check covers more.

**A build uses the newest version that any of its packages was checked with,
and nothing newer.** This is Go's minimal version selection. Selecting the
newest release that a range allows puts a release that was published an hour
ago into every build, which is how a compromised release reaches thousands
of machines before anyone has read it.

| Rule | Reason |
|---|---|
| There are no version ranges and no solver. | Selecting versions under ranges is NP-complete, and its answer changes as packages are published. The answer of minimal version selection depends only on the lock file, so it is the same on every machine, every day. |
| Two edits to a lock file merge by taking the higher version of each package. | A solver's lock file cannot be merged without solving again (*parallel agents*). |
| A version is written only in the lock file. | An LLM does not know which versions exist today, so no file that is written by hand holds one. |
| There are no 0.x versions. | A version that may break at any release cannot be the one version of its name in a build. |
| A release may change a function's result within its contract. | This is how a fix reaches its users. A guarantee that users are meant to rely on goes in an `ensures`. |

### The registry

Rules: [The registry](PACKAGES.md#the-registry).

| Rule | Reason |
|---|---|
| A package is published as its source. | The code that a reviewer reads in the registry is the code that compiles. |
| The registry keeps an append-only public log of the hash of every version, as Go's checksum database does. | The registry cannot give two users different code under one version. |
| The registry signs the proofs and test results that it computed for a release. | Proving a whole dependency tree on a machine that starts with nothing, such as an agent's new container, is the cost that GOALS.md sets out to remove. Each signed result is a function of its key, so a registry that signed a false result is caught by anyone who recomputes it. |
| A new toolchain re-proves the registry, as far as the toolchain changed the proofs. | A toolchain that fails a proof of an approved package that the previous toolchain passed is not released. |
| A yanked release, one that is marked as not to use, still builds. | If yanking broke builds, one compromised account could stop every project that depends on the package. |

## Incremental builds

GOALS.md asks that building, testing, and proving cost O(change), not
O(project). Text files stay the source of truth: programmers and tools edit
ordinary files. The build caches its results per definition, and the rules
of the language keep the dependencies of each result few.

A definition's identity is its kind, its structure, the names it resolves
to, the names of its local variables, the values of its literals, and the
order of its clauses within each kind. An edit that changes none of these
changes no definition.

| Edit | Invalidates | Reason |
|---|---|---|
| Reformat a file, or move a definition within its file or to another file of its module | Nothing | Identity excludes the file, the position in the file, the surrounding definitions, and the layout. |
| Edit a body, such as replacing a `todo` | The check, the proof, and the code of that body. No caller is re-checked or re-proven. | A definition names its dependencies by module path and name, never by content, and callers depend on the signature alone. |
| Strengthen an `ensures` | The proofs of callers. No caller is type-checked. | A signature has two parts: the interface, which the types of callers depend on, and the contract, which only the proofs of callers depend on. |
| Change the default of a parameter | The proofs and tests of the callers that omit the argument, and the code of the callee alone | The interface records only that the parameter has a default, and the callee applies it. |
| Reorder the fields of a record | Nothing, unless the type derives `Ordered` | The compiler chooses the layout, and a record with more than one field is constructed with labeled arguments. |
| Add a `derives` | Nothing that exists | Each derived implementation is a definition of its own, generated from the trait, the fields of the type, and the compiler's deriving rule, and never stored. A changed field therefore re-checks, of the derived code, only the code that compares, hashes, or orders the type. |
| Add, remove, or rename a definition | The name lookups with its scope and name | A definition depends on lookups keyed by scope and name, such as "the members of `List` named `length`", including the lookups that found nothing. Each lookup searches few places: a method lives with its type, an `impl` with its trait or a type it names, and an unqualified constant comes only from the same module. |
| Rename or move a definition | The type checks of its users, which are cheap. Their proofs, test results, and compiled code are cache hits. | Proofs, test results, and compiled code are keyed by content, not by name. |
| Rename a local variable | One body | Local names are part of identity, because diagnostics and `echo` output show them, and a cached result would show the old name. |
| Change the spelling of a literal, such as `0xFF` to `255` | Nothing | Identity holds the value of the literal. The file keeps the spelling, so `truss fmt` can print it back. |
| Reorder clauses | Nothing between kinds of clause. The definition, within one kind. | Each `requires` may rely on the `requires` before it. |
| Add a line at the top of a file | Nothing | A panic, an `echo`, a failed `assert`, and debug information record a position relative to their definition. A table built at the end of the build converts each position to a file and a line. |
| Upgrade a dependency | The dependents of the dependency's diff | A path holds no version, so a new version of a package is an edit to code that the project does not own, and is tracked as any edit is. |
| Install a new compiler | The results of the stages that changed | Each stage is versioned separately: the parser, the type checker, the prover with its pinned solver, code generation, and each deriving rule. A release that changes code generation leaves every proof valid. |

A development build inlines only from the standard library and from registry
packages. Inlining makes the code of a caller depend on the body of its
callee. The bodies of the standard library and of registry packages change
only with a new toolchain or a new lock file, so inlining them never widens
a rebuild during editing. A release build inlines across everything.

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
| `into()` | Rust infers the target of `into()` from context, which is a common source of inference failures. A conversion names its target, as in `Int64.from(count)`. |
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
