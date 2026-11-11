# Truss Syntax

This document describes how Truss code is written. For what the code means
(capabilities, costs, memory, failure, and so on), see [DESIGN.md](DESIGN.md).
It describes the language, not a compiler: what stage0 builds of it is in
the documents of stage0's stages, which
[IMPLEMENTATION.md](IMPLEMENTATION.md) lists.

## Guiding ideas

- **Look familiar.** Truss borrows from Rust, Swift, Go, and Kotlin, which
  people and LLMs already know well.
- **One way to write each thing.** A single formatter, `truss fmt`, decides all
  layout.
- **Every top-level definition parses on its own.** There are no user-defined
  operators, no custom precedence, and no macros that change how later code is
  read.
- **Signatures carry the important facts.** Types, capabilities, costs, and
  contracts all live in the signature, so reviewers can focus there.
- **Simple to parse.** The grammar avoids anything that needs type information
  or long lookahead to parse.

## Source files

- Source files are UTF-8. There is no other encoding and no setting for one.
- Each language version names one Unicode version, and the rules here that
  depend on Unicode, such as which characters are invisible, follow that
  version. It changes only with a new language version. A string can still
  hold a character from a later Unicode version.
- A byte order mark is allowed only as the very first character, and is
  ignored.
- Tabs count as whitespace, like spaces.
- A carriage return followed by a line feed counts as a single line break. A
  carriage return on its own is a compile error.
- `truss fmt` removes the byte order mark, indents with spaces, and writes
  line feeds only.
- Invisible characters that can change how code looks are a compile error
  anywhere in a file, including inside strings:
  - the bidirectional controls: U+061C, U+200E, U+200F, U+202A to U+202E,
    and U+2066 to U+2069
  - control characters (U+0000 to U+001F, U+007F, and U+0080 to U+009F),
    except tab, line feed, and a carriage return before a line feed
  - the rest of Unicode's default-ignorable characters, such as zero-width
    space, word joiner, soft hyphen, and the tag characters U+E0000 to
    U+E007F

  The zero-width joiner (U+200D), the zero-width non-joiner (U+200C), and the
  variation selectors are allowed, because emoji and some scripts need them
  in visible text. An ordinary string that needs any of the others writes it
  as an escape, such as `\u{2068}`. A raw string cannot contain them.

## Names

- Types, constructors, traits, and capabilities use `UpperCamelCase`. Values,
  constants, functions, and fields use `lower_snake_case`. The parser relies
  on this: in a pattern, `Circle` is a constructor and `radius` binds a new
  variable, unless a constant named `radius` is in scope.
- A name that starts with an uppercase letter is `UpperCamelCase` and cannot
  contain `_`. Any other name is `lower_snake_case`: it has no uppercase
  letters, and `_` appears only singly, between parts. Names cannot start or
  end with `_`. `_` on its own is the wildcard pattern.
- Names use only ASCII: a letter from `a` to `z` or `A` to `Z`, then letters,
  digits, and `_`. A letter from another script, such as `é` in `café`, is
  an error. Text in any language goes in strings, including test names, as in
  `test "café counts accents"`. See [DESIGN.md](DESIGN.md#naming).
- By convention, names are made of whole words: `items`, not `xs`; `config`,
  not `cfg`; `length`, not `len`. Single letters are kept for loop indices
  such as `i` and `j`. This applies to generic parameters too: `[Element]` and
  `[Key, Value]`, not `[T]` and `[K, V]`. The compiler does not enforce this.
  The standard library and style guides set the example.
- No name can hide another name in scope: not a prelude name, not a
  definition in the same file, and not a variable from an enclosing scope.
  `let name = name.trim()` is an error; write
  `let trimmed_name = name.trim()`.
- Module names live apart from other names, because they are only ever
  written before `::`. A variable can be called `url` even in a file that
  imports the `url` module.

## Keywords

These keywords are reserved everywhere and cannot be used as names:

`any` `assert` `break` `capability` `concurrent` `continue` `cost`
`decreases` `derives` `echo` `else` `ensures` `exists` `false` `fn` `for`
`forall` `if` `impl` `in` `indirect` `internal` `is` `invariant` `law`
`lends` `let` `match` `mut` `opaque` `own` `parallel` `proof` `provide`
`public` `requires` `return` `self` `Self` `test` `theorem` `todo` `trait`
`true` `type` `unreachable` `use` `uses` `var` `while` `with` `yield`
`yields`

A few words have a special meaning in one position only, and are ordinary
names everywhere else, because they are common names for variables and
fields. They are not keywords: the lexer reads them as names, and the parser
or name resolution gives them their meaning where they appear:

| Words | Where they mean something special |
|---|---|
| `amortized`, `time`, `allocations`, `allocated_bytes`, `calls`, `O`, `finite`, `potential` | In the fixed positions of a `cost` clause: `cost [amortized] resource bound` and `cost potential expression` |
| `time(...)`, `calls(...)` | Called inside a `cost` bound, where they are the cost functions |
| `log(...)`, `power(...)` | Called inside a `cost` bound or any other specification, where they are the functions on exact integers |
| `result` | Inside `ensures` and `cost`, where it names the return value |
| `old` | Inside specifications: `requires`, `ensures`, invariants, laws, `decreases`, `cost`, and proofs |
| `identical` | Inside specifications: `identical(a, b)`, whether two values of one type are the same value |
| `yielded`, `finished` | Inside the `ensures` of a lending or yielding method, and `yielded` in the `invariant` of a `for` loop, where they name what was handed out so far and whether the method ran to its end |

A parameter cannot be named `result`, and a function cannot be named `old`,
because inside specifications those names mean the return value and a value as
it was when the function was called. Other names are unaffected: in
`fn wait(time: Duration) cost time O(time.seconds())`, the second `time` is
the resource and the third is the parameter. A function named `log` or `power`
can be defined and called anywhere except inside a `cost` bound.

These are reserved for possible later use, so they cannot be used as names
either:

`as` `async` `await` `const` `defer` `extern` `loop` `macro` `static`
`unsafe` `where`

Reserving them now means adding one later breaks no code. It also lets the
compiler give a clear error when code borrowed from another language uses one,
such as "Truss has no `loop`; write `while true`".

## Line breaks

A line break ends a statement, with no semicolons. It does so exactly when
the line before can end a statement and the next line can begin one:

1. Inside `(` and `[`, line breaks are ignored. Inside `{`, they count again,
   so a block inside a call's arguments works as usual.
2. Elsewhere, a line break ends the statement only if both of these hold:
   - The line ends with a token that can end a statement: a name, `_`, a
     literal, `)`, `]`, `}`, `?`, `true`, `false`, `self`, `Self`, `todo`,
     `unreachable`, `break`, `continue`, or `return`.
   - The next line starts with a token that can begin a statement. A line
     that starts with anything else continues the one before: `.`, `else`,
     `with`, `is`, `in`, `|`, `=>`, `->`, `yields`, `lends`, a clause keyword
     (`uses`, `requires`, `ensures`, `cost`, `invariant`, `decreases`,
     `derives`), a binary operator that cannot begin an expression
     (`+ * / % == != < <= > >= & ^ << >> && || ==> .. ..=`), `=` or a compound
     assignment, or a closing `)`, `]`, or `}`.
3. The `{` that opens a body may start the next line.

[GRAMMAR.md](GRAMMAR.md#line-breaks) lists exactly which tokens can begin a
statement.

So all of these continue onto the next line:

```truss
let active_names = users
  .filter(fn(user) { user.is_active })
  .map(fn(user) { user.name.copy() })

let total = subtotal
  + shipping
  + tax
```

A line that starts with `-`, `!`, `~`, `(`, `[`, or `{` begins a new
statement, because each of those can begin an expression. Such a statement
is almost always an unused value, which is a compile error with a fix that
moves the operator to the end of the line before:

```truss
let balance = deposits
  - withdrawals
```

The lexer applies these rules on its own. `truss fmt` puts line breaks only
where they continue the statement.

## Syntax from other languages

Code written from habit in another language gets a specific error with an
exact fix, never a generic "unexpected token". These sequences are rejected
rather than read as something else:

| Written | Error and fix |
|---|---|
| `// ...`, `/* ... */`, `# ...` | Truss has no comments. The fix removes the comment, and the message says where its content belongs: a name, a contract, or a test. |
| `;` | Statements end at a newline. The fix removes it. |
| `A => 1,` in a `match` | Arms are separated by line breaks. The fix removes the comma. |
| `'a'` | Truss has no character literal. The fix writes `Character"a"`. |
| `` ` ``, `@` | Not used in Truss. |
| `++`, `--` | No increment or decrement. The fix writes `i += 1` or `i -= 1`. `--x` is rejected too; write `-(-x)`. |
| `===`, `!==` | The fix writes `==` or `!=`. |
| `x ? a : b` | No conditional operator. The fix writes `if x { a } else { b }`. |
| `let mut x` | The fix writes `var x`. |
| `&x`, `&mut x` | The fix writes `x` or `mut x`. |
| `\|x\| x + 1` | The fix writes `fn(x) { x + 1 }`. |
| `Point { x: 1.0, y: 2.0 }` | Records are built with parentheses. The fix writes `Point(x: 1.0, y: 2.0)`. |
| `copy(original, backup)` | Arguments after the first need a label. The fix writes `copy(original, destination: backup)`. |
| `parse::<Int64>(text)` | The fix writes `parse[Int64](text)`. |
| `items.map { it.name }`, `{ $0.name }` | The fix writes `items.map(fn(item) { item.name })`. |
| `x as Int64` | The fix writes `Int64.from(x)`, or `Int64.try_from(x)` when the conversion can lose information. |
| `null`, `nil` | The fix suggests `None`. |
| `elif` | The fix writes `else if`. |
| `fn name(...) -> Type;` | The fix removes the `;`. |

Each fix is an exact text replacement that tools and agents can apply
directly.

## No comments

Truss has no comment syntax. Names, signatures, contracts, invariants, laws,
costs, and tests carry what comments would otherwise say. See
[DESIGN.md](DESIGN.md#no-comments) for the reasons. The code examples in this
document are explained in the text around them.

Some examples show only a function's signature, with no body, to focus on the
signature. In real code, every function has a body, except a method declared
in a trait or a capability. A function that is not written yet has the body
`{ todo }`.

## Built-in types

| Type | Meaning |
|---|---|
| `Int8`, `Int16`, `Int32`, `Int64` | Signed integers |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | Unsigned integers |
| `USize` | Sizes, lengths, and indices |
| `ISize` | Offsets and differences between positions |
| `Float32`, `Float64` | IEEE 754 floating point |
| `Bool`, `String` | The usual meanings |
| `Array[Element, count]` | Exactly `count` elements, stored in place with no heap allocation. See [Arrays](#arrays). |
| `Character` | A Unicode scalar value: any code point except the surrogates |
| `Unit` | The result of a function that returns nothing. Its only value is also written `Unit`. |
| `Never` | The result type of a function that never returns |

Integer types never convert implicitly. Use `Int64.from(size)` for conversions
that cannot lose information, and `UInt32.try_from(size)` (which returns a
`Result`) for ones that can.

### Number literals

| Literal | Meaning |
|---|---|
| `42`, `1_000_000` | Decimal |
| `0xFF`, `0xdead_beef` | Hexadecimal |
| `0b1010_0001` | Binary |
| `0o755` | Octal |
| `0.5`, `6.02e23`, `1.0e-9` | Floating point |

- `_` may appear between digits to group them.
- A decimal literal does not start with `0` unless it is `0` or a float
  such as `0.5`. In C and Go, `0755` is octal, so Truss rejects it rather than
  silently reading 755: write `0o755`, or `755` if decimal was meant. Digits
  after the `.` and in an exponent may start with zeros, as in `1.0e-09`.
- A float has digits on both sides of the `.`: `0.5`, not `.5` or `1.`. This
  keeps `1..2` a range and `1.max(2)` a method call. The exponent is optional.
- The prefixes `0x`, `0b`, and `0o` and the exponent `e` are lowercase. Hex
  digits may be either case.
- Literals have no type suffixes. A literal takes its type from its context,
  as in `let small: UInt8 = 3`. When nothing decides it, an integer literal is
  an `Int64` and a float literal is a `Float64`, so `var best = 0` makes an
  `Int64`.
- A literal operand of an arithmetic operator, a comparison, or a range takes
  the type of the other operand when it can be that type, as Go's untyped
  constants do. So in `count + 1` with a `UInt8` count, the `1` is a `UInt8`,
  and in `index == 0` with a `USize` index, the `0` is a `USize`. In
  `duration * 2`, a `Duration` is not an integer type, so the `2` is an
  `Int64`. A literal shift amount, as in `flags << 3`, is a `USize`.
- An integer literal is never a float: `let ratio: Float64 = 1` is an error.
  Write `1.0`.
- A literal that does not fit its type is a compile error.
- `-` is an operator, not part of the literal. A negated literal is checked
  after the negation, so `-128` fits an `Int8`.

## Constants

A constant is a `let` at the top level. A constant that belongs to a type is
written under the type's name, like a method:

```truss
public let pi: Float64 = 3.141592653589793

public let UInt8.maximum: UInt8 = 255
public let Instant.epoch: Instant = Instant(nanoseconds: 0)
public let seconds_per_day: Int64 = 24 * 60 * 60

fn circle_area(radius: Float64) -> Float64 {
  pi * radius * radius
}
```

- A constant's type is always written out.
- Constants are values, so their names are `lower_snake_case`, like any other
  value. `UInt8.maximum` has no parentheses, because it is a value, not a call.
- The value is a *constant expression*: literals, arithmetic on numbers, other
  constants, and records, variants, lists, maps, and strings built from
  constant parts. It cannot call functions. The compiler works it out when the
  code is compiled. Calls to pure functions may be allowed later. Constants
  can appear in types, so for now their values never wait on running code.
- A constant lives in the program's static memory and is a read-only
  place, like a variable that can never change. Reading it or taking a view
  of it costs nothing. Where an owned value is needed, such as a `var`, an
  `own` argument, or a record field, write `.copy()`, as for a variable:
  `var scores = starting_scores.copy()`. A type that copies implicitly, such
  as an integer, needs no `.copy()`. A constant can never be marked `own` or
  `mut`.
- There is no `var` at the top level, so there are no mutable globals.
- A constant can be used as a pattern, written as it is anywhere else. See
  [Patterns](#patterns).

## Types

All types are declared with `type`. A record has named fields, listed in
parentheses after its name. A sum type has one or more variants, and each
variant has fields of its own or none.

```truss
type Point(x: Float64, y: Float64)

type Shape =
  | Circle(center: Point, radius: Float64)
  | Rectangle(corner: Point, opposite_corner: Point)
  | Empty

type Option[Value] =
  | Some(value: Value)
  | None

type Pair[First, Second](first: First, second: Second)

type DiscardLog()

type Bit = Zero | One
```

The `|` before the first variant is optional. `truss fmt` writes a short sum
type on one line without it, as for `Bit`, and a longer one with each variant
on its own line, starting with `|`, as for `Shape`.

Values are built like this:

```truss
let origin = Point(x: 0.0, y: 0.0)
let unit_circle = Shape.Circle(center: origin, radius: 1.0)
let found = Some(3)
let quiet = DiscardLog()
```

- Fields are declared exactly like a function's parameters, and a value is
  built the same way a function is called. See
  [Calls and arguments](#calls-and-arguments).
- A field can have a default, as a parameter can. A field with a default can be
  left out when the value is built:

  ```truss
  public type Request(
    method: Method,
    path: String,
    headers: Map[String, String] = [:],
  )

  let request = Request(method: Method.Get, path)
  ```

- A record with no fields is declared `type DiscardLog()` and built as
  `DiscardLog()`.
- Long field lists can span several lines, since line breaks inside `(` are
  ignored.

In expressions, a variant is written under its type, as in `Shape.Circle` or
`Shape.Empty`. From another module it also needs the module, as in
`geometry::Shape.Circle`. The prelude's variants `Some`, `None`, `Ok`, and
`Err` are written bare everywhere.

Generic parameters use square brackets. Angle brackets would clash with `<` and
`>` as comparison operators, which forces awkward workarounds in other
languages.

A generic parameter can also be a value of type `USize`, written in
`lower_snake_case` with its type: `[Element, count: USize]`. Its value is
known when the code is compiled. It cannot be computed in a type, so
`Array[Float64, rows * columns]` is not allowed.

### Recursive types

A type that contains itself marks the variant where it does so `indirect`:

```truss
type Expression =
  | Number(value: Int64)
  | indirect Sum(left: Expression, right: Expression)
  | Call(function: String, arguments: List[Expression])
```

- An `indirect` variant keeps its fields on the heap, all in one
  allocation. Building one, as in `Expression.Sum(left, right)`, costs one
  allocation, and `cost` clauses count it. Changing its fields in place, or
  moving them out with `own`, allocates nothing.
- Patterns and construction look the same as for any variant.
- Every cycle of types that contain each other must pass through an
  `indirect` variant, unless it passes through a collection. `Call` needs no
  mark, because a `List` already keeps its elements on the heap. A missing
  mark is a compile error, with a fix that adds it.
- A record cannot contain itself, even through an `Option`, because there is
  no variant to mark. Use a sum type with an `indirect` variant, or a
  collection.
- A variant that is not recursive may be marked `indirect` too, so that one
  large, rarely used variant does not make every value of the type large.
- A type cannot occur in the input of a function type that has a `time`
  clause in its own fields, directly or through the types that it contains:
  `type Knot(run: (fn(Knot) -> Bool cost time finite))` is a compile error.
  A function stored in a `Knot` could be called on that `Knot` and call
  itself through it, so it might not terminate. A function type without a
  `time` clause may take the type, as in `type Button(label: String,
  on_click: fn(Button))`. The output of a function type may be the type, as
  in `type Lazy(next: (fn() -> Lazy cost time finite))`.

### Single-field records

To give a plain value its own type, wrap it in a record with one field:

```truss
type UserId(number: UInt64)
type Meters(meters: Float64)

let user = UserId(42)
let distance = Meters(12.5)
let raw = user.number
```

- `UserId` is a different type from `UInt64` and from any other wrapper, so
  they cannot be mixed up.
- The record does not get the field's methods or operators. `distance +
  distance` does not compile unless `Meters` implements `Add[Meters]`.
- A record with one field has exactly the same representation as the field, so
  it costs nothing at run time.
- Truss has no type aliases, and there is no separate syntax for wrapper types.

### Grouping values

Truss has no tuples. Values that belong together go in a record, so each one
has a name. The standard library provides records for the common cases:

```truss
public type Indexed[Element](index: USize, element: Element)
public type Entry[Key, Value](key: Key, value: Value)
public type Pair[First, Second](first: First, second: Second)
```

`enumerate` produces `Indexed` values, maps hold `Entry` values, and `zip`
produces `Pair` values. They are in `standard::core` and `standard::map`,
not in the prelude: a pattern never names them, and a signature that does
writes `core::Pair`. A function that returns several values declares a
record for its result:

```truss
type Extremes(lowest: Int64, highest: Int64)

fn extremes(scores: Slice[Int64]) -> Option[Extremes]
```

### Patterns

A pattern is written the way the value is built. A variant pattern names the
variant, without its type or module. The variant is looked up in the type of
the value being matched, just as a method is looked up in the type of its
receiver. A record pattern is written without the type name, because a record
type has only one shape:

```truss
for (index, element) in scores.enumerate() { todo }

match items.split_first() {
  Some((first, rest)) => todo
  None => todo
}

match shape {
  Circle(radius, ..) => todo
  Rectangle(corner, opposite_corner) => todo
  Empty => todo
}
```

- A bare name that matches a field binds that field to a variable of the same
  name, so `(index, element)` binds both fields of an `Indexed`, and
  `Circle(radius, ..)` binds `radius`.
- `field: pattern` matches one field against a pattern:
  `(index, element: score)` binds the field `element` to a variable named
  `score`.
- In a record or variant with exactly one field, a bare pattern matches that
  field whatever it is called, so `Some(count)` binds the value inside the
  `Some` to `count`.
- Fields can be written in any order. `..` skips the remaining fields.
- Nested patterns work the same way: in `Some(Circle(..))`, `Circle` is looked
  up in the type inside the `Option`.
- Parentheses in a pattern always hold fields, so patterns have no grouping
  parentheses.

Patterns can also match values directly:

```truss
match status_code {
  http::ok => todo
  301 | 302 | 307 => todo
  not_modified => todo
  500..=599 => todo
  code if code >= 400 => todo
  _ => todo
}
```

| Pattern | Matches |
|---|---|
| `200`, `-1`, `true`, `"GET"`, `Character"a"`, `UInt8"\n"` | A value equal to the literal |
| `http::ok`, `Status.teapot`, `not_modified` | A value equal to the constant |
| `500..=599`, `Character"a"..=Character"z"`, `0..=max_port` | A value in the range, for integers and characters |
| `301 \| 302 \| 307`, `Some(Low \| Normal)` | A value matching any of the alternatives |
| `_` | Anything, without binding it |
| `code` | Anything, binding it to `code` |

- A bare name that names a constant in scope means that constant, wherever it
  appears in a pattern. Any other bare name binds a new variable. Constants
  from other modules and constants under a type are qualified, as everywhere
  else: `http::ok`, `Status.teapot`.
- A constant in a pattern must have a type with structural equality: built
  in, as for integers, strings, and `Bool`, or derived from fields that all
  have it, so that matching it and comparing it with `==` agree. A type with
  a float field derives a lawful `Equal` that is not structural, since
  `-0.0 == 0.0`. See [DESIGN.md](DESIGN.md#equality-ordering-and-deriving).
- The ends of a range are literals or constants, as in `0..=max_port` or
  `http::informational_first..=http::informational_last`. A name there must
  be a constant. Both ends are needed.
- Float literals cannot be patterns. A float `==` treats `-0.0` and `0.0` as
  equal, so a pattern such as `0.0` would match both without saying so. Use a
  guard: `value if value == 0.0`.
- Every alternative of an or-pattern must bind the same names, with the same
  types.
- A *guard* is written `if condition` after the pattern. The arm is taken only
  when the pattern matches and the condition is true.
- Each arm of a `match` goes on its own line, with no comma between arms. An
  arm's body can continue on the next line after `=>`, or be a block.
- An arm's body is a statement, like a line of a block, so it can be an
  assignment, a `yield`, an `assert`, or a loop: `Click => clicks += 1`.
  When the `match` is used as a value, an arm whose body is not an expression
  has type `Unit`.
- `match` must cover every case. An arm with a guard never counts toward
  covering its pattern. When the guards cover everything, end with
  `_ => unreachable`, which the prover checks.
- An arm that can never be reached, because earlier arms already match
  everything it matches, is a compile error.
- A pattern in `let`, in `for`, or in a lambda's parameters must match every
  value of its type, as `(first, rest)` does for a pair. A pattern that can
  fail, such as `Some(user)`, needs a `match`, an `is` test, or
  `let ... else`, described next.

These rules keep a misspelled constant from passing silently. A misspelled
constant binds a new variable that matches everything, which makes the arms
after it unreachable, or leaves the binding unused. Either is a compile error.

### Matching several values

A `match` can take several values, separated by commas. Each arm then has one
pattern per value, in the same order:

```truss
match state, event {
  Idle, Start => todo
  Running, Stop => todo
  Idle | Paused, Tick if elapsed > limit => todo
  _, Reset => todo
}
```

- No tuple is made. The values are matched together, as if by nested
  `match`es.
- Every combination must be covered, and every arm must be reachable, across
  all the values together.

### Testing a pattern with `is`

`value is pattern` is `true` when the value matches the pattern:

```truss
if response is Ok(body) && body.length() > 0 {
  render(body)
}

while queue.pop() is Some(task) {
  run(task)
}

let is_quiet = level is Low | Normal
```

- `is` binds like a comparison, so it combines with `&&` and `||`.
- The pattern can be anything a `match` arm can have.
- The names a pattern binds can be used only where the test is known to be
  true: in the rest of an `&&` chain, in the block of the `if` or `while`, and
  in a `match` arm whose guard contains the test. They cannot be used after
  `||` or in an `else`.
- To choose among several patterns, use `match`, which checks that every case
  is covered.

### `let ... else`

A `let` whose pattern can fail has an `else` block, which runs when the
pattern does not match:

```truss
let Some(user) = find_user(id) else {
  return Err(LoginError.UnknownUser(id))
}
greet(user)
```

- The names the pattern binds can be used in the rest of the enclosing block.
- The `else` block must leave the block: it ends with `return`, `break`,
  `continue`, or `unreachable`, or has type `Never`.
- `var` works the same way, binding mutable names.
- The expression before `else` cannot end with `}`, so that the `else` cannot
  be mistaken for part of it. Put such an expression in parentheses:
  `let Some(choice) = (if ready { first } else { second }) else { ... }`.

### Updating records

A `with` expression makes a record with some fields changed:

```truss
let moved = origin with (x: 1.0)
let production = own config with (server.port: 443, log_level: LogLevel.Warning)
let retry = request.copy() with (attempt: request.attempt + 1)
```

It is shorthand for copying the base into a new variable, assigning to its
fields, and returning it:

```truss
{
  var updated = own config
  updated.server.port = 443
  updated.log_level = LogLevel.Warning
  updated
}
```

- The base is handed over the same way as an `own` argument: mark a place with
  `own` to give it up, or call `copy()` to keep it. Types that copy implicitly
  (see [DESIGN.md](DESIGN.md#memory)) need neither, as with `origin` above.
- A field can be a path, such as `server.port`, to update a nested field.
- `origin with (x)` uses a local variable named `x`, as building a record
  does.
- `with` works on records. For a sum type, `match` on the variant first.
- Only fields visible at that point can be updated.
- `with` applies to the expression directly before it. To keep chaining, use
  parentheses: `(own config with (debug: true)).validate()`.

### Invariants

A type can state an `invariant`: a condition every value of the type
satisfies.

```truss
public type DateRange(start: Date, end: Date)
  invariant start <= end

public type SortedList[Element: Ordered](items: List[Element])
  invariant is_sorted(items)

public type Port(number: UInt16)
  invariant number != 0

public type Interval =
  | Closed(low: Int64, high: Int64)
  | Unbounded
  invariant match self {
    Closed(low, high) => low <= high
    Unbounded => true
  }

public type Tree =
  | Leaf
  | indirect Node(left: Tree, value: Int64, right: Tree)
  invariant is_balanced(self)
```

- An invariant belongs to the whole type. Clauses after the last variant,
  such as `invariant` and `derives`, always apply to the type, never to that
  variant.
- In an invariant, `self` names the value. A record's fields can also be
  used by name, as in `start <= end`.
- A condition on one variant is written with `match`, as for `Interval`, or
  by giving the variant a record that has its own invariant:
  `| Closed(range: ClosedRange)`.
- `invariant` may repeat. All of the conditions must hold.
- Functions called in an invariant must be pure and have a `time` clause.
- A private method that takes `mut self` may be called while `self` is in
  the middle of a change. Its `self` is not assumed to meet the invariant,
  and need not meet it when the method returns, so it states what it needs
  and what it leaves with `requires` and `ensures`:

  ```truss
  fn SortedList[Element: Ordered].sift_into_place(mut self, index: USize)
    requires index < self.items.length()
    requires is_sorted(self.items[..index])
    ensures is_sorted(self.items)
  {
    todo
  }
  ```

Invariants are proven at compile time, never checked at run time. When the
compiler cannot prove one, the usual fix is a constructor that checks or
establishes it:

```truss
fn DateRange.new(start: Date, end: Date) -> Option[DateRange]

impl TryFrom[UInt16] for Port {
  type Error = PortError
  fn try_from(value: own UInt16) -> Result[Port, PortError] { todo }
}

impl From[List[Element]] for SortedList[Element: Ordered] {
  fn from(value: own List[Element]) -> SortedList[Element] { todo }
}
```

`DateRange.new` returns `None` when `start` is after `end`, `Port.try_from`
returns an error for 0, and `SortedList.from` sorts its input.

## Functions and signatures

```truss
fn area(shape: Shape) -> Float64 {
  match shape {
    Circle(radius, ..) => math::pi * radius * radius
    Rectangle(corner, opposite_corner) =>
      (opposite_corner.x - corner.x) * (opposite_corner.y - corner.y)
    Empty => 0.0
  }
}
```

Parameter and return types are always written out. Inside function bodies,
types are inferred, one statement at a time: a variable's type comes from its
own `let` or `var` and never changes. When the statement alone cannot decide
it, as in `var names = []`, give the `let` a type:
`var names: List[String] = []`.

A function that returns nothing leaves out the return type, and its result is
`Unit`. The formatter removes a written `-> Unit`. A function that never
returns, such as one that always panics or runs a server forever, has the
return type `Never`.

### Calls and arguments

Parameter names are part of a function's API. Arguments after the first are
always named, either with a label or by passing a variable of the same name:

```truss
fn copy(source: Path, destination: Path)
  uses FileRead, FileWrite
fn connect(host: HostName, port: UInt16 = 443, secure: Bool = true) -> Result[Connection, NetworkError]
  uses NetworkClient

copy(original, destination: backup)
copy(source: original, destination: backup)
copy(source, destination)
let connection = connect(host, port: 8080)?
let root = sqrt(area)
```

1. `label: value` passes `value` to the parameter named `label`.
2. A bare name that matches a parameter's name passes that variable to that
   parameter. `copy(source, destination)` passes the variables `source` and
   `destination`. A mode keyword can come first, as in `mut destination`.
3. Any other first argument goes to the first parameter, as `original` and
   `area` do above. Any other later argument is a compile error, with a fix
   that adds the label.
4. Arguments are written in the order of the parameters.

A parameter can have a default, written after its type. A default follows the
same rules as a [constant](#constants): it is a constant expression, and it
cannot refer to other parameters. An argument for a parameter with a default
can be left out, as `port` and `secure` are in `connect(host)`.

Building a record or a variant follows the same rules, with two differences:

- Fields can be written in any order, because the order of a record's fields
  has no meaning. Their values are evaluated in the order written.
- Only a record or variant with exactly one field can take a bare value, as in
  `Some(3)`, `UserId(42)`, and `ConfigError.Malformed(error)`. With more than
  one field, every argument needs a label or a matching name, as in
  `Point(x: 0.0, y: 0.0)` or `Summary(count, best, average)`.

A call through a function value, such as `visit(item)` or
`compare(left, right)`, passes its arguments by position, because function
types have no parameter names.

### Explicit type arguments

Type arguments are usually inferred. When they cannot be, they are written in
square brackets after the function's name, as in a type:

```truss
let value = parse[Int64](text)?
let names = items.map[String](describe)
let builder = List[String].with_capacity(64)
```

- `parse[Int64]` is written the same way as indexing. Name resolution tells
  them apart: `parse` is a generic function, so `[Int64]` gives its type
  arguments. A local variable cannot be generic, so a variable followed by
  `[...]` is always an index. For a method, such as `items.map[String]`, the
  type of the receiver decides, as it does for every method call.
- For the same reason, whether an expression starts with a place (see
  [Parameter modes](#parameter-modes)) is known after name resolution, not
  from the text alone: `mut parse[Int64](text)` starts with a function, not a
  place.
- When the compiler reports an error in `f[X]`, it says which reading
  applied, such as "`parse` is a generic function, and `[Int64]` is its type
  argument" or "`scores` is a `List`, so `[...]` indexes it".

A signature can carry clauses between the return type and the body:

```truss
public fn binary_search[Element: Ordered](sorted: Slice[Element], target: Element) -> Option[USize]
  requires is_sorted(sorted)
  ensures match result {
    Some(index) => sorted[index] == target
    None => !contains(sorted, target)
  }
  cost time O(log(sorted.length()))
  cost allocations == 0
{
  todo
}
```

| Clause | Meaning |
|---|---|
| `uses Capability, ...` | The capabilities the function may use. Leaving it out means the function is pure. At most once. |
| `requires condition` | A precondition every caller must prove. May repeat. |
| `ensures condition` | A postcondition the function must prove. `result` names the return value. May repeat. |
| `decreases measure, ...` | Proves that recursion ends. See below. At most once. |
| `cost resource bound` | A proven cost bound. Optional. May repeat. |

Clauses of different kinds may be written in any order. The formatter groups
them in the order `uses`, `requires`, `ensures`, `decreases`, `cost`, but never
reorders clauses of the same kind. When a clause repeats, all of its
conditions must hold, and each one may rely on the ones before it:

```truss
fn bump(items: mut List[Int64], index: USize)
  requires index < items.length()
  requires items[index] < Int64.maximum
```

The second `requires` reads `items[index]`, which is in bounds because of
the first. Each `requires` may rely on the `requires` before it. Each
`ensures` may rely on every `requires` and on the `ensures` before it.
Repeated `invariant` clauses, on types and on loops, work the same way.

### Recursion

A recursive function that must terminate, because it has a `time` clause or
is used in a specification, needs to show that its recursion ends. Most
recursion needs nothing written:

```truss
fn depth(tree: Tree) -> USize
  cost time O(tree.size())
{
  match tree {
    Leaf => 0
    Node(left, right, ..) => 1 + depth(left).max(depth(right))
  }
}
```

`depth(left)` passes a field taken out of the parameter by a pattern, so the
compiler can see that the recursion ends. Other recursion states a
`decreases` clause:

```truss
fn search(sorted: Slice[Int64], target: Int64, low: USize, high: USize) -> Option[USize]
  requires high <= sorted.length()
  decreases high - low
  cost time O(log(high - low))
{
  todo
}

fn merge(first: Slice[Int64], second: Slice[Int64]) -> List[Int64]
  decreases first.length(), second.length()
  cost time O(first.length() + second.length())
{
  todo
}
```

- A measure is an integer expression, written in terms of the parameters,
  that must stay at or above zero. Every recursive call must make it
  smaller.
- A list of measures is compared in order: each call makes the first one
  smaller, or keeps it the same and makes the second one smaller, and so on.
- When functions call each other in a cycle, each one states a `decreases`
  clause, and every call between them must make it smaller.
- A function without a `time` clause may not terminate, so it needs no
  `decreases`.

### Cost clauses

A cost clause has the form `cost <resource> <bound>`.

| Resource | Allowed bounds |
|---|---|
| `time` | `O(expression)` or `finite` |
| `allocations` | `O(...)`, `<= expression`, `== expression` |
| `allocated_bytes` | `O(...)`, `<= expression`, `== expression` |
| `calls(target)` | `O(...)`, `<= expression`, `== expression` |

The target of `calls` is a function parameter (`calls(visit)`), a capability
method (`calls(FileRead.read)`), or a whole capability (`calls(FileRead)`).
`O(f)` means that the cost is at most `c * f + d` for every input, for some
constants `c` and `d` that the prover finds. So `O(rows * columns)` and
`O(text.length() + pattern.length())` mean exactly what they say, and small
inputs need no special case.

A bound is an expression that can use:

- the parameters, `self`, their fields, and pure methods with a `time` clause,
  such as `items.length()`
- `result`, for bounds that depend on what the function returns, as in
  `cost time O(text.length() + result.length())`
- `+`, `*`, and `/` and `-` where the result stays at or above zero, all on
  exact integers
- `log(n)`, which means the smallest integer at least log₂(n + 1), so
  `log(0)` is 0 and `log(1)` is 1
- `power(base, exponent)`, for bounds such as `O(power(2, items.length()))`
- `time(visit)`, a bound on the time of any one call to the function
  parameter `visit`, and `calls(...)` as above
- `time(Element.equal)`, a bound on the time of any one call to a method of
  a trait that bounds a type parameter

`time(visit)` cannot depend on what `visit` is called with, because a
function type's parameters have no names. If `visit` has the type
`(fn(Item) cost time O(1))`, `time(visit)` is a constant. If it has
`cost time finite`, `time(visit)` is a fixed bound that is not known. A
callback whose time grows with its argument is better described by a trait
whose method has a cost clause.

A generic function counts the methods of its bounds the same way:

```truss
fn Slice[Element: Equal].contains(self, item: Element) -> Bool
  cost time O(self.length() * time(Element.equal))
```

- **The term names a method of a bound.** In `time(Element.equal)`,
  `Element` is a type parameter of the definition, or `Self` in a trait,
  and `equal` is a method of a trait that bounds it. If the name has
  several versions, the term means the read-only one.
- **An operator counts as the method it calls.** `==` and `!=` spend
  `time(Element.equal)`, and `<`, `<=`, `>`, and `>=` spend
  `time(Element.compare)`.
- **At a call, the term has the value the type gives it.** For
  `List[Int64]`, `time(Int64.equal)` is a constant, because
  `impl Equal for Int64` promises `cost time O(1)`, so `contains` is
  `O(self.length())`. For `List[String]`, comparing two strings promises
  only `cost time finite`, so the term is a fixed bound that is not known,
  as it is for a function value.
- **A trait's provided method states its cost the same way,** as in
  `cost time O(time(Self.equal))`, and an `impl` that writes the method
  itself must keep that bound.

`log` and `power` are also specification functions. Outside a `cost` bound
they can be used in `requires`, `ensures`, invariants, `decreases`, and
proofs, with the same meaning:

```truss
fn digit_count(value: UInt64, base: UInt64) -> USize
  requires base >= 2
  ensures result <= log(value) + 1
```

A bound such as "at most 64 digits" cannot be proven step by step, and
`log(value) + 1` can. The prover knows `log` of a number exactly, and
knows that `log` of a value of an integer type is at most the type's
width. Outside a `cost` bound, a local or a definition of the file named
`log` or `power` takes precedence. Neither function can be called in code
that runs.

`time` counts abstract steps: each primitive operation and each call counts
as one. It never measures time on a machine.

#### Amortized costs

Some operations are cheap almost every time and occasionally expensive.
Pushing onto a full `List` copies every element into a larger buffer, but
over many pushes each one costs O(1) on average. Such a method promises an
*amortized* bound:

```truss
public opaque type List[Element](buffer: Buffer[Element], length: USize, capacity: USize)
  invariant length <= capacity
  cost potential growth_credit(length, capacity)

fn List[Element].push(mut self, item: own Element)
  cost amortized time O(1)
```

- A type can declare a `cost potential`: an integer expression over its
  fields that never goes below zero. Cheap operations raise it, and
  expensive ones use it up.
- `cost amortized time O(f)` promises that the method's actual cost, plus
  the change in the potential of the values it changes or returns, is
  within `O(f)`. `amortized` works with every resource that takes an `O(...)`
  bound.
- Amortized bounds add up. A function that pushes `count` times can promise
  `cost amortized time O(count)`. It can also promise a plain bound that
  includes the potential the list came in with, as in
  `cost time O(count + items.length())`.
- A value's potential belongs to that value alone. Values are never shared,
  so two parts of a program can never use up the same potential.
  `copy()` makes a new potential, and pays for it with its own cost.
- Truss has no bounds that hold only on average over random choices, such
  as a hash map's expected O(1). Cost clauses state bounds that hold for
  every input.

```truss
public fn load_configs(paths: List[Path]) -> Result[List[Config], ConfigError]
  uses FileRead
  cost calls(FileRead.read) == paths.length()
  cost time O(paths.length())
```

### Function types

A function type is written `fn(Input) -> Output`. As with definitions,
`-> Unit` is left out. A function type with clauses is written in
parentheses, with the clauses after its return type, as in a definition.
These parameters have the three forms:

```truss
fn sort_by(items: mut List[Item], compare: fn(Item, Item) -> Ordering)
fn record_all(items: List[Item], record: (fn(Item) uses Clock, Random))
fn serve(handle: (fn(Request) -> Response uses Database, Log cost time finite))
```

- A function type can have `uses` and `cost` clauses. Its parameters have no
  names, so a `cost` clause cannot mention them: `cost time O(1)`,
  `cost time finite`, and `cost allocations == 0` are allowed.
- A function type without `uses` is pure, the same as a function definition
  without `uses`. One without a `time` clause might not terminate.
- The parentheses end the clauses, so they never run into the next parameter
  or type argument, as in `List[(fn(Item) uses Clock, Random)]`.
- Clauses after a definition's return type always belong to the definition.
  A function that returns a function type with clauses puts it in
  parentheses: `fn make_counter() -> (fn(Int64) -> Int64 uses Clock)`.

The type of a function-typed parameter can say what the function passes it,
with a `requires`. Its inputs are then named, so the `requires` can mention
them, and it can also mention the parameters before it:

```truss
fn List[Element].map[Output](
  self,
  transform: (fn(element: Element) -> Output requires self.model().contains(element)),
) -> List[Output]
  ensures result.length() == self.length()
{
  todo
}

let picked = indices.map(fn(i) { values[i] })
```

- The function must meet the `requires` at every call it makes through
  `transform`, and a lambda passed for it may rely on it. Above, the lambda
  knows that `i` is one of `indices`, so `values[i]` is proven in bounds
  when every index in `indices` is.
- A named function passed for it must accept every argument the `requires`
  allows.
- The names are only for the `requires`. They are not labels, and calls
  through a function value still pass arguments by position. A function
  type names its inputs exactly when it has a `requires`.
- Only a parameter's own type can have a `requires`, at its top: not a
  field's type, a result type, or a type argument such as
  `List[(fn(index: USize) requires ...)]`.

A function that passes on whatever capabilities its callback needs declares a
capability parameter with `capability`:

```truss
public fn for_each[Item, capability Granted](
  items: List[Item],
  visit: (fn(Item) uses Granted cost time finite),
)
  uses Granted
  cost calls(visit) == items.length()
  cost time O(items.length() * time(visit))
```

`visit` promises to terminate, so `for_each` can promise a `time` bound.
`time(visit)` stands for the time one call to `visit` takes.

A function-typed parameter can be called but not kept, so it accepts lambdas
that capture local variables. To store the function, declare the parameter
`own`. It then accepts only functions that capture nothing, such as named
functions:

```truss
fn List[Element].sort_by(mut self, compare: fn(Element, Element) -> Ordering)
fn Router.add(mut self, route: String, handler: own fn(Request) -> Response)
```

`mut router.add("/users", handler: list_users)` works. Passing a lambda that
captures a local variable to `add` is a compile error.

### Parameter modes

```truss
fn total(scores: List[Int64]) -> Int64
fn sort[Element: Ordered](items: mut Slice[Element])
fn push[Element](items: mut List[Element], item: own Element)
```

`total` only reads `scores`, which is the default. `sort` may modify the
caller's value. `push` takes ownership of `item`.

| Call | Meaning |
|---|---|
| `sort(mut scores)` | `scores` may change. |
| `push(mut names, item: own name)` | `name` is used up and cannot be used afterward. |
| `push(mut names, item: name.copy())` | `name` is kept, and `push` gets a copy. |
| `push(mut names, item: "Alice")` | A temporary value is never marked. |

A *place* is a variable, `self`, or a constant, followed by any number of
field accesses and indexes: `scores`, `config.servers`, `scores[0]`. A
constant is a read-only place. When a place is passed
to a `mut` or `own` parameter, the call site repeats the keyword. A reader can
see what happens to each existing value without looking up the signature.

A temporary value, such as a literal or the result of a call, is never marked.
Nothing else can see it, so it is always handed over as owned. Copies that
would allocate are never made implicitly; `copy()` makes one explicitly.

When the keyword comes before a longer expression, it marks the longest place
the expression starts with. The first method call after that place takes it
as its receiver, with the keyword's mode. Anything after that call works on
the call's result, which is a temporary:

| Expression | Marked place |
|---|---|
| `mut scores.sort()` | `scores` |
| `mut config.servers.sort()` | `config.servers`, so `config.clients` can still be used, for example by another parallel branch |
| `mut items[0].push(name)` | `items[0]` |
| `mut config.load_servers().sort()` | `config`, for `load_servers`. `sort` then works on the list it returns. |
| `own config with (debug: true)` | `config` |
| `sort(mut items[..middle])` | `items[..middle]`, since there is no method call |

An expression that does not start with a place cannot be marked:
`mut make_list().push(1)` is a compile error, with a fix that removes `mut`.

`own` can move a single field out of a record:

```truss
let name = own config.name
let port = config.port
config.name = "default"
save(own config)
```

After `own config.name`, the other fields of `config` can still be used, but
`config` as a whole cannot, until `config.name` is given a new value.

A place that is lent `mut` can be moved out of in the same way, as long as it
is given a new value before it goes back to its owner. This is how a function
takes what a `mut` place holds and leaves something else there:

```truss
fn Option[Value].take(mut self) -> Option[Value] {
  let taken = own self
  self = None
  taken
}
```

- **What can be moved out** is the whole place or a field of it. The place
  can be a `mut` parameter, `mut self`, the variable of a `mut` loop, a `mut`
  binding of a `match`, or a lambda's `mut` parameter.
- **It must be assigned again on every path** before the function returns,
  `return` and `?` included, before the loop's iteration or the `match` arm
  ends, and in a yielding method before each `yield`.
- **Until then the place cannot be used.** It cannot be read or passed to a
  call, so nothing sees it empty.

### Views

A read-only name can refer to the original value instead of a copy. This
covers read-only parameters, a `let` bound to a place, the variable of a
`for x in items` loop, and slices:

```truss
let middle = items[1..4]
let total = middle.sum()
mut items.push(9)
```

While such a name is still in use, the original cannot be changed or moved.
Here `push` is allowed because `middle` is not used after it. The compiler
checks this within each function, with no annotations.

- `Slice`, `StringSlice`, a cursor from a `self` method, and a lambda that
  reads local variables are views, and so is any type that holds one, in a
  field, a variant, an element, or a type argument. `Option[Slice[Int64]]`
  and the record that `split_at` returns are views.
- A view can be bound, kept in local records and collections, and passed as
  an argument. It cannot be put where a stored value is needed, such as an
  `own` parameter of function type, and putting it into a record or a list
  makes that record or list a view too.
- A function can return a view only of what its parameters view or of the
  parameters themselves, never of its own locals, as `items[1..4]`,
  `split_at`, `split_first`, and `text.trim()` do. The caller treats the
  result as viewing everything its read-only and view arguments view: after
  `let chosen = found.unwrap_or(default: backup[..])`, `backup` is frozen
  while `chosen` is in use.
- A function keeps only the views that it is given. To keep a view of an
  argument in a `mut` parameter or in `mut self`, take the argument as a
  `Slice`, a `StringSlice`, or a function. An argument that is only lent is
  never kept, so after `mut reader.read(mut buffer, limit: 64)` the reader
  does not view the buffer, and the next read can use the same buffer. A
  value cannot keep a view of its own part either:
  `self.recent = self.items[0..1]` is an error.
- A `var` can hold a view, such as a cursor over a list (see
  [Lending and yielding methods](#lending-and-yielding-methods)), as long as
  the view never leaves the function.
- `mut` access is never stored. It has a name only as a `mut` parameter, a
  `mut` loop's variable, or a lambda's `mut` parameter, and lasts only for
  that call, iteration, or `provide mut` block. Disjoint parts can be
  changed side by side, as in `sort(mut items[..middle])` and
  `sort(mut items[middle..])`.
- A view of a temporary cannot be bound with `let`. Bind the value first:
  `let loaded = load()`, then `let first = loaded.first()`.
- A `List` passed to a `Slice` parameter, or a `String` passed to a
  `StringSlice` parameter, becomes a view of it without copying. This is the
  only implicit conversion.

Where an owned value is needed (a `var`, an `own` parameter, a record field, a
collection element, or a return value), a place must be marked `own` or
copied. `let name = config.name` needs neither, but
`Person(name: config.name.copy())` needs the copy.

## Methods

A method is a function in a type's namespace, declared as `fn Type.name`:

```truss
fn List[Element].with_capacity(capacity: USize) -> List[Element]

fn List[Element].length(self) -> USize
  cost time O(1)

fn List[Element].push(mut self, item: own Element)

fn List[Element: Ordered].sort(mut self)
  cost time O(self.length() * log(self.length()))

fn List[Element].map[Output](self, transform: fn(Element) -> Output) -> List[Output]
```

```truss
var names: List[String] = []
mut names.push("Ada")
let count = names.length()
let same_count = List.length(names)
```

The last line makes the same call as the line before it, written in full.

- A function whose first parameter is `self` can be called with a dot. One
  without `self`, such as `List.with_capacity(64)`, is called through the type's name.
- `self` has no type annotation. Its type is the one named before the dot. It
  is written `self`, `mut self`, or `own self` to give its mode.
- The type's generic parameters go before the dot (`List[Element]`). The
  method's own go after its name (`map[Output]`). A bound before the dot, as in
  `List[Element: Ordered].sort`, means the method only exists for those
  element types.
- Each method is its own top-level definition. There is no block that groups a
  type's methods.
- Every call uses parentheses. `point.x` reads a field, and `names.length()`
  runs code.
- Methods can only be defined in the same package as their type.

### Versions by receiver mode

A method can have up to three versions that differ only in how they take
`self`:

```truss
fn List[Element: Copyable].filter(self, keep: fn(Element) -> Bool) -> List[Element]
fn List[Element].filter(own self, keep: fn(Element) -> Bool) -> List[Element]

fn List[Element].enumerate(self) yields Indexed[Element]
fn List[Element].enumerate(mut self) yields mut Indexed[Element]
```

The keyword at the call site picks the version, and no keyword picks the
read-only one. On a temporary value, the `own` version is used if there is one,
so `load_scores().filter(is_valid)` keeps the elements of the list it was
given instead of copying them into a new one. This is the only overloading
Truss allows.

A type's versions of one name need not all be its own methods. One can come
from a trait the type implements in its own package:

```truss
impl Iterable for Grid {
  type Element = Cell
  fn each(self) yields Cell { todo }
}

fn Grid.each(mut self) yields mut Cell { todo }
```

`Grid` has the `each(self)` that generic code written against `Iterable`
calls, and an `each(mut self)` of its own, which not every `Iterable` type
could offer. A call picks among all of a name's versions by its keyword, as
it does among a type's own.

### Lending and yielding methods

A method can give its caller parts of `self` instead of returning a value,
in one of two ways. A *lending* method gives out one part, exactly once. A
*yielding* method gives out any number of parts, one after another. The
signature says which, with `lends` or `yields` in place of a return type, and
both use `yield` in their bodies.

A lending method gives the caller access to one part, and then continues:

```truss
fn Grid.cell(self, position: Position) lends Cell {
  yield self.cells[position.row * self.width + position.column]
}

fn Grid.cell(mut self, position: Position) lends mut Cell {
  yield mut self.cells[position.row * self.width + position.column]
}

let current = grid.cell(position).state
mut grid.cell(position).visit()
```

- `lends Cell` lends read-only access, and `lends mut Cell` lends `mut`
  access. A method can have a version for each receiver mode, as other
  methods can.
- **The part is lent for the rest of the caller's statement.** Then the
  method always continues after its `yield`, even if the statement leaves
  early with `?` or `return`. So a type can update what depends on the part,
  such as a cached total, after the caller changes it.
- **For that long, `grid` is lent whole.** The statement cannot use `grid`
  again when the part is lent `mut`, and cannot change it when the part is
  lent read-only.
- **The mark is on the place the part is lent from.** In
  `mut grid.cell(position).visit()`, `mut` chooses the `cell` that lends
  `mut`, and the part it lends is then changed by `visit` with no mark of
  its own. A part cannot be given up with `own`, and `let` keeps one only by
  copying it.
- **A lending method yields exactly once on every path.** A path with no
  `yield`, or with two, is a compile error.
- A lending method cannot drive a `for` loop or be pulled.

A method can also lend a value that it builds around its parts. This is how
a lookup that can miss lends an `Option` without copying the element:

```truss
fn Slice[Element].get(self, index: USize) lends Option[Element] {
  if index < self.length() {
    yield Some(self[index])
  } else {
    yield None
  }
}
```

- **The operand of `yield` may be a constructor application.** An argument
  that is a place is lent to the value that is built. It needs no `own` and
  no copy. The place can be any place the method could yield by itself.
- **Constructors nest,** as in
  `yield Some(SplitFirst(first: self[0], rest: self[1..]))`.
- **Only the constructor written directly after `yield` counts.** A `let`,
  an `if` expression, or a call around it does not, so the `if` above
  chooses between two `yield` statements.
- **The other fields have nothing to drop.** Beside a lent place, a field
  is a place, a nested constructor, or a value that is `Plain`, such as an
  index or a `Slice`. An owned value there is an error. Bind it to a name
  first, and the name is then a place.
- **A `mut` lend marks each place it lends `mut`:**
  `yield Indexed(index: index, value: mut self[index])`. The caller's
  changes to a marked field reach the place when the lend ends. A field
  without the mark is a value, and a change to it ends with the lend. Two
  places lent `mut` by one `yield` must be different places.
- **The value owns none of what it was lent.** It holds each lent place's
  value for as long as it is lent, and `self` is lent whole for that time,
  as it is when one part is lent.

A yielding method gives out parts one after another:

- `yields Cell` gives read-only parts, `yields mut Cell` lends `mut` access
  to each, and `yields own Cell` hands over owned values.
- **A yielding method drives a loop:**

  ```truss
  fn Grid.each(mut self) yields mut Cell {
    for index in 0..self.cells.length() {
      yield mut self.cells[index]
    }
  }

  for cell in mut grid {
    cell.age += 1
  }
  ```

  The loop's body runs at each `yield`. When the body leaves the loop with
  `break`, `return`, or `?`, the method stops at that `yield` and does not
  continue. A method may therefore end at any of its `yield`s, so the type's
  invariants, and the method's `ensures` clauses about how it ends, must hold
  at each one, whatever the caller did to the part it was lent. See
  [Contracts of lending and yielding methods](#contracts-of-lending-and-yielding-methods).
- `for item in items` uses `items.each()`, and `for item in mut items` and
  `for item in own items` use the `mut self` and `own self` versions. A
  user's type supports `for` by defining `each`, as methods of its own or by
  implementing `Iterable`, whose one method is `each(self)`.
- **Called anywhere but a `for` loop, a yielding method makes a cursor.** A
  method that yields read-only or owned values can be pulled one value at a
  time, through a cursor:

  ```truss
  var first_cursor = first.each()
  var second_cursor = second.each()
  var differences = 0
  while mut first_cursor.next() is Some(left) && mut second_cursor.next() is Some(right) {
    if left != right { differences += 1 }
  }
  ```

  `next()` runs the method to its next `yield` and returns `Some` of what it
  yields, and since pulling changes the cursor, the call is marked `mut`, or `None` when the method ends. A cursor that is never pulled
  again is simply dropped, which ends the method at its last `yield`, as
  `break` does. A cursor from an `own self` method owns what it iterates
  over. A cursor from a `self` method is a view. Cursors are how `zip`,
  merging sorted sequences, and looking ahead with `peek` are written.
- **A cursor's type has no name,** as with Rust's closures, but every cursor
  implements the prelude trait `Cursor`:

  ```truss
  trait Cursor {
    type Element
    fn next(mut self) -> Option[Self.Element]
  }

  type Lexer[Characters: Cursor[Element = Character]](characters: Characters, line: USize)
  ```

  A function or record that holds a cursor is generic over it, as `Lexer`
  is, which costs nothing at run time. To return a cursor, or to store one
  without a type parameter, use `any Cursor[Element = Int64]`, which
  allocates once. Usually a yielding method is simpler than returning a
  cursor. A hand-written cursor, such as one that keeps an explicit stack,
  implements `Cursor` too.
- A method that yields `mut` access cannot be pulled, because a cursor would
  have to store the access. To change two collections side by side, use
  indexes, or the standard `zip` for indexable collections:
  `for (first, second) in mut names.zip(mut ages)`.
- A method whose yields go through a recursive call, such as a tree's `each`
  that runs `for item in left { yield item }`, works in `for` loops but
  cannot be pulled, because its cursor would need room for every level of
  the recursion. Calling `next()` on its cursor is a compile error that
  names the recursive loop. To pull such a structure, write a cursor type
  that keeps an explicit stack.

#### Contracts of lending and yielding methods

A lending or yielding method's `ensures` says what it hands out and what it
leaves behind:

```truss
fn List[Element].each(self) yields Element
  ensures identical(result, self[yielded.length()])
  ensures finished ==> yielded.length() == self.length()
  cost time O(self.length())
{
  for index in 0..self.length() {
    yield self[index]
  }
}

fn Grid.cell(mut self, position: Position) lends mut Cell
  requires position.row < self.height && position.column < self.width
  ensures identical(result, old(self.cells[position.row * self.width + position.column]))
  ensures identical(
    self.cells.model(),
    old(self.cells.model()).update(position.row * self.width + position.column, value: yielded[0]),
  )
{
  yield mut self.cells[position.row * self.width + position.column]
}
```

- **A clause that mentions `result` holds at each `yield`,** where `result`
  is the part being handed out. The caller's statement, or the loop's body,
  may rely on it.
- **Every other clause holds wherever the method ends:** after its last
  statement, and, for a yielding method, at any `yield` where the loop
  stops.
- **`yielded` is a `Sequence` of the parts handed out so far,** each as the
  caller left it. A lending method's `yielded` holds its one part once the
  caller is done with it, which is how `Grid.cell` says that the cell the
  caller changed is the one in the grid afterward.
- **`finished` is `true` when the method ran to its end,** and `false`
  when a loop stopped it at a `yield`.
- **A `for` loop's `invariant` may use `yielded`,** for the values of the
  iterations before the current one:

  ```truss
  var total: Int64 = 0
  for score in scores
    invariant total == sum(yielded)
  {
    todo
  }
  ```

The facts every `for` loop gets, such as `i < count` in `for i in 0..count`
and that a loop over a list runs once per element, come from these clauses
on the standard library's `each` methods, so a user's collection gets the
same facts by making the same promises.

### Constructors

| Name | Use |
|---|---|
| `Type.new(...)` | The main way to make a value: `Account.new(owner)` |
| `Type.from(value)`, `Type.try_from(value)` | Conversions, through standard traits |
| `Type.default()` | A default value, through a standard trait |
| A descriptive name | Any other constructor: `List.with_capacity(64)`, `Map.seeded()` |

`new` is an ordinary name, not a keyword. A record whose fields are all visible
can be built directly (`Point(x: 0.0, y: 0.0)`) and does not need `new`. An
`UpperCamelCase` name before `(` is always a type or variant being built,
never a function, so building a value never looks like running code. Lists
and maps are built with literals too (`[]`, `[:]`), so they have no `new`.

## Function bodies

```truss
fn summarize(scores: List[Int64]) -> Result[Summary, SummaryError] {
  let count = scores.length()
  var best = 0
  for score in scores {
    if score > best { best = score }
  }
  let average = compute_average(scores)?
  Ok(Summary(count, best, average))
}
```

- `let` binds an immutable value. `var` binds a mutable one. Both take a
  pattern, as in `var (low, high) = bounds`, and every name a `var` binds is
  mutable. `var` is only allowed inside functions, so there are no mutable
  globals.
- `return`, `break`, `continue`, and `unreachable` have the type `Never`, so
  they can stand where a value is expected, such as in a `match` arm:
  `None => return Err(error)`.
- `?` returns early when a `Result` is an error. See Errors below.
- Every value must be used. A statement whose value is not `Unit`, such as a
  call to `FileWrite.write` that returns a `Result`, is a compile error. To
  discard a value on purpose, write
  `let _ = FileWrite.write(path, contents: report)`. The last expression of a
  block is the block's value, so it is always used. An `if` or `match`
  written as a statement must have `Unit` branches.
- Blocks, `if`, and `match` are expressions. A block's value is its last
  expression, so `summarize` returns the `Ok(...)` on its last line.
- `match` must cover every case, and every arm must be reachable. See
  [Patterns](#patterns).
- Every variable must be used. A `let` or a pattern that binds a name nothing
  reads is a compile error; bind it to `_` instead. Parameters are exempt,
  because an implementation of a trait may not need all of them.
- Code that can never run is a compile error, such as a statement after a
  `return`, a `break`, a call that returns `Never`, or a `while true` that is
  never left. Code after a `todo` is exempt, since it is unfinished, not
  dead.
- Statements end at a line break. There are no semicolons. See
  [Line breaks](#line-breaks) for when a line continues.
- Lambdas are written `fn(score) { score / 2 }`. See [Lambdas](#lambdas).

### Lambdas

```truss
let passing = scores.filter(fn(score) { score >= threshold })
let total = entries.fold(0, combine: fn(sum, (value, ..)) { sum + value })
mut scores.update_each(fn(score) { score = score / 2 })
```

- A lambda is written `fn(parameters) { body }`. Like any block, its body's
  value is its last expression.
- A lambda's parameter types, modes, and result type are never written. They
  come from the function type the lambda is passed as. In `update_each`,
  which takes `fn(mut Element)`, `score` can be changed.
- Types are worked out from the outside in: the receiver and the other
  arguments decide the function type first, and then the lambda's body is
  checked. A parameter's type is never worked out from how the body uses it.
- When nothing gives the lambda a function type, give one to the `let`, or
  type arguments to the call:

  ```truss
  let is_ready: fn(Job) -> Bool = fn(job) { job.is_ready() }
  let handler = make_handler[HttpRequest](fn(request) { respond(request) })
  ```

  `let length = fn(text) { text.length() }` is a compile error, with a fix
  that adds a type to the `let`.
- A parameter can be a pattern that matches every value, such as
  `(value, ..)`, or `_` for a parameter that is not used.
- A lambda can read local variables, but cannot change them. A lambda that
  reads local variables can be bound with `let`, held in a local record or
  list, and passed to a function-typed parameter. It cannot be returned,
  alone or inside another value, stored in a place the caller keeps, or
  given to an `own` function-typed parameter, because it would outlive the
  variables it reads. A named function, and a lambda that reads no local
  variable, can be returned, stored, and given up freely.
- A lambda's capabilities are inferred from its body. A lambda that calls
  `Clock.now()` can only be passed where a function type with `uses Clock`
  is expected.
- Inside a lambda, `return` and `?` leave the lambda, not the function around
  it. `break` and `continue` cannot reach a loop outside the lambda.
- There is no shorthand for a lambda's parameter, such as Kotlin's `it` or
  Swift's `$0`, and a lambda is always passed inside the parentheses.

### Errors

`?` returns the error unchanged, so it only works when the error type matches
the function's. To convert, call `map_error` first:

```truss
type ConfigError =
  | Unreadable(error: SystemError)
  | Malformed(error: ParseError)

fn load_config(file: Path) -> Result[Config, ConfigError]
  uses FileRead
{
  let text = FileRead.read_text(file).map_error(ConfigError.Unreadable)?
  let config = toml::parse(text).map_error(ConfigError.Malformed)?
  Ok(own config)
}
```

A variant with exactly one field can be used as a function, so
`ConfigError.Unreadable` is a function from `SystemError` to `ConfigError`. The same rule makes
`names.map(Some)` work. A variant with more fields is not a function: a
function takes its arguments by position, and fields have no order.

`?` also works on an `Option` in a function that returns an `Option`. It never
converts between the two: use `.ok_or(error)?` to turn an `Option` into a
`Result`, and `.ok()?` for the reverse.

`main` returns an `ExitCode`, so it cannot use `?`. It usually calls a function
that returns a `Result` and matches on it.

### Ranges

| Range | Meaning |
|---|---|
| `0..count` | From 0 up to `count`, not including `count` |
| `0..=UInt8.maximum` | From 0 up to and including the end |
| `(0..count).reversed()` | The same values, in reverse order |
| `(0..count).step_by(2)` | Every second value |

A range whose start is at or past its end is empty, not an error. The inclusive
form exists because some ranges cannot be written otherwise: `0..256` would
overflow a `UInt8`.

A range of characters, such as `Character"a"..=Character"z"`, holds the
characters between its ends in the order of their code points. The
surrogates are not characters, so U+E000 follows U+D7FF, as in Rust.

### Collections

| Literal | Meaning |
|---|---|
| `[2, 3, 5, 7]` | A `List`, or an `Array` or `Set` where one is expected |
| `[]` | An empty `List`, or an empty `Set` where one is expected |
| `["http": 80, "https": 443]` | A `Map` |
| `[:]` | An empty `Map` |

- A `[...]` literal is a `List` unless the expected type is an `Array` or a
  `Set`, as in `let colors: Set[String] = ["red", "green"]`. An `Array`
  literal must have exactly as many elements as the type says.
- The element types of `[]` and `[:]` come from the context or an annotation,
  as in `let names: List[String] = []`.
- Map keys are expressions, so `[name: 1]` uses the value of `name`. Keys in a
  literal must be proven distinct.
- The keys of a `Map` and the elements of a `Set` must be `Hash` and
  `Ordered`. Lookups, insertions, and removals cost O(log n) in the worst
  case, and O(1) in typical use.
- `Map.seeded()` and `Set.seeded()` make an empty collection whose hashing
  takes a key from the `Random` capability, so their signatures declare
  `uses Random`. They give the same results as ordinary ones, and stay fast
  even when keys are chosen to collide.
- Trailing commas are allowed. The formatter puts each element of a long
  literal on its own line.

#### Arrays

```truss
let digest: Array[UInt8, 32] = Array.filled(0)
let squares: Array[USize, 8] = Array.generate(fn(index) { index * index })
public let round_constants: Array[UInt32, 4] = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5]

fn sum[count: USize](values: Array[Int64, count]) -> Int64
```

- An `Array` holds its elements in place, with no heap allocation, and
  copies implicitly when its elements do. `Array[UInt8, 32]` is plain data,
  like an integer.
- `Array.filled(value)` and `Array.generate(fn(index) { ... })` take the
  length from the expected type. A literal works too, including in
  constants.
- Indexing and slicing work as for a `List`. An index must be proven
  smaller than `count`.
- An `Array` is never moved to the heap without being asked. A very large
  one can overflow the stack.

| Indexing | Meaning |
|---|---|
| `items[i]` | Element `i`, which must be proven in bounds. `i` is a `USize`. |
| `items.get(i)` | `Some(element)`, or `None` if `i` is out of bounds. |
| `items[1..4]`, `items[2..]`, `items[..3]` | A `Slice`, whose bounds must be proven. |
| `scores[i] = 0` | Replaces element `i`, which must be in bounds. |
| `ports[name]` | The value for `name`, which must be proven present, for example by an earlier `if ports.contains(name)`. |
| `ports.get(name)` | `Some(value)`, or `None` if `name` is missing. |
| `ports[own name] = 8080` | Inserts or replaces the value for `name`. The map keeps the key, so a key that is not plain data is given up with `own` or copied. |

- Ranges without a start or an end, such as `2..`, are only allowed inside
  brackets.
- Strings cannot be indexed. Use `text.bytes()` or `text.characters()` to say
  which you mean.
- A type supports `[]` by implementing the prelude trait `Index`, whose
  lending methods give read and `mut` access to an element and state with
  `requires` what an index must satisfy. See
  [Lending and yielding methods](#lending-and-yielding-methods).
- An assignment `collection[key] = value` inserts a missing key when the
  type also implements `IndexAssign`, whose one method `assign` takes the
  key and the value. `Map` does. For any other type the assignment replaces
  the element that `Index` lends, so the key must be there.

### Loops

| Loop | Meaning |
|---|---|
| `for score in scores { ... }` | Read each element. |
| `for score in mut scores { score = score / 2 }` | Change elements in place. |
| `for item in own items { ... }` | Use up the collection. |
| `for (index, element) in mut scores.enumerate() { ... }` | The mode applies to `scores`. |
| `for i in 0..items.length() { ... }` | Loop over a range. |
| `while low < high { ... }` | Loop while a condition holds. |

- The mode keyword goes on the collection, following the same rule as call
  sites. A `mut` loop may change elements but may not add or remove them.
- `while true { ... }` is the infinite loop. There is no `loop` keyword and no
  C-style `for`. A `while true` that no `break` leaves has type `Never`, so a
  function whose main loop runs forever can return `Never`.
- Loops are statements, not expressions. `break` and `continue` take no value
  or label. To leave nested loops at once, move them into a function and
  `return`.

When the compiler cannot prove something about a loop on its own, the loop can
state it with clauses written like signature clauses:

```truss
while low < high
  invariant high <= sorted.length()
  decreases high - low
{
  todo
}
```

`invariant` states a fact that holds at the start of every iteration.
`decreases` names a value that shrinks on every iteration and never goes below
zero, which proves the loop ends. Both are optional. `invariant` may repeat;
`decreases` appears at most once, and takes a list of measures compared in
order, as for a function.

A `cost` clause on a loop states what the loop has spent so far, at the
start of every iteration and when it ends. A loop needs one only when its
iterations cost different amounts, as when each one handles a row of its own
length:

```truss
fn sum_all(rows: List[List[Int64]]) -> Int64
  cost time O(rows.length() + rows.model().sum(fn(cells) { cells.length() }))
{
  var total = 0
  for row in rows
    cost time O(yielded.length() + yielded.sum(fn(cells) { cells.length() }))
  {
    for cell in row {
      total = total.saturating_add(cell)
    }
  }
  total
}
```

- A loop's `cost` takes the resources and bounds of a function's, and may
  repeat, but is never `amortized` or `finite`.
- Its bound can use the variables in scope at the loop and, in a `for`
  loop, `yielded`.
- `sum` adds up a measure of each element of a `Sequence`, here each row's
  length. The measure is a lambda or a named function that ends and uses no
  capabilities, and two lambdas with the same body are the same measure.

### Operators

The set of operators is fixed:

- Arithmetic: `+ - * / %`, and `-` for negation
- Comparison: `== != < <= > >=`
- Logic: `&& || !`, and `==>` for implication in specifications
- Bitwise: `& | ^ << >>`, and `~` for bitwise NOT

`!` works only on `Bool`, and `~` only on integers. Negation works only on
signed integers and floats; on a signed integer it must be proven not to
overflow, since `-Int8.minimum` does not fit.

`==` and `!=` use the `Equal` trait, and `<`, `<=`, `>`, and `>=` use
`Ordered`, whose `compare` method returns `Ordering.Less`, `Ordering.Equal`, or
`Ordering.Greater`. Both sides must have the same type, so `Int64 == Int32`
does not compile. `any` values and functions cannot be compared.

The arithmetic operators go through traits with a type parameter for the
right side and an associated type for the result, so the two sides can have
different types:

| Operator | Trait |
|---|---|
| `a + b` | `Add[Right]` |
| `a - b` | `Subtract[Right]` |
| `a * b` | `Multiply[Right]` |
| `a / b` | `Divide[Right]` |
| `a % b` | `Remainder[Right]` |
| `-a` | `Negate` |

```truss
impl Add[Duration] for Instant {
  type Output = Instant
  fn add_is_defined(self, right: Duration) -> Bool { true }
  fn add(self, right: Duration) -> Instant { todo }
}

let deadline = now + timeout
let scaled = velocity * 2.0
```

The built-in number types implement these only with themselves on both
sides. The bitwise operators and shifts work only on the built-in integer
types.

An operation need not be defined for every pair of values: `Int8`'s `+` is
not where the sum overflows, and its `/` is not for a divisor of 0. Each
trait therefore has a second method, which says where the operation is
defined, and the operation requires it:

```truss
public trait Add[Right] {
  type Output

  fn add_is_defined(self, right: Right) -> Bool
    cost time finite

  fn add(self, right: Right) -> Self.Output
    requires self.add_is_defined(right)
}
```

| Trait | Says where it is defined | Fixed-width integers | Floats |
|---|---|---|---|
| `Add[Right]` | `add_is_defined(right)` | the sum fits the type | always |
| `Subtract[Right]` | `subtract_is_defined(right)` | the difference fits the type | always |
| `Multiply[Right]` | `multiply_is_defined(right)` | the product fits the type | always |
| `Divide[Right]` | `divide_is_defined(right)` | `right != 0`, and not `minimum / -1` | always |
| `Remainder[Right]` | `remainder_is_defined(right)` | `right != 0`, and not `minimum % -1` | always |
| `Negate` | `negate_is_defined()` | `self != minimum` | always |

Generic code states the same obligation that an operator on a built-in
type has, and can also test it:

```truss
fn doubled[Number: Add[Number]](value: Number) -> Number.Output
  requires value.add_is_defined(value)
{
  value + value
}
```

A type whose operation is defined everywhere returns `true`.

For floats, `==` follows IEEE 754 except that every NaN equals every other NaN,
so `-0.0 == 0.0` is still true. In ordering, NaN comes after every number.
`x.is_nan()` tests for NaN. `x.ieee_equal(y)`, `x.ieee_less(y)`, and the
other `ieee_` comparisons follow IEEE 754 exactly, and compile to a single
instruction, for code where comparisons are the bottleneck.

#### Precedence

Operators bind in this order, tightest first:

| Operators | Notes |
|---|---|
| `.` `()` `[]` `?` `with (...)` | `a.b()?.c()`. `with` applies to the expression directly before it. |
| `mut` `own` `any` | Apply to the whole postfix expression after them, such as `mut config.servers.sort()`. See [Parameter modes](#parameter-modes) for which place they mark. |
| `-` `!` `~` | `-x.abs()` is `-(x.abs())`. `!is_ready == expected` is `(!is_ready) == expected`. |
| `*` `/` `%` | |
| `+` `-` | |
| `..` `..=` | `0..count - 1` is `0..(count - 1)`. |
| `==` `!=` `<` `<=` `>` `>=` `is` | `response is Ok(body)` tests a pattern. See [Testing a pattern](#testing-a-pattern-with-is). |
| `&&`, `\|\|` | |
| `==>` | Only in specifications. `a && b ==> c` is `(a && b) ==> c`. |
| `echo`, and the body after `=>` in `forall` or `exists` | `echo player.wins * 3` shows the product. |

Some combinations have no precedence at all and need parentheses:

- **Shifts and bitwise operators** (`<<`, `>>`, `&`, `|`, `^`) can be combined
  only with themselves: `a | b | c` is fine, but `(flags & 0xFF) | extra`,
  `a << (b + 1)`, and `(flags & mask) != 0` need their parentheses.
- **`&&` and `||`** cannot be mixed: `(is_ready && is_valid) || is_forced`.
- **Comparisons, `is`, ranges, and `==>`** cannot be chained: `a < b < c`,
  `a == b == c`, and `0..10..20` are errors.

Leaving the parentheses out is a compile error with a fix that adds them.

#### Compound assignment

```truss
self.buckets[index].count += 1
totals[region] += sale.amount
deadline += extension
flags |= Permission.write
```

- `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, and `>>=` exist
  for each binary operator. There is no `++` or `--`.
- `a += b` is a statement, like `=`. The left side must be a place.
- It means `a = a + b`, with the place written and checked once: an index is
  proven in bounds once.
- The old value of `a` is replaced, so it is handed to the operator as owned.
  When the operator's trait has a version that takes `own self`, that version
  is used and can reuse the old value's memory, so `matrix += other` can
  update in place.
- `truss fmt` writes `x = x + y` as `x += y`.

#### Integer division and shifts

- `/` on integers rounds toward zero, and `%` gives a result with the sign of
  the left operand, so `-7 / 2` is `-3` and `-7 % 3` is `-1`.
  `value.floor_divide(divisor)` and `value.floor_modulo(divisor)` round down
  instead.
- `>>` on a signed integer copies the sign bit. On an unsigned integer it
  shifts in zeros.
- The shift amount can be any unsigned integer type, and must be proven
  smaller than the number of bits in the value being shifted.

## Capabilities

A capability is a set of methods for doing something outside pure computation,
such as reading files or getting the time. A function lists the capabilities
it needs with `uses`. The code that runs it decides which implementation to
provide. The standard library declares the `Random` capability like this:

```truss
capability Random {
  fn next() -> UInt64
}

fn roll_die() -> UInt64
  uses Random
{
  Random.next() % 6 + 1
}
```

Code calls a capability's methods through the capability's name, as in
`Random.next()`. An implementation is an ordinary type with an `impl`, like a
trait implementation. Its methods take `self`, or `mut self` if they change
the implementation's own state:

```truss
type LoadedDie(face: UInt64)

impl Random for LoadedDie {
  fn next(self) -> UInt64 { self.face }
}

let rolled = provide LoadedDie(face: 5) {
  roll_die()
}
```

`provide implementation, ... { body }` runs the body using the given
implementations. They are handed over like arguments: a temporary needs no
mark, and a place is marked `mut` when its methods change its state. The
changes then remain in the place afterward:

```truss
var disk = files::MemoryFiles.new()
let config = provide mut disk, log::DiscardLog() {
  save_and_reload(Path.new("app.toml"))
}
```

Afterward, `disk` holds everything that was written.

- An implementation is never called directly. `Random.next()` is the only way
  to call it.
- A type can implement several capabilities. Providing it provides all of
  them.
- An `impl` can declare `uses` when its methods need capabilities of their own.
  Providing it then requires those capabilities.

### Standard capabilities

These capabilities are in the prelude:

| Capability | What it allows |
|---|---|
| `Console` | Reading standard input, writing standard output and standard error |
| `FileRead` | Reading files and listing directories |
| `FileWrite` | Creating, writing, renaming, and deleting files |
| `NetworkClient` | Opening outgoing connections and looking up names |
| `NetworkServer` | Listening for incoming connections |
| `Handles` | Reading, writing, and closing what is already open: a file, a connection, a listener, a running program |
| `Clock` | The current time, a monotonic clock, and sleeping |
| `Random` | Random numbers from the operating system |
| `Environment` | Environment variables, the current directory, and which operating system and processor the program runs on |
| `Processes` | Running other programs |
| `Signals` | Waiting for a signal sent to the program |
| `Tasks` | Running `concurrent` code and using channels |
| `Log` | Recording what the program did |
| `Panic` | Ending the program |

Each capability's methods are the least an implementation has to give.
What is built from them is an ordinary function in a module of the standard
library, such as `files::write_with` and `network::connect`, so it works
with every implementation.

`Panic` is built in. Its method is `Panic.crash("message")`, and it is also
required by `expect` and `unwrap`. Code cannot `provide` an implementation of
`Panic`.

`unreachable` is a keyword that marks a point the code can never reach, such
as a `match` arm ruled out by an earlier check. It must be proven unreachable.
If the prover cannot show that, it is an error, not a hidden crash.

### Files, connections, and other resources

A handle to something the operating system holds, such as an open file, a
network connection, or a running process, is released automatically when its
owner is done with it, the same way memory is:

```truss
fn first_line(path: Path) -> Result[Option[String], SystemError]
  uses FileRead, Handles
{
  var file = FileRead.open(path)?
  mut file.read_line()
}
```

The file is closed when `first_line` returns, on every path, including the
early returns from `?`.

- Opening is one capability and using what is open is another. `open` is
  `FileRead`'s, and `read_line` has `uses Handles`, as every method of a
  handle does. Code that is handed a file or a connection needs `Handles`
  alone, and can open nothing with it. Code that only holds a handle still
  cannot use it without the capability.
- Releasing a handle never runs Truss code and never fails. Types cannot
  define code that runs when a value is released.
- Anything that can fail, or that the program needs to know happened, is an
  explicit call that returns a `Result`, such as `flush`, `sync`, `shutdown`
  for closing a connection cleanly, and `wait` for a process's exit status.
- A buffered writer is only lent, inside a scope, so its data can never be
  lost without anyone knowing. `files::write_with` lends the writer to a
  function, then writes out what is left and returns the first error, from
  the function or from writing:

  ```truss
  fn save_report(path: Path, report: Report) -> Result[Unit, SystemError]
    uses FileWrite, Handles
  {
    files::write_with(path, write: fn(writer) {
      mut writer.write(report.header())?
      mut writer.write(report.body())
    })
  }
  ```

  Code never owns a writer, so it can never drop one with data left in it,
  and `?` inside the function needs no cleanup. A type that writes in
  stages, such as a CSV encoder, takes the writer as a `mut` parameter of
  each call.
- When the program panics, the operating system releases everything.

### main

A program starts at the `main` of its package's `main` module, which always
has this signature, plus whatever capabilities it uses:

```truss
fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead
{
  match Config.parse(arguments) {
    Ok(config) => run(config)
    Err(error) => {
      Console.print_error("${error}")
      ExitCode.failure
    }
  }
}
```

The runtime provides the real implementation of each capability in `main`'s
`uses` clause, and nothing else. The program ends when `main` returns its
`ExitCode`, or when it panics.

### Narrowing

To give code less than you have, provide an implementation that checks each
call and passes it on. Inside an implementation, calling the capability it
implements goes to the next provider out:

```truss
type FilesWithin(root: Path)

impl FileRead for FilesWithin
  uses FileRead
{
  fn read(self, file: Path) -> Result[List[UInt8], SystemError] {
    FileRead.read(self.root.join_within(file)?)
  }
}

let summary = provide files::FilesWithin(root: Path.new("logs")) {
  log_report::summarize(Path.new("access.log"))
}
```

The `impl` is shown with one of `FileRead`'s methods; the rest are written
the same way. `log_report::summarize` declares `uses FileRead` and cannot
tell it has been narrowed. Its read of `access.log` reaches
`logs/access.log` on the real file system, and a path such as `../secrets`
fails with a `SystemError`. Narrowing
again inside the block narrows further, since each layer passes its calls to
the one outside it. A capability that is not narrowed passes through unchanged.

### Layering

A capability can be built on others through its implementations. It cannot
inherit from them:

```truss
capability ReadDatabase {
  fn query(statement: SqlQuery) -> Result[Rows, DatabaseError]
}

impl ReadDatabase for PostgresReader
  uses NetworkClient
{
  fn query(self, statement: SqlQuery) -> Result[Rows, DatabaseError] { todo }
}
```

Code that `uses ReadDatabase` can run queries and nothing else. The network
access belongs to `PostgresReader`, so providing it requires `NetworkClient`.
A capability cannot be declared as a bundle of others, as in
`capability FileSystem: FileRead + FileWrite`. `uses` always names exactly the
capabilities the code itself can call.

## Parallelism

A `parallel` block runs each of its statements at the same time and ends when
all of them have finished:

```truss
fn total_score(players: Slice[Player]) -> Int64
  cost time O(players.length())
{
  let halves = players.split_at(players.length() / 2)
  parallel {
    let left = sum_scores(halves.first)
    let right = sum_scores(halves.second)
  }
  left.saturating_add(right)
}
```

- Each statement directly inside the block is a branch. To run several
  statements in one branch, wrap them in a block: `{ ... }`.
- A `let` in a branch is in scope after the `parallel` block, not in the other
  branches.
- Any branch may read any place. A place that one branch changes, by assigning
  to it or passing it as `mut` or `own`, cannot be used by any other branch.
- Branches cannot use capabilities, except `Panic`. Branches that use
  capabilities are written with `concurrent` (see
  [Concurrency](#concurrency)).
- A branch cannot leave the block early with `return`, `break`, `continue`, or
  `?`. Return a `Result` from the branch and use `?` after the block.

`parallel for` runs the iterations of a loop at the same time:

```truss
parallel for player in mut players {
  player.rating = estimate_rating(player.history)
}
```

It works with every form of `for`. The body may read any place but may only
change its own element and its own variables. It cannot use capabilities other
than `Panic`, and it cannot use `break`, `return`, or `?`. `continue` is
allowed.

## Concurrency

A `concurrent` block runs each of its statements as a task and ends when
every task has ended. The function that contains it needs `uses Tasks`:

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

- Branches are written as in a `parallel` block: each statement directly
  inside the block is a branch, and a `let` in a branch is in scope after
  the block, not in the other branches.
- A branch may use the capabilities of the code around it.
- Any branch may read any place. A place that one branch changes, by
  assigning to it or passing it as `mut` or `own`, cannot be used by any
  other branch.
- A `?`, `return`, or `break` that leaves the block cancels the other
  branches, waits for them to end, and then leaves. Above, a query that
  fails cancels the other query, and `profile` returns the error.
- The code after the block does not run when a branch leaves early, so a
  branch that takes a value out of a place gives one back before it ends.
- In a cancelled task, a call of the standard capabilities that would wait
  returns at once: `Err(SystemError.Cancelled)` where it returns a
  `Result`, and `None` where it returns an `Option`. `Tasks.cancelled()`
  tells whether the task has been cancelled.

`concurrent for` runs each iteration of a loop as a task:

```truss
fn serve(listener: network::Listener)
  uses Tasks, Handles, Log
{
  concurrent for connection in listener.connections() {
    handle(own connection)
  }
}
```

The body may read any place but may only change its own element and its
own variables. `break` leaves the loop and cancels the iterations that are
still running, and `continue` ends one iteration.

An iteration keeps running after the loop has gone on to the next value,
so what it is given must stay valid until the loop ends:

- A range, a cursor, and a method that `yields own` values give each task
  a value of its own.
- A method that yields read-only values may lend a place inside a
  parameter that it takes read-only, such as `yield self[index]` in the
  `each(self)` of a `List`. The method cannot change that parameter, so
  each task borrows its element for the whole loop. `concurrent for item
  in items` works this way for any element type.
- A method may yield a value that it computes for the `yield`. The task
  owns it.
- A `Plain` value may be yielded from any place. The task gets a copy.
- A method that yields `mut` access works when its body is one `for` over
  a range whose body is one `yield`, as the `each(mut self)` methods of
  `List`, `Slice`, and `Array` are. Each task then runs one iteration of
  that loop and changes its own element.

Any other `concurrent for` is rejected with
`ownership.task_outlives_yield`. A place in a local of the method or in a
`mut` parameter, and a view of one, could change or be freed when the
method resumes, while a task still uses it.

`yield` is not allowed in a `concurrent` block or a `concurrent for`. The
caller's loop body would run as a task, and it is checked as sequential
code.

A time limit is a function. Each of its two branches returns from the
function when it finishes, which cancels the other:

```truss
public fn within[Output, capability Granted](
  limit: Duration,
  work: (fn() -> Output uses Granted),
) -> Option[Output]
  uses Tasks, Clock, Granted
{
  concurrent {
    return Some(work())
    {
      Clock.sleep(limit)
      return None
    }
  }
}
```

### Channels

A task waits for another through a channel, a queue with a fixed capacity.
`send` waits while the channel is full, `receive` waits while it is empty,
and `close` ends the loops that receive from it:

```truss
fn total_size(paths: Slice[Path]) -> USize
  uses Tasks, FileRead
{
  let texts = Channel[String].new(capacity: 16)
  var total: USize = 0
  concurrent {
    {
      for path in paths {
        if FileRead.read_text(path) is Ok(text) {
          let _ = texts.send(own text)
        }
      }
      texts.close()
    }
    for text in texts.messages() {
      total = total.saturating_add(size(text))
    }
  }
  total
}
```

- A message is owned: sending it moves it. Its type is `Storable`: a
  record or a sum type of owned data, and never a view or a function. An
  `any Trait` can be sent only when `Trait` requires `Storable`.
- A channel's methods take `self` read-only, so every branch can use a
  channel that is declared before the block. `channel.copy()` is another
  reference to the same queue.
- `Channel[Message].new()` makes a channel of capacity 0, which holds no
  message: `send` returns when another task has received the message.
- `send` returns `Err(SendError.Closed)` on a closed channel. `receive`
  returns the messages that a closed channel still holds, and then `None`.
  `try_receive` never waits: it returns `None` when the channel is empty.
- In a cancelled task, a `send` that would wait returns
  `Err(SendError.Cancelled)`, and a `receive` that would wait returns
  `None`.
- A task that waits for several kinds of message receives a sum type from
  one channel.
- `tasks::Limiter` bounds how many tasks do something at once.
  `limiter.hold(work)` runs `work` when one of the limiter's permits is
  free, and returns `Some` of its output. In a task that is cancelled
  while it waits for a permit, `hold` returns `None` and does not run
  `work`.

### Shared state

State that several tasks change belongs to a capability implementation.
When the code inside a `provide mut` can use `Tasks`, calls of the
implementation's methods are mutually exclusive: each call holds the
implementation's mutex from start to end.

```truss
capability Sessions {
  fn open(user: UserId) -> SessionId
  fn close(session: SessionId)
}

type SessionTable(open: Map[SessionId, UserId], next: UInt64)

impl Sessions for SessionTable {
  fn open(mut self, user: UserId) -> SessionId {
    let session = SessionId(self.next)
    self.next = self.next.wrapping_add(1)
    self.open[session] = user
    session
  }

  fn close(mut self, session: SessionId) {
    let _ = mut self.open.remove(session)
  }
}

fn run(listener: network::Listener)
  uses Tasks, Handles, Log
{
  var table = SessionTable(open: [:], next: 0)
  provide mut table {
    serve_sessions(listener)
  }
}
```

- A check and the change that depends on it go in one method, since other
  tasks' calls can come between two calls.
- An implementation whose calls are mutually exclusive has no method with
  a parameter that can hold a function, or an `any` value, that uses a
  capability. Calling it while holding the mutex could deadlock.
- A capability's method keeps no view that it is given and returns no view
  of its implementation's state.
- An implementation provided without `mut` is only read, so it has no
  mutex.

### Testing concurrent code

A test provides a `Tasks` implementation that runs one task at a time and
chooses by a seed which runs next, so a test of concurrent code gives the
same result on every run:

```truss
test "two deposits both arrive" {
  let seeds: UInt64 = 64
  for seed in 0..seeds {
    var bank = Bank.new()
    provide mut bank, tasks::SeededTasks.new(seed) {
      concurrent {
        Accounts.deposit(alice, amount: 10)
        Accounts.deposit(alice, amount: 5)
      }
    }
    assert bank.balance(alice) == 15
  }
}
```

- The seeded implementation switches tasks only at capability calls, which
  are the only points where one task can see what another did.
- A test in which no task can go on fails, and reports what each task was
  waiting for. The report is a panic, so a function that provides a
  `SeededTasks` or a `World` outside a test declares `uses Panic`.

`simulation::World` provides every standard capability, with tasks
scheduled by a seed and a clock of its own. The clock advances only when
every task is blocked, and then it jumps to the earliest deadline of a
sleeping task. So a test of a time limit takes no real time:

```truss
test "a reply that never arrives ends at the time limit" {
  let world = simulation::World.new(seed: 3)
  provide world {
    let reply = tasks::within(Duration.seconds(5), work: fn() { wait_for_reply() })
    assert reply is None
    assert Clock.monotonic() == Duration.seconds(5)
    assert world.output() == ""
  }
}
```

- `simulation::Setup` holds what a world starts with, such as the lines of
  its console's input, its environment's variables, and its files.
  `World.from(setup, seed: seed)` makes the world.
- A world's file system is in memory. `Setup.with_file(path, contents)`
  puts a file in it, with the directories above the file, and
  `world.file_text(path)` reads one back.
- `world.fail_next(operation, error)` makes the next `Open`, `Read`, or
  `Write` of a file fail with `error`, once.
- A `World` is a reference to its state, so it is provided without `mut`.
  A test reads what happened, such as `world.output()` and
  `world.records()`, inside the `provide`.
- Each capability call into a `World` is a point where the seed may switch
  to another task.

## Strings and templates

Truss has two forms of string literal. Both insert values with `${expr}`.

### Ordinary strings

```truss
let greeting = "Hello, ${name}!"
let path = "C:\\logs\\today.txt"
```

A string literal is a `String` kept in the program's static memory, so making
one costs nothing. It is copied to the heap the first time it is changed. Only
`String` methods that write bytes, such as `push`, can change it, and their
cost clauses already allow an allocation. `copy()` of a literal's `String`
costs nothing, because both can share the static bytes. `StringSlice` is the view of a `String`, returned by methods such as
`trim()`, `split()`, and `lines()`.

An ordinary string fits on one line; a line break inside one is a compile
error. It supports these escapes:

| Escape | Meaning |
|---|---|
| `\n`, `\t`, `\r` | Line feed, tab, carriage return |
| `\0` | The NUL character |
| `\\`, `\"` | A backslash, a double quote |
| `\${` | A literal `${` |
| `\u{1F600}` | The Unicode scalar value with that hex code: 1 to 6 digits, at most `10FFFF`, and not a surrogate |

Any other backslash sequence is a compile error.

Strings have no concatenation operator. Text is joined with interpolation or
methods:

```truss
let greeting = "${salutation}, ${name}"
let line = fields.join(", ")
mut report.push(footer)
```

`+` on strings is a compile error, with a fix that rewrites it as
interpolation. A long string stays on one line; `truss fmt` never breaks one.

### Raw strings

A string between `"""` delimiters is *raw*: backslashes are ordinary
characters, so there are no escapes. Raw strings are for text that spans
several lines or contains many backslashes.

```truss
let phone = Regex"""\d{3}-\d{4}"""

let query = SqlQuery"""
  select name, email
  from users
  where id = ${user_id}
    and active = true
  """
```

- A raw string can sit on one line, like `phone`, or span several lines, like
  `query`.
- In a multi-line raw string, the opening `"""` ends its line, and the closing
  `"""` sits on its own line. The line breaks next to them are not part of the
  string. To end the string with a line break, leave an empty line before the
  closing `"""`.
- The closing `"""` sets the indentation. Its indentation is removed from every
  line, so `query` starts with `select`, and the `and` line keeps its two extra
  spaces.
- Every line must start with exactly the same whitespace as the closing
  `"""`, so a tab where the closing line has spaces is a compile error. A line
  that holds only whitespace is exempt: if it does not start with that
  whitespace, it becomes an empty line. Spaces after the opening `"""` are
  ignored, and `truss fmt` removes them.
- All other whitespace is kept exactly, including at the ends of lines.
  `truss fmt` never changes the text inside a string.
- Text that contains `"""` uses a longer delimiter. A string opened with
  `""""` ends at the next `""""`. A run of more quotes than the delimiter is
  a compile error, so a one-line raw string cannot start or end with `"`. Use
  the multi-line form for that.
- A raw string has no escapes of any kind. `${` starts an interpolation, and
  every other `$` is literal, so `"""Total: $${price}"""` puts a `$` before
  the price.
- Text that contains `${` itself, such as a shell script or JavaScript, opens
  the string with extra `$`s. In a string opened with `$$"""`, only `$${`
  starts an interpolation, and `${` is literal text:

  ```truss
  let script = Shell$$"""
    echo "${HOME}/$${folder}"
    """
  ```

  Here `${HOME}` reaches the shell unchanged, and `folder` is interpolated.
  In general, a string opened with *n* `$`s interpolates at *n* `$`s followed
  by `{`. Any `$`s before those are literal.
- Line endings are always `\n`, whatever line endings the source file uses.

### Interpolation

`${expr}` inserts the value of any expression. Single `{`, `}`, and `$`
characters are always literal, so JSON, regular expressions, and shell text
need no escaping:

```truss
let fixture = """
  { "name": "${name}", "tags": [] }
  """
```

- The expression can contain anything an expression can, including string
  literals and braces: `"Players: ${names.join(", ")}"`.
- An interpolation never contains a line break, in either form of string. A
  longer expression goes in a `let` first.
- An empty `${}` is a compile error.

### Tagged templates

A type name written directly before a string of either form makes a tagged
template:

```truss
let query = SqlQuery"select name from users where id = ${user_id}"
let pattern = Regex"[a-z]+@${domain}"
```

The tag is the type of the result. From another module it is written with the
module, as in `database::SqlQuery"..."`. A plain `"..."` string is the case
where the tag is `String`.

- The tag touches the opening quote, with no space: `Regex"..."`, not
  `Regex "..."`. Extra `$`s for a raw string go between them, as in
  `Shell$$"""`. The tag and the string form a single token.
- A tag is a plain type name, without generic arguments. If its type is
  generic, the arguments are inferred.

The pieces are never joined into a plain string. The first example above
becomes roughly the following, where `Literal(...)` stands for a piece of
literal text, which only the compiler can make:

```truss
SqlQuery.from_template(Template.new(
  literals: [Literal("select name from users where id = "), Literal("")],
  parts: [SqlParameter.from(user_id)],
))
```

A type can be used as a tag by implementing the prelude trait `FromTemplate`,
whose one method is `from_template`. The trait's associated type `Part` is the
type each interpolated value is converted to, and the method's parameter,
`Template[Part]`, holds the literal text and the converted values.

A tag states what makes its literal text valid with `requires`:

```truss
impl FromTemplate for Regex {
  type Part = RegexPart

  fn from_template(template: Template[RegexPart]) -> Regex
    requires is_valid_pattern(template.literals)
  {
    todo
  }
}
```

The literal text is known when the code is compiled, so the compiler proves the
`requires` by running `is_valid_pattern` on it. A check reads each piece's
text with `literal.text()`, a `StringSlice`, and its bytes with
`text.byte(index)`. `Regex"[a-z"` is a compile
error, and `Regex"[a-z]+"` needs no `?`, because building it cannot fail. Text
that is only known at runtime goes through a function that returns a `Result`,
such as `Regex.parse(text)`. DESIGN.md explains why tagged templates make
injection attacks impossible.

### Characters and bytes

Truss has no separate character literal. A single character or byte is a
tagged template:

```truss
let separator = Character","
let accent = Character"é"
let newline = UInt8"\n"
```

`Character"..."` must hold exactly one Unicode scalar value, and `UInt8"..."`
exactly one ASCII character. Both are checked when the code is compiled, and
neither allows `${...}`.

`text.characters()` gives the `Character`s of a string. What a reader sees as
one character can be several scalar values, such as an emoji with a skin tone,
so `text.graphemes()` gives those as `StringSlice`s.

## Traits and laws

```truss
trait Monoid: Equal {
  fn empty() -> Self
    cost time finite
  fn combine(self, other: Self) -> Self
    cost time finite

  law left_identity(value: Self) { Self.empty().combine(value) == value }
  law associative(first: Self, second: Self, third: Self) {
    first.combine(second).combine(third) == first.combine(second.combine(third))
  }
}

impl Monoid for Int64 {
  fn empty() -> Int64 { 0 }
  fn combine(self, other: Int64) -> Int64 { self.wrapping_add(other) }
}
```

A `law` is a property every implementation must satisfy. A trait bound on a
generic parameter is written `[Element: Ordered]`.

A law is about what methods return, so the prover can use it only where
those methods end and give the same result for the same arguments: methods
with a `time` clause and no capabilities, as `cost time finite` gives here.
An `impl`'s method keeps its trait's `time` clause.

A law can have `requires` clauses, as a theorem can. They are its premises:
the law must hold for every set of values that meets them.

### Required traits

A trait can require other traits, written like a bound. `+` joins several,
both here and in bounds such as `[Key: Hash + Ordered]`:

```truss
trait Ordered: Equal {
  fn compare(self, other: Self) -> Ordering

  fn max(own self, other: own Self) -> Self {
    if self.compare(other) == Ordering.Less { other } else { self }
  }

  law agrees_with_equal(first: Self, second: Self) {
    (first.compare(second) == Ordering.Equal) == (first == second)
  }

  law transitive(first: Self, second: Self, third: Self)
    requires first <= second
    requires second <= third
  {
    first <= third
  }
}

trait Loggable: Display + Hash {}

impl Loggable for Event {}
```

- A type must implement the required traits before it can implement the
  trait: `impl Ordered for Point` needs `Point` to implement `Equal`.
- A bound includes what the trait requires, so with `[Element: Ordered]`,
  `==` works on `Element`.
- Laws can use the methods of required traits.
- A trait cannot redeclare a method of a trait it requires. It can add a
  version of one that takes `self` another way, as a
  `trait Changeable: Iterable` can declare `each(mut self)`.
- Traits cannot require each other in a cycle.
- Each type implements a trait with its own `impl`. There are no impls that
  cover every type matching a bound.
- A trait with no methods of its own, like `Loggable`, combines traits for
  `any`: `List[any Loggable]`. Its `impl` is empty because there is nothing to
  write.

In the standard library, `Hash` and `Ordered` both require `Equal`.

### Methods with bodies

A method with a body, like `max`, is provided to every implementation. An
implementation can replace it with a faster version, but only one proven to
give the same result:

```truss
trait Ordered: Equal {
  fn compare(self, other: Self) -> Ordering

  fn max(own self, other: own Self) -> Self {
    if self.compare(other) == Ordering.Less { other } else { self }
  }
}

impl Ordered for Int64 {
  fn compare(self, other: Int64) -> Ordering { todo }
  fn max(own self, other: own Int64) -> Int64 { Int64.maximum_of(self, other) }
}
```

- The replacement must prove that its result is the one the provided body
  gives. A provided method can be replaced only when the prover reads its
  body as its definition: it is pure, has a `time` clause, and its body is
  functional, with no `var`, assignment, or loop (see
  [DESIGN.md](DESIGN.md#what-a-function-means-to-the-prover)).
- Code that calls the method reasons from the trait alone, so a replacement
  never changes what a call means, only how fast it runs.

### Implementing a trait for a generic type

An `impl` for a generic type states its conditions on the type's parameters,
as a method does:

```truss
impl Display for List[Element: Display] {
  fn display(self, output: mut TextBuilder) { todo }
}

impl Equal for Option[Value: Equal] {
  fn equal(self, other: Option[Value]) -> Bool { todo }
}
```

`List[Element]` implements `Display` exactly when `Element` does. A type has
at most one `impl` of each trait, whatever its type arguments, so an
`impl Display for List[String]` cannot sit beside the one above.

### Traits with type parameters

A trait can take type parameters, and a type can implement the trait once for
each set of arguments:

```truss
trait From[Source] {
  fn from(value: own Source) -> Self
}

impl From[Int32] for Int64 {
  fn from(value: own Int32) -> Int64 { todo }
}

impl From[UInt32] for Int64 {
  fn from(value: own UInt32) -> Int64 { todo }
}

let total = Int64.from(count)
```

- The `impl` is chosen by the types of the arguments, which are worked out
  first, without looking at which `impl`s exist. A literal argument has its
  default type. So adding an `impl` never changes which one an existing call
  uses.
- The `impl` is never chosen from the type the result is expected to have.
  Truss has no `into()` that guesses its target from context: the target is
  always named, as in `Int64.from(count)`.
- Truss has no other overloading. Two functions cannot share a name and
  differ only in their parameter types.

### Associated types

A trait can leave a type for each implementation to choose:

```truss
trait Index {
  type Key
  type Output
  fn contains_key(self, key: Self.Key) -> Bool
    cost time finite
  fn at(self, key: Self.Key) lends Self.Output
    requires self.contains_key(key)
  fn at(mut self, key: Self.Key) lends mut Self.Output
    requires self.contains_key(key)
}

impl Index for Grid {
  type Key = Position
  type Output = Cell
  fn contains_key(self, key: Position) -> Bool { todo }
  fn at(self, key: Position) lends Cell { todo }
  fn at(mut self, key: Position) lends mut Cell { todo }
}

fn total[Items: Iterable[Element = Int64]](items: Items) -> Int64
fn first[Items: Iterable](items: Items) -> Option[Items.Element]
```

- `type Key = Position` can only appear in an `impl`, where it says which
  type the implementation uses. Truss has no type aliases.
- `Items.Element` names an associated type of a generic parameter.
  `Iterable[Element = Int64]` constrains it in a bound.
- A trait's own type parameters are the types an implementation can be
  chosen by, as in `From[Source]`. Its associated types are the types each
  implementation decides, as in `Index`'s `Output`.
- A trait states its methods' preconditions through its own methods, as
  `Index` does with `contains_key`, so generic code can show them, and an
  implementation says what they mean for its type: a `List`'s keys are the
  indexes below its length.

### Deriving

A `derives` clause on a type asks the compiler to write trait implementations
for it:

```truss
type Point(x: Float64, y: Float64)
  derives Equal, Hash

type Priority =
  | Low
  | Normal
  | Urgent(deadline: Instant)
  derives Equal, Ordered

type Option[Value] =
  | Some(value: Value)
  | None
  derives Equal, Hash, Ordered
```

| Trait | What the compiler writes |
|---|---|
| `Equal` | Two values are equal when all their fields are equal. |
| `Hash` | Combines the hashes of all fields. |
| `Ordered` | Compares variants in the order they are declared, then fields in the order they are declared. |
| `Default` | Uses each field's default. Only a record can derive it. |
| `Copyable`, `Plain` | Nothing: they state that an opaque type can be copied, explicitly or implicitly. See below. |

- Every field must already have the trait, or deriving it is an error.
- A derived trait needs the traits it requires. Deriving `Ordered` or `Hash`
  also needs `Equal` to be derived, not written by hand, so that the derived
  implementations agree.
- A generic type has a derived trait only when its parameters do:
  `Option[Value]` is `Equal` only when `Value` is.
- A derived implementation satisfies the trait's laws automatically. A
  hand-written `impl` must prove them.

`Copyable` and `Plain` are prelude traits that the compiler implements. A
`Copyable` type has `copy()`, and a `Plain` type copies implicitly (see
[DESIGN.md](DESIGN.md#memory)). The compiler works them out from a type's
fields, except for an opaque type, which has them only when it declares them,
as in `public opaque type Token(bytes: Array[UInt8, 16]) derives Plain`. The
compiler checks a declaration against the fields, and other packages rely only
on what is declared. A generic opaque type that declares one has it under the
conditions its fields give: `Slice[Element]` is `Plain` for every `Element`,
because the view it holds is. Generic code that copies says so with a bound,
as in `[Element: Copyable]`.

`Storable` is a third. Every type that is not a view type has it (see
[DESIGN.md](DESIGN.md#views)), and no type declares it: the compiler works
it out from the fields of every type, opaque or not. A type parameter has
it only when bounded, so `List[Element]` is `Storable` where `Element` is,
and `any Trait` has it only when `Trait` requires it.
Generic code that keeps a value past the function that made it says so with
a bound, as in `Channel[Message: Storable]`.

Every type also has debug output, which tools such as the test runner use to
show values, as in a failed `assert`. Nothing needs to be derived for it. To
use a value in `${...}` interpolation, its type must implement `Display` by
hand.

- Trait methods are called with a dot, like other methods, without importing
  the trait.
- A call with a dot finds the type's own methods, and the methods of the
  traits it implements that come from the standard library, the calling
  package, or a package the calling package lists in its manifest. Traits
  from packages further away are not considered.
- If two of those traits give a type methods with the same name, a call with
  a dot is a compile error, however each takes `self`. Write the call in full
  instead: `Ordered.compare(first, second)`. A trait and a trait it requires
  are the exception, since one can only add a version of the other's method.
- A type's own method and a method of a trait it implements cannot be the
  same method: the same name, taking `self` the same way. An `impl` that
  would give a type such a method is a compile error. An `impl` in the
  type's own package can give it another version of a method it has, by
  writing that method itself. A method the `impl` leaves to the body its
  trait provides, and any method of an `impl` in another package, cannot use
  a name the type's methods have at all.
- An `impl` must be in the package of the trait, of the type, or of the
  outermost type of one of the trait's arguments. So `impl Multiply[Vector]
  for Float64`, which makes `2.0 * velocity` work, lives with `Vector`.
- Contracts and costs on a trait's methods apply to every `impl` and are
  proven for each one.
- An `impl`'s method may promise more than the trait: its own `ensures` and
  `cost` clauses, which it proves, and a `requires` that the trait's
  `requires` implies. A call that is known to reach that `impl`, such as
  `grid[position]` on a `Grid`, gets the `impl`'s contract. A call through a
  bound or through `any` gets the trait's.

### Values of any type with a trait

`any Trait` is the type of a value of some type that implements the trait. It
lets values of different types share a collection:

```truss
trait Handler {
  fn handle(self, request: Request) -> Response
    uses Database
    cost time O(request.body.length())
}

type Server(handlers: List[any Handler])

mut server.handlers.push(any UserRoutes(users: [:]))
mut server.handlers.push(any HealthCheck())

for handler in server.handlers {
  mut responses.push(handler.handle(request))
}
```

- `any value` takes ownership of the value and makes an `any`. It allocates
  once, which counts in `cost` clauses.
- `any` names exactly one trait. To combine traits, declare a trait that
  requires them, like `Loggable` above.
- `any` fixes every associated type of its trait, as a bound can:
  `any Cursor[Element = Int64]`.
- A method can be called through `any` if it takes `self`, `mut self`, or
  `own self`, has no generic parameters of its own, and does not take or
  return `Self`. Calling any other method on an `any` value is a compile
  error.
- An `any` value cannot be turned back into its concrete type.

## Tests

```truss
test "config loads with defaults" {
  let disk = files::MemoryFiles.new().with_text(Path.new("app.toml"), contents: "")
  let config = provide disk, log::DiscardLog() {
    load_config(Path.new("app.toml"))
  }
  assert config == Ok(Config.default())
}
```

A test must provide every capability its code uses, except `Panic`, unless
it declares them with `uses`. A test with `uses` is *external*: it gets the
real implementations of exactly those capabilities, as `main` does.

```truss
test "writes the report"
  uses FileRead, FileWrite
{
  let written = provide files::FilesWithin(root: Path.new("test_output/report")) {
    write_report(sample_report())
  }
  assert written == Ok(Unit)
}
```

- A test without `uses` is deterministic, and its result is cached until its
  code changes. An external test runs every time the test suite runs.
- An external test gets exactly what it declares, with no hidden isolation.
  To keep it to a scratch directory, narrow the capability with `provide`, as
  above.
- Failed tests are never retried automatically.
- A failed `assert` ends the test as failed. After an `assert`, the rest of the
  test can rely on what it asserted.
- Tests do not wait for proofs. A test build checks, as the code runs, every
  operation that could fail, such as an index, a `requires` that can run, or
  an addition that could overflow, so a test runs safely even where a proof
  has failed or is still running. A failed check ends the test as failed and names the operation.
  A program is built only once everything it can reach is proven.
- A panic fails only the test it happens in. There is no way to expect a
  panic: test error cases as `Result` values instead.
- A test that does not finish within the project's time limit fails.

## Proofs

Most facts are proven automatically. Proofs are written only when the prover
needs help, using ordinary Truss syntax.

### Theorems

A `theorem` is a named fact with its proof. It is written like a function:
`requires` gives its assumptions, `ensures` gives its conclusions, and the body
is the proof.

```truss
theorem reverse_keeps_length[Element](items: List[Element])
  ensures items.reverse().length() == items.length()
{
}

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

- An empty body asks the prover to prove the theorem on its own, as for
  `reverse_keeps_length`.
- Calling a theorem makes its `ensures` facts available at that point. After
  `reverse_twice(rest)`, the prover knows that `rest.reverse().reverse()` equals
  `rest`.
- A theorem that calls itself on smaller input is a proof by induction. Its
  `decreases` clause proves that the recursion ends.
- A theorem's body can use calls, `let`, `match`, `if`, and `assert`.

### Proof blocks

A `proof { }` block inside a function body gives the prover hints at that
point:

```truss
fn SortedList[Element: Ordered].insert(mut self, item: own Element) {
  let position = self.items.partition_point(fn(existing) { existing < item })
  mut self.items.insert_at(position, item)
  proof {
    insert_at_partition_point_keeps_sorted(old(self.items), position, item)
  }
}
```

A proof block is removed from the compiled program. It contains the same things
as a theorem's body.

### Proving laws

When the prover needs help showing that an implementation satisfies a trait's
law, a `proof` definition supplies it:

```truss
proof Monoid.associative for Int64 {
  wrapping_add_is_associative()
}
```

### Writing specifications

In specifications, `&&`, `||`, `==>`, and `if` are read from left to right,
so the right side can rely on the left: in
`index < items.length() && items[index] > 0`, `items[index]` is in bounds
because `index < items.length()` is true there.

These forms can be used in `requires`, `ensures`, invariants, laws, and proofs:

| Form | Meaning |
|---|---|
| `forall index in 0..items.length() => items[index] >= 0` | True for every value in a range or collection. |
| `forall value: Int64 => value + 0 == value` | True for every value of a type. |
| `exists item in items => item == target` | True for at least one value. |
| `index < split ==> items[index] < pivot` | Implication: when the left side is true, so is the right. |
| `old(self.items)` | A value as it was when the function was called. |
| `identical(result, self.model()[key])` | The same value, for values of any one type, whether or not it implements `Equal`. `==` is always the type's `Equal`. |
| `assert condition` | Inside a proof: a fact the prover must show, which can then be used. |

A quantifier over a range or a collection is an ordinary expression, and can
be used in code too. It runs as a loop that stops as soon as the answer is
known, and its body may rely on the bound name being in its range:

```truss
fn is_sorted[Element: Ordered](items: Slice[Element]) -> Bool
  cost time finite
{
  forall i in 1..items.length() => items[i - 1] <= items[i]
}
```

A quantifier over a whole type, such as `forall value: Int64`, and `==>`
cannot run, so they appear only in specifications and in the bodies of
functions for specifications only. A quantifier's body is pure: it cannot use
capabilities.

The prover reads `is_sorted`'s body as what `is_sorted` means, because the
function is pure, has a `time` clause, and its body is functional: `let`,
`if`, `match`, `is`, calls, fields, building values, `with`, operators, and
quantifiers, with no `var`, assignment, or loop. Any other function is known
to the prover only by its contract. See
[DESIGN.md](DESIGN.md#what-a-function-means-to-the-prover).

A function called in a specification must be pure, with no `uses` at all,
and have a `time` clause. A function that is defined only for some inputs
says so with `requires`, which every specification that calls it must meet.

- `a ==> b` binds more loosely than `&&` and `||`, so `a && b ==> c` means
  `(a && b) ==> c` and `a ==> b || c` means `a ==> (b || c)`, as in Dafny and
  Verus. It does not chain: `a ==> b ==> c` needs parentheses. Outside
  specifications, write `!a || b`.
- The body of `forall` or `exists` runs to the end of the expression. A
  quantifier can be the last operand of `&&`, `||`, or `==>`, as in
  `requires count > 0 && forall i in 0..count => items[i] > 0`, whose body is
  `items[i] > 0`.

Integer arithmetic in specifications is exact and never overflows. It is done
on `Integer`, the mathematical integers, a prelude type that exists only in
specifications:

- Every built-in integer type is a subset of `Integer`. In a specification,
  arithmetic on integers gives an `Integer`, and comparisons can mix integer
  types: `requires count <= items.length()` works with a `UInt32` count.
- An `Integer` can stand where a built-in integer is expected, as in
  `items[i + 1]`, and the prover checks that it fits.
- A function whose signature mentions `Integer`, such as
  `fn sum(items: Slice[Int64]) -> Integer`, can be called only from
  specifications. It is never compiled, and its body is a specification.

Float arithmetic in specifications follows IEEE 754, the same as in code.

#### Mathematical collections

Specifications describe collections through mathematical values that exist
only in specifications, as `Integer` does:

| Type | Values |
|---|---|
| `Sequence[Element]` | Finite sequences |
| `FiniteSet[Element]` | Finite sets |
| `FiniteMap[Key, Value]` | Finite maps |
| `Multiset[Element]` | Finite multisets |

A type gives its value in these terms by implementing the prelude trait
`Model`:

```truss
trait Model {
  type Value
  fn model(self) -> Self.Value
}
```

`List`, `Slice`, and `String` are modeled by sequences, `Map` by a finite map
and the order of its keys, and `Set` by a finite set and its order. Contracts
compare models:

```truss
fn List[Element].push(mut self, item: own Element)
  ensures identical(self.model(), old(self.model()).append(item))
  cost amortized time O(1)
{
  todo
}
```

- `model()` can be called only in specifications.
- The mathematical types compare by structure, so two lists with equal
  models are interchangeable in a proof.
- Their contracts, in `standard::specification`, are written with
  `identical`, as are the contracts that describe a collection through its
  model, such as `List.push`'s
  `ensures identical(self.model(), old(self.model()).append(item))`.
- A `[...]` literal is one of these types where one is expected, as in
  `ensures identical(self.model(), [])`.
- A function whose signature mentions one of these types is for
  specifications only, as for `Integer`.

`assert` means two different things in the two places it can appear. In a
proof, it is proven at compile time. In a test, it is checked when the test
runs. It cannot be used anywhere else.

## Unfinished code

`todo` marks code that is not written yet. It can stand in for an expression of
any type, a whole function body, or a type's definition:

```truss
public fn parse_config(text: String) -> Result[Config, ConfigError]
  cost time O(text.length())
{
  todo
}

fn render(report: Report) -> String {
  let header = render_header(report.title)
  let body = todo
  "${header}\n${body}"
}

public opaque type Session = todo
```

- For each `todo`, the compiler reports the type it must have and the names in
  scope, such as "hole of type `String`; in scope: `report: Report`,
  `header: String`".
- Code with holes is type-checked and proved. Callers are checked against the
  signature of an unfinished function.
- `truss build` refuses to build a program if `main` can reach a `todo`,
  including one in a proof.
- Tests run normally. A test that reaches a `todo` is reported as incomplete,
  not failed.
- A type defined as `todo` can be named and passed around, but its contents
  cannot be used until it is defined.

## Debug output

`echo` shows a value while the code runs, then returns it unchanged:

```truss
fn score(player: Player) -> Int64 {
  let base = echo player.wins * 3
  base.saturating_add(echo bonus(player))
}
```

- It records the value's debug output with the file, line, and expression
  text.
- It needs no `uses`, so it works in pure code. `echo expr` has the type of
  `expr`, and proofs and cost clauses treat it as `expr`.
- In tests, the output is attached to the test's report. Output from parallel
  branches and tasks is grouped by branch or task. In other runs, it goes to
  stderr.
- It is not allowed in proofs.
- Like `todo`, it cannot ship: `truss build` refuses a program if `main` can
  reach an `echo`, and a package containing one cannot be published.

## Modules and visibility

Each file is a module. A package is a directory with a `truss.toml` manifest
that has a `[package]` table.

`use` imports a module, never individual names. Names from the module are
then written with the module's name and `::` in front:

```truss
use standard::json
use standard::url

let settings = json::parse(text)?
let url = url::parse(raw)?
let fallback = json::Value.Null
```

- `::` always reaches into a module, and `.` always reaches into a type or a
  value. `url::parse` is a function in the `url` module, and `url.host()` is
  a method of the variable `url`.
- Every name that is not local or from the prelude shows where it comes from.
  `json::ParseError` and `url::ParseError` cannot be confused.
- There are no import aliases.
- A full path such as `standard::json::parse(text)` works without a `use`. Use
  it when two imported modules would have the same last name. Importing two
  modules with the same last name is a compile error.
- `use` lines come before every definition in a file. `truss fmt` sorts them.
- A `use` whose module the file never names is a compile error, as in Go.

The standard library's root module is `standard`.

### Module paths

Every `.truss` file in a package's directory is a module. Its path is the
package's name, then the directories it is in, then its file name:

| File in the `weather` package | Module |
|---|---|
| `forecast.truss` | `weather::forecast` |
| `forecast/hourly.truss` | `weather::forecast::hourly` |

- Every path starts with a package name: `standard`, a dependency's name from
  the manifest, or the package's own name. A file names another file of its
  own package the same way other packages do: `use weather::forecast::hourly`.
- A package from the registry has its owner in its name, so a path into one
  starts with two parts: `use acme::geometry::vector` imports the module
  `vector` of the package `acme::geometry`. A path holds no version.
- There are no relative paths, such as Rust's `super::`, so a module is
  written the same way wherever it is used.
- A directory is not a module by itself. `forecast.truss` and a `forecast/`
  directory can sit side by side.
- File and directory names must be `lower_snake_case` names.
- Modules in a package can use each other freely, even in a cycle. The
  dependencies between packages cannot form a cycle.

A method can be defined in any file of its type's package. In another file,
the type is named with its module:

```truss
use weather::forecast::hourly

fn hourly::Forecast.summary(self) -> String { todo }
```

The type must be visible there, so a type that is private to its file has
its methods in that file.

A small, fixed *prelude* is in scope in every file without a `use`. It holds
the names nearly every program needs, all of them `UpperCamelCase`, so they
never clash with variable or function names:

- the built-in types (`Int64`, `USize`, `Float64`, `Bool`, `String`, `Unit`,
  `Never`, and so on)
- `Option` (`Some`, `None`) and `Result` (`Ok`, `Err`)
- the core collections: `List`, `Slice`, `Map`, and `Set`
- the core traits, such as `Equal`, `Ordered`, `From`, `TryFrom`, `Default`,
  `Copyable`, `Plain`, `Storable`, `Index`, `IndexAssign`, `Iterable`,
  `Cursor`, `FromTemplate`, `Model`, and the arithmetic traits `Add`,
  `Subtract`, `Multiply`, `Divide`, `Remainder`, and `Negate`
- `Integer`, `Sequence`, `FiniteSet`, `FiniteMap`, and `Multiset`, for
  specifications
- the standard capabilities, such as `Console`, `FileRead`, and `Panic`, and
  the types signatures are written with everywhere: `Path`, `Instant`,
  `Duration`, and `SystemError`

Everything else is imported with `use`, including the standard library's
records for grouping values, `core::Pair` and `core::Indexed`, so that a
package's own `Pair` never clashes. Projects cannot define their own
prelude, and code cannot define a name that hides a prelude name. The prelude
changes only with a new language version.

| Keyword | Visible to |
|---|---|
| *(none)* | The same file only. This is the default. |
| `internal` | The whole package. |
| `public` | Everyone, including other packages. |

An `impl`, a test, and a `proof` of a law take no visibility keyword. An
`impl` applies wherever its trait and the types it names are visible, and
nothing names a test or a law's proof.

A public type can hide its contents with `opaque`:

```truss
public type Point(x: Float64, y: Float64)

public opaque type SqlQuery(text: String, parameters: List[SqlParameter])
```

`Point` makes its name and fields public. `SqlQuery` makes only its name
public. Outside its package, an opaque type can be named and passed around,
but its fields cannot be read, built, updated, or matched on. Other packages
use its methods instead. `opaque` is only allowed on `public` types, because
private and `internal` types are only visible within the package anyway.

A public function's signature cannot mention a private or `internal` type, and
neither can a public type's fields, unless the type is opaque. Other packages
could never name such a type.

### No foreign code

Truss code cannot call functions written in other languages. There is no
`extern` declaration and no raw pointer type, and `extern` and `unsafe` are
reserved. The standard library reaches the operating system through the
compiler, in ways that are not part of the language and that no other package
can use.

The standard library is also the only code that differs between operating
systems. Other code asks which one it runs on through the `Environment`
capability, so a test can provide a different answer.

### Package manifest

A package's manifest, `truss.toml`, names the package, says which Truss it is
written for, and lists the packages its code may use, each with the
capabilities it is granted:

```toml
[package]
name = "weather"
truss = "0.1"

[dependencies]
forecast = []
"truss::toml" = []
"truss::http" = ["NetworkClient", "Handles", "Clock"]
```

- **`name`** is a `lower_snake_case` name, or two joined by `::`, an owner
  and a name, as in `"acme::geometry"`. A package must have an owner in its
  name to be published. `standard` is the standard library's name, and a
  name of one part cannot be the owner of another package of the build.
- **`truss`** is the language version the package's files are read as, and
  the least toolchain that can build it.
- **Each entry of `[dependencies]`** is a package's name and the list of
  capabilities it is granted. An empty list grants none, so the package can
  only do pure computation. A prelude capability is written by its name, and
  any other by its full path, as in
  `"acme::store::connection::ReadDatabase"`. The build fails where code
  names something of a dependency that uses a capability the dependency was
  not granted.
- **A dependency is a package of the project** if the project has one by
  that name, and otherwise a package from the registry, at the version in
  the project's lock file. A manifest holds no versions and no paths to
  other packages.
- **A dependency the package never uses is a compile error,** as an unused
  `use` is. A package uses a dependency by naming one of its modules, or by
  calling a method of one of its traits with a dot.
- **A manifest is TOML, read strictly.** A table or a key that is not
  described here is an error, and so is a version, which manifests in other
  languages hold.

A package's program starts at the `main` of its `main` module, the file
`main.truss` beside the manifest. A package without that module is a library.

A package is verified for both widths of `USize`, 32 and 64 bits, unless its
`[package]` table says `usize_bits = 64`. Its code may then rely on 64 bits,
it cannot be built for a 32-bit target, and only packages that say the same
can depend on it. See [DESIGN.md](DESIGN.md#integers).

### Projects

A manifest with a `[project]` table makes its directory a project: every
package under it is one of the project's, except those under a directory
whose manifest has a `[project]` table of its own. A package with no such
manifest above it is a project by itself.

```toml
[project]

[test]
time_limit = 10
```

- The project's manifest may also hold a `[package]`, when the project's
  root is itself a package.
- `time_limit` is the time each test of the project may take, in seconds. It
  is 10 unless the manifest says otherwise.
- Two packages of a project cannot have the same name.

### The lock file

`truss.lock`, beside the project's manifest, holds the version and content of
every registry package the project's packages use, their dependencies' and
their dependencies' in turn. `truss add` and `truss upgrade` write it. It is
kept in version control.

```text
format 1
acme::geometry_v2 2.1.3 6f1c2f0f8f0b7a1e3d9c4a5b6e7d8c9f0a1b2c3d4e5f60718293a4b5c6d7e8f9
truss::http 1.12.0 0d4e8a1b7c3f2e6d5a9b8c7f1e0d3a2b4c6e8f0a1c3e5a7b9d1f3e5c7a9b0d2f holds Clock, Handles, NetworkClient
truss::toml 1.9.4 a3b1c5d7e9f20416283a4c6e8f0b2d4f6a8c0e2f4b6d8a0c2e4f6b8d0a2c4e6f
```

- The first line names the format. Each line after it is one package: its
  name, its version, the hash of its content, and after `holds`, the
  capabilities it holds, which are those its users in the build grant it.
  The lines are in order of name.
- A version is three numbers. The first is the number after `_v` at the end
  of the package's name, or 1 for a name without one.
- The hash is of the package's files as the registry holds them. It is the
  BLAKE3 hash of a line for each file, in the order of the bytes of their
  paths: the path, a space, the BLAKE3 hash of the file's bytes as 64
  hexadecimal digits, and a line feed. It is written as 64 hexadecimal
  digits too.
- A lock file that does not match the project's manifests is a compile
  error: a dependency with no line, a line no package uses, or a `holds`
  that the manifests' grants do not give. `truss check --fix` removes a
  line that is not used and corrects a `holds`, and `truss add` adds a
  line.

A published package holds its `truss.toml`, its modules, the Markdown files
beside them, and a `truss.lock` with a line for each registry package it
was published with, without `holds`: those its code uses, its tests apart,
and those that they use in turn. Only the lock file at a project's
root decides a build's versions directly. The others are what
[DESIGN.md](DESIGN.md#choosing-versions) calls a package's record: a build
uses the highest version that the project's lock file or any of its
packages' records names.
