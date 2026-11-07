# Truss Syntax

This document describes how Truss code is written. For what the code means
(capabilities, costs, memory, failure, and so on), see [DESIGN.md](DESIGN.md).
Nothing is built yet. This is the design agreed so far.

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
  variable.
- A name that starts with an uppercase letter is `UpperCamelCase` and cannot
  contain `_`. Any other name is `lower_snake_case`: it has no uppercase
  letters, and `_` appears only singly, between parts. Names cannot start or
  end with `_`. `_` on its own is the wildcard pattern.
- Names can use letters from any script, following Unicode's rules for
  identifiers ([UAX #31](https://www.unicode.org/reports/tr31/)): a letter,
  then letters, digits, and joining marks. Keywords and the standard library
  use only ASCII.
- Letters from scripts without case, such as Chinese or Arabic, count as
  lowercase, so a name written in them is a value or function. A type name in
  such a script starts with an uppercase Latin letter.
- A name must be in Unicode Normalization Form C, so two names that look the
  same are spelled the same. `truss fmt` converts names to it.
- Names cannot be made to look like other names
  ([UTS #39](https://www.unicode.org/reports/tr39/)). A name mixes Latin with
  at most one other script, and never mixes Latin with Cyrillic or Greek. Two
  names visible in the same package that Unicode lists as confusable, such as
  Latin `paypal` and a Cyrillic look-alike, are an error.
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

`any` `assert` `break` `capability` `continue` `cost` `decreases` `derives`
`echo` `else` `ensures` `exists` `false` `fn` `for` `forall` `if` `impl` `in`
`internal` `invariant` `law` `let` `match` `mut` `opaque` `own` `parallel`
`proof` `provide` `public` `requires` `return` `self` `Self` `test` `theorem`
`todo` `trait` `true` `type` `unreachable` `use` `uses` `var` `while` `with`

A few words are keywords only in one position and ordinary names everywhere
else, because they are common names for variables and fields:

| Keywords | Where |
|---|---|
| `time`, `allocations`, `allocated_bytes`, `calls`, `finite` | Inside a `cost` clause |
| `result` | Inside `ensures`, where it names the return value |
| `old` | Inside specifications: `requires`, `ensures`, invariants, laws, `decreases`, `cost`, and proofs |

A parameter cannot be named `result`, and a function cannot be named `old`,
because inside specifications those names mean the return value and a value as
it was when the function was called.

These are reserved for possible later use, so they cannot be used as names
either:

`as` `async` `await` `const` `defer` `extern` `is` `loop` `macro` `static`
`unsafe` `where` `yield`

Reserving them now means adding one later breaks no code. It also lets the
compiler give a clear error when code borrowed from another language uses one,
such as "Truss has no `loop`; write `while true`".

## Line breaks

A line break ends a statement, with no semicolons. These rules say when one
does not:

1. Inside `(` and `[`, line breaks are ignored. Inside `{`, they count again,
   so a block inside a call's arguments works as usual.
2. Elsewhere, a line break ends the statement only if both of these hold:
   - The line ends with a token that can end an expression: a name, a
     literal, `)`, `]`, `}`, `?`, `true`, `false`, `self`, `todo`,
     `unreachable`, `break`, `continue`, or `return`.
   - The next line does not start with a token that continues one: `.`,
     `else`, `with`, `|`, `=>`, `->`, a clause keyword (`uses`, `requires`,
     `ensures`, `cost`, `invariant`, `decreases`, `derives`), or a binary
     operator that cannot begin an expression (`+ * / % == != < <= > >= & ^
     << >> && || .. ..=`).
3. The `{` that opens a body may start the next line, and a line break may
   come just before a closing `}`.

So all of these continue onto the next line:

```truss
let active_names = users
  .filter(fn(user) => user.is_active)
  .map(fn(user) => user.name.copy())

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
| `'a'` | Truss has no character literal. The fix writes `Character"a"`. |
| `` ` ``, `@` | Not used in Truss. |
| `++`, `--` | No increment or decrement. The fix writes the assignment out. `--x` is rejected too; write `-(-x)`. |
| `===`, `!==` | The fix writes `==` or `!=`. |
| `x ? a : b` | No conditional operator. The fix writes `if x { a } else { b }`. |
| `let mut x` | The fix writes `var x`. |
| `&x`, `&mut x` | The fix writes `x` or `mut x`. |
| `\|x\| x + 1` | The fix writes `fn(x) => x + 1`. |
| `Point { x: 1.0, y: 2.0 }` | Records are built with parentheses. The fix writes `Point(x: 1.0, y: 2.0)`. |
| `copy(original, backup)` | Arguments after the first need a label. The fix writes `copy(original, destination: backup)`. |
| `parse::<Int64>(text)` | The fix writes `parse[Int64](text)`. |
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

## Built-in types

| Type | Meaning |
|---|---|
| `Int8`, `Int16`, `Int32`, `Int64` | Signed integers |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | Unsigned integers |
| `USize` | Sizes, lengths, and indices |
| `ISize` | Offsets and differences between positions |
| `Float32`, `Float64` | IEEE 754 floating point |
| `Bool`, `String` | The usual meanings |
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
- A float has digits on both sides of the `.`: `0.5`, not `.5` or `1.`. This
  keeps `1..2` a range and `1.max(2)` a method call. The exponent is optional.
- The prefixes `0x`, `0b`, and `0o` and the exponent `e` are lowercase. Hex
  digits may be either case.
- Literals have no type suffixes. A literal takes its type from its context,
  as in `let small: UInt8 = 3` or `count + 1`. When nothing decides it, an
  integer literal is an `Int64` and a float literal is a `Float64`, so
  `var best = 0` makes an `Int64`.
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
  code is compiled. Calls to pure functions may be allowed later, once the
  compiler can run code while compiling.
- Like a string literal, a constant lives in the program's static memory.
  Reading one costs nothing, and it is copied to the heap only when a change
  needs more room.
- There is no `var` at the top level, so there are no mutable globals.
- A constant cannot be used as a pattern, because a `lower_snake_case` name in
  a pattern binds a new variable. Compare with `==` or a guard instead.

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
  distance` does not compile unless `Meters` defines the operation.
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
produces `Pair` values. A function that returns several values declares a
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
for (index, element) in scores.enumerate() { ... }

match items.split_first() {
  Some((first, rest)) => ...,
  None => ...,
}

match shape {
  Circle(radius, ..) => ...,
  Rectangle(corner, opposite_corner) => ...,
  Empty => ...,
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
  | Closed(low: Int64, high: Int64) invariant low <= high
  | Unbounded
```

- An invariant refers to fields by name. In a sum type, each variant can have
  its own invariant.
- `invariant` may repeat. All of the conditions must hold.
- Functions called in an invariant must be pure and have a `time` clause.

Invariants are proven at compile time, never checked at run time. When the
compiler cannot prove one, the usual fix is a constructor that checks or
establishes it:

```truss
fn DateRange.new(start: Date, end: Date) -> Option[DateRange]
fn Port.try_from(number: UInt16) -> Result[Port, PortError]
fn SortedList[Element: Ordered].from(items: own List[Element]) -> SortedList[Element]
```

`DateRange.new` returns `None` when `start` is after `end`, `Port.try_from`
returns an error for 0, and `SortedList.from` sorts its input.

## Functions and signatures

```truss
fn area(shape: Shape) -> Float64 {
  match shape {
    Circle(radius, ..) => math::pi * radius * radius,
    Rectangle(corner, opposite_corner) =>
      (opposite_corner.x - corner.x) * (opposite_corner.y - corner.y),
    Empty => 0.0,
  }
}
```

Parameter and return types are always written out. Inside function bodies,
types are inferred.

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
  has no meaning.
- Only a record or variant with exactly one field can take a bare value, as in
  `Some(3)`, `UserId(42)`, and `ConfigError.Malformed(error)`. With more than
  one field, every argument needs a label or a matching name, as in
  `Point(x: 0.0, y: 0.0)` or `Summary(count, best, average)`.

A call through a function value, such as `visit(item)` or
`compare(left, right)`, passes its arguments by position, because function
types have no parameter names.

A signature can carry clauses between the return type and the body:

```truss
public fn binary_search[Element: Ordered](sorted: Slice[Element], target: Element) -> Option[USize]
  requires is_sorted(sorted)
  ensures match result {
    Some(index) => sorted[index] == target,
    None => !contains(sorted, target),
  }
  cost time O(log(sorted.length()))
  cost allocations == 0
{
  ...
}
```

| Clause | Meaning |
|---|---|
| `uses Capability, ...` | The capabilities the function may use. Leaving it out means the function is pure. At most once. |
| `requires condition` | A precondition every caller must prove. May repeat. |
| `ensures condition` | A postcondition the function must prove. `result` names the return value. May repeat. |
| `cost resource bound` | A proven cost bound. Optional. May repeat. |

Clauses may be written in any order. The formatter sorts them into the order
`uses`, `requires`, `ensures`, `cost`. When a clause repeats, all of its
conditions must hold.

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
Expressions are written in terms of the parameters. `time(visit)` refers to the
time taken by a function parameter.

```truss
public fn load_configs(paths: List[Path]) -> Result[List[Config], ConfigError]
  uses FileRead
  cost calls(FileRead.read) == paths.length()
  cost time O(paths.length())
```

### Function types

A function type is written `fn(Input) -> Output`, optionally followed by
`uses`. As with definitions, `-> Unit` is left out. A function that passes on
whatever capabilities its callback needs declares a capability parameter with
`capability`:

```truss
public fn for_each[Item, capability Granted](items: List[Item], visit: fn(Item) uses Granted)
  uses Granted
  cost calls(visit) == items.length()
  cost time O(items.length() * time(visit))
```

A function type without `uses` is pure, the same as a function definition
without `uses`.

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

When a *place* (a variable, a field, or an element, such as `scores`,
`config.servers`, or `scores[0]`) is passed to a `mut` or `own` parameter, the
call site repeats the keyword. A reader can see what happens to each existing
value without looking up the signature.

A temporary value, such as a literal or the result of a call, is never marked.
Nothing else can see it, so it is always handed over as owned. Copies that
would allocate are never made implicitly; `copy()` makes one explicitly.

When the keyword comes before a longer expression, it applies to the place the
expression starts with. This is how a method call marks its receiver:

```truss
mut scores.sort()
mut config.servers.sort()
```

The first call modifies `scores`. In the second, the place is
`config.servers`.

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

- A view cannot be stored in a record field, a collection, or a `var`, and
  cannot be returned, with one exception: a method may return a view of
  `self`, as `items[1..4]`, `split_at`, `split_first`, and `text.trim()` do. A
  record holding views, such as the result of `split_at`, is a view itself.
- `mut` access never has a name. It lasts only for a call, a `mut` loop, or a
  `provide mut` block. Disjoint parts can be changed side by side, as in
  `sort(mut items[..middle])` and `sort(mut items[middle..])`.
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
fn List[Element].enumerate(self) -> Enumeration[Element]
fn List[Element].enumerate(mut self) -> MutableEnumeration[Element]
fn List[Element].enumerate(own self) -> OwnedEnumeration[Element]
```

The keyword at the call site picks the version, and no keyword picks the
read-only one. On a temporary value, the `own` version is used if there is one,
so `scores.filter(is_valid).enumerate()` moves the filtered elements instead of
copying them. This is the only overloading Truss allows.

### Constructors

| Name | Use |
|---|---|
| `Type.new(...)` | The main way to make a value: `Account.new(owner)` |
| `Type.from(value)`, `Type.try_from(value)` | Conversions, through standard traits |
| `Type.default()` | A default value, through a standard trait |
| A descriptive name | Any other constructor: `List.with_capacity(64)`, `Set.from(["red", "green"])` |

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

- `let` binds an immutable value. `var` binds a mutable one. `var` is only
  allowed inside functions, so there are no mutable globals.
- `?` returns early when a `Result` is an error. See Errors below.
- Every value must be used. A statement whose value is not `Unit`, such as a
  call to `FileWrite.write` that returns a `Result`, is a compile error. To
  discard a value on purpose, write
  `let _ = FileWrite.write(path, contents: report)`. The last expression of a
  block is the block's value, so it is always used. An `if` or `match`
  written as a statement must have `Unit` branches.
- Blocks, `if`, and `match` are expressions. A block's value is its last
  expression, so `summarize` returns the `Ok(...)` on its last line.
- `match` must cover every case.
- Statements end at a line break. There are no semicolons. See
  [Line breaks](#line-breaks) for when a line continues.
- Lambdas: `fn(score) => score / 2`, or `fn(score) { ... }` with a block body.
  A lambda can read local variables, as in
  `scores.filter(fn(score) => score >= threshold)`, but cannot change them.
  A lambda that reads local variables can only be passed as an argument, not
  stored or returned.
  Their types are inferred.

### Errors

`?` returns the error unchanged, so it only works when the error type matches
the function's. To convert, call `map_error` first:

```truss
type ConfigError =
  | Unreadable(error: FileError)
  | Malformed(error: ParseError)

fn load_config(file: Path) -> Result[Config, ConfigError]
  uses FileRead
{
  let text = FileRead.read_text(file).map_error(ConfigError.Unreadable)?
  let config = toml::parse(text).map_error(ConfigError.Malformed)?
  Ok(config)
}
```

A variant with exactly one field can be used as a function, so
`ConfigError.Unreadable` is a function from `FileError` to `ConfigError`. The same rule makes
`names.map(Some)` work.

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
| `(0..count).reverse()` | The same values, in reverse order |
| `(0..count).step_by(2)` | Every second value |

A range whose start is at or past its end is empty, not an error. The inclusive
form exists because some ranges cannot be written otherwise: `0..256` would
overflow a `UInt8`.

### Collections

| Literal | Meaning |
|---|---|
| `[2, 3, 5, 7]` | A `List` |
| `[]` | An empty `List` |
| `["http": 80, "https": 443]` | A `Map` |
| `[:]` | An empty `Map` |
| `Set.from(["red", "green"])` | A `Set`, which has no literal of its own |

- The element types of `[]` and `[:]` come from the context or an annotation,
  as in `let names: List[String] = []`.
- Map keys are expressions, so `[name: 1]` uses the value of `name`. Keys in a
  literal must be proven distinct.
- Trailing commas are allowed. The formatter puts each element of a long
  literal on its own line.

| Indexing | Meaning |
|---|---|
| `items[i]` | Element `i`, which must be proven in bounds. `i` is a `USize`. |
| `items.get(i)` | `Some(element)`, or `None` if `i` is out of bounds. |
| `items[1..4]`, `items[2..]`, `items[..3]` | A `Slice`, whose bounds must be proven. |
| `scores[i] = 0` | Replaces element `i`, which must be in bounds. |
| `ports[name]` | The value for `name`, which must be proven present, for example by an earlier `if ports.contains(name)`. |
| `ports.get(name)` | `Some(value)`, or `None` if `name` is missing. |
| `ports[name] = 8080` | Inserts or replaces the value for `name`. |

- Ranges without a start or an end, such as `2..`, are only allowed inside
  brackets.
- Strings cannot be indexed. Use `text.bytes()` or `text.characters()` to say
  which you mean.
- A type supports `[]` by implementing the prelude trait `Index`, whose method
  states with `requires` what an index must satisfy.

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
  C-style `for`.
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
  ...
}
```

`invariant` states a fact that holds at the start of every iteration.
`decreases` names a value that shrinks on every iteration and never goes below
zero, which proves the loop ends. Both are optional and may repeat.

### Operators

The set of operators is fixed:

- Arithmetic: `+ - * / %`, and `-` for negation
- Comparison: `== != < <= > >=`
- Logic: `&& || !`
- Bitwise: `& | ^ << >>`, and `~` for bitwise NOT

`!` works only on `Bool`, and `~` only on integers. Negation works only on
signed integers and floats; on a signed integer it must be proven not to
overflow, since `-Int8.minimum` does not fit.

`==` and `!=` use the `Equal` trait, and `<`, `<=`, `>`, and `>=` use
`Ordered`, whose `compare` method returns `Ordering.Less`, `Ordering.Equal`, or
`Ordering.Greater`. Both sides must have the same type, so `Int64 == Int32`
does not compile. `any` values and functions cannot be compared.

For floats, `==` follows IEEE 754 except that every NaN equals every other NaN,
so `-0.0 == 0.0` is still true. In ordering, NaN comes after every number.
`x.is_nan()` tests for NaN, and `x.ieee_equal(y)` gives exact IEEE equality.

Mixing `&&` with `||`, or bitwise operators with comparisons, needs
parentheses: `(is_ready && is_valid) || is_forced`.

## Capabilities

A capability is a set of methods for doing something outside pure computation,
such as reading files or getting the time. A function lists the capabilities
it needs with `uses`. The code that runs it decides which implementation to
provide. The standard library declares the `Clock` capability like this:

```truss
capability Clock {
  fn now() -> Instant
}

fn timestamp_message(message: String) -> String
  uses Clock
{
  "[${Clock.now()}] ${message}"
}
```

Code calls a capability's methods through the capability's name, as in
`Clock.now()`. An implementation is an ordinary type with an `impl`, like a
trait implementation. Its methods take `self`, or `mut self` if they change
the implementation's own state:

```truss
type FixedClock(time: Instant)

impl Clock for FixedClock {
  fn now(self) -> Instant { self.time }
}

let stamped = provide FixedClock(time: Instant.epoch) {
  timestamp_message("ready")
}
```

`provide implementation, ... { body }` runs the body using the given
implementations. They are handed over like arguments: a temporary needs no
mark, and a place is marked `mut` when its methods change its state. The
changes then remain in the place afterward:

```truss
var files = MemoryFiles(files: [:])
let config = provide mut files, DiscardLog() {
  save_and_reload(Path.new("app.toml"))
}
```

Afterward, `files` holds everything that was written.

- An implementation is never called directly. `Clock.now()` is the only way to
  call the clock.
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
| `NetworkServer` | Listening for and accepting incoming connections |
| `Clock` | The current time, a monotonic clock, and sleeping |
| `Random` | Random numbers from the operating system |
| `Environment` | Environment variables and the current directory |
| `Processes` | Running other programs |
| `Tasks` | Starting concurrent tasks and using channels |
| `Panic` | Ending the program |

`Panic` is built in. Its method is `Panic.crash("message")`, and it is also
required by `expect` and `unwrap`. Code cannot `provide` an implementation of
`Panic`.

`unreachable` is a keyword that marks a point the code can never reach, such
as a `match` arm ruled out by an earlier check. It must be proven unreachable.
If the prover cannot show that, it is an error, not a hidden crash.

### main

A program starts at `main`, which always has this signature, plus whatever
capabilities it uses:

```truss
fn main(arguments: List[String]) -> ExitCode
  uses Console, FileRead
{
  match Config.parse(arguments) {
    Ok(config) => run(config),
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
  fn read(self, file: Path) -> Result[Bytes, FileError] {
    FileRead.read(self.root.join_within(file)?)
  }
}

let summary = provide FilesWithin(root: Path.new("logs")) {
  log_report::summarize(Path.new("access.log"))
}
```

`log_report::summarize` declares `uses FileRead` and cannot tell it has been
narrowed. Its read of `access.log` reaches `logs/access.log` on the real file
system, and a path such as `../secrets` fails with a `FileError`. Narrowing
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
  fn query(self, statement: SqlQuery) -> Result[Rows, DatabaseError] { ... }
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
  time O(players.length())
{
  let halves = players.split_at(players.length() / 2)
  parallel {
    let left = total(halves.first)
    let right = total(halves.second)
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
- Branches cannot use capabilities, except `Panic`.
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

## Strings and templates

Truss has two forms of string literal. Both insert values with `${expr}`.

### Ordinary strings

```truss
let greeting = "Hello, ${name}!"
let path = "C:\\logs\\today.txt"
```

A string literal is a `String` kept in the program's static memory, so making
one costs nothing. It is copied to the heap the first time a change needs more
room. `StringSlice` is the view of a `String`, returned by methods such as
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
  that is empty or holds only whitespace may be shorter, and becomes an empty
  line.
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
becomes roughly:

```truss
SqlQuery.from_template(Template.new(
  literals: [literal "select name from users where id = ", literal ""],
  parts: [SqlParameter.from(user_id)],
))
```

A type can be used as a tag by implementing the prelude trait `FromTemplate`,
whose one method is `from_template`. Its parameter, `Template[Part]`, holds the
literal text and the interpolated values, each already converted to `Part`.

A tag states what makes its literal text valid with `requires`:

```truss
impl FromTemplate for Regex {
  fn from_template(template: Template[RegexPart]) -> Regex
    requires is_valid_pattern(template.literals)
  {
    ...
  }
}
```

The literal text is known when the code is compiled, so the compiler proves the
`requires` by running `is_valid_pattern` on it. `Regex"[a-z"` is a compile
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
trait Monoid {
  fn empty() -> Self
  fn combine(self, other: Self) -> Self

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
}

trait Loggable: Display + Hash {}

impl Loggable for Event {}
```

- A type must implement the required traits before it can implement the
  trait: `impl Ordered for Point` needs `Point` to implement `Equal`.
- A bound includes what the trait requires, so with `[Element: Ordered]`,
  `==` works on `Element`.
- Laws can use the methods of required traits.
- A trait cannot redeclare a method of a trait it requires, and traits cannot
  require each other in a cycle.
- Each type implements a trait with its own `impl`. There are no impls that
  cover every type matching a bound.
- A trait with no methods of its own, like `Loggable`, combines traits for
  `any`: `List[any Loggable]`. Its `impl` is empty because there is nothing to
  write.

A method with a body, like `max`, is provided to every implementation and
cannot be replaced by one. In the standard library, `Hash` and `Ordered` both
require `Equal`.

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
| `Default` | Uses each field's default. |

- Every field must already have the trait, or deriving it is an error.
- A derived trait needs the traits it requires. Deriving `Ordered` or `Hash`
  also needs `Equal` to be derived, not written by hand, so that the derived
  implementations agree.
- A generic type has a derived trait only when its parameters do:
  `Option[Value]` is `Equal` only when `Value` is.
- A derived implementation satisfies the trait's laws automatically. A
  hand-written `impl` must prove them.

Every type also has debug output, which tools such as the test runner use to
show values, as in a failed `assert`. Nothing needs to be derived for it. To
use a value in `${...}` interpolation, its type must implement `Display` by
hand.

- Trait methods are called with a dot, like other methods, without importing
  the trait.
- If two traits give a type methods with the same name, a call with a dot is a
  compile error. Write the call in full instead: `Ordered.compare(first,
  second)`.
- A type's own methods cannot share a name with the methods of its traits.
- An `impl` must be in the package of the trait or the package of the type.
- Contracts and costs on a trait's methods apply to every `impl` and are
  proven for each one.

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
  let response = handler.handle(request)
}
```

- `any value` takes ownership of the value and makes an `any`. It allocates
  once, which counts in `cost` clauses.
- `any` names exactly one trait. To combine traits, declare a trait that
  requires them, like `Loggable` above.
- A method can be called through `any` if it takes `self`, `mut self`, or
  `own self`, has no generic parameters of its own, and does not take or
  return `Self`. Calling any other method on an `any` value is a compile
  error.
- An `any` value cannot be turned back into its concrete type.

## Tests

```truss
test "config loads with defaults" {
  let files = MemoryFiles(files: [Path.new("app.toml"): ""])
  let config = provide files, DiscardLog() {
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
  provide FilesWithin(root: Path.new("test_output/report")) {
    write_report(sample_report())
  }
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
- `assert` is only allowed directly in tests and proofs.
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
    None => {},
    Some((first, rest)) => {
      reverse_twice(rest)
      reverse_of_append(rest.reverse(), suffix: [first])
    },
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
  let position = self.items.partition_point(fn(existing) => existing < item)
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

These forms can be used in `requires`, `ensures`, invariants, laws, and proofs:

| Form | Meaning |
|---|---|
| `forall index in 0..items.length() => items[index] >= 0` | True for every value in a range or collection. |
| `forall value: Int64 => value + 0 == value` | True for every value of a type. |
| `exists item in items => item == target` | True for at least one value. |
| `old(self.items)` | A value as it was when the function was called. |
| `assert condition` | Inside a proof: a fact the prover must show, which can then be used. |

Integer arithmetic in specifications is exact and never overflows. Float
arithmetic in specifications follows IEEE 754, the same as in code.

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

Each file is a module. A package is a directory with a `truss.toml` manifest.

`use` imports a module, never individual names. Names from the module are
then written with the module's name and `::` in front:

```truss
use standard::file_system
use standard::url

let text = file_system::read_text(path)?
let url = url::parse(raw)?
let local = file_system::Path.new("app.toml")
```

- `::` always reaches into a module, and `.` always reaches into a type or a
  value. `url::parse` is a function in the `url` module, and `url.host` is a
  field of the variable `url`.
- Every name that is not local or from the prelude shows where it comes from.
  `file_system::Path` and `url::Path` cannot be confused.
- There are no import aliases.
- A full path such as `standard::json::parse(text)` works without a `use`. Use
  it when two imported modules would have the same last name.

The standard library's root module is `standard`.

A small, fixed *prelude* is in scope in every file without a `use`. It holds
the names nearly every program needs, all of them `UpperCamelCase`, so they
never clash with variable or function names:

- the built-in types (`Int64`, `USize`, `Float64`, `Bool`, `String`, `Unit`,
  `Never`, and so on)
- `Option` (`Some`, `None`) and `Result` (`Ok`, `Err`)
- the core collections: `List`, `Slice`, `Map`, and `Set`
- the core traits, such as `Equal`, `Ordered`, `From`, `TryFrom`, `Default`,
  `Index`, and `FromTemplate`
- the standard capabilities, such as `Console`, `FileRead`, and `Panic`

Everything else is imported with `use`. Projects cannot define their own
prelude, and code cannot define a name that hides a prelude name. The prelude
changes only with a new language version.

| Keyword | Visible to |
|---|---|
| *(none)* | The same file only. This is the default. |
| `internal` | The whole package. |
| `public` | Everyone, including other packages. |

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

### Package manifest

The manifest names the package and its dependencies, and grants each
dependency the capabilities it may use:

```toml
[package]
name = "weather"
version = "0.3.0"

[dependencies]
json = { version = "2.1" }
http = { version = "4.0", capabilities = ["NetworkClient", "Clock"] }
```

A dependency with no `capabilities` list gets none, so it can only do pure
computation. The build fails if a dependency uses a capability it was not
granted.
