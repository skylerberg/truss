# Writing Truss Programs

This guide teaches the `truss` commands and the part of the language that
small programs use. [SPECIFICATION.md](SPECIFICATION.md) defines every rule,
and each section below links to the rules it summarizes.

Truss proves its code correct. `truss check` rejects a program in which an
integer may overflow, an index may be out of bounds, or a value may be used
after it was moved. Most of the work is reading a diagnostic and changing the
code until `truss check` reports nothing.

## Setup

`truss` builds programs with `clang` or `cc` and proves them with Z3 5.3.3,
found as `z3` on the `PATH`. `TRUSS_CC` and `TRUSS_Z3` name others. It builds
programs for Linux and macOS.

## Commands

| Command | Effect |
|---|---|
| `truss new NAME` | Create the package `NAME` in the directory `NAME`, with `truss.toml` and `main.truss` |
| `truss check` | Report every error: syntax, types, ownership, capabilities, and proofs |
| `truss check --fix` | Apply every fix that is its diagnostic's only fix, then report the rest |
| `truss test` | Run the tests. `--match TEXT` runs only the tests whose names contain `TEXT` |
| `truss run ARGUMENTS` | Build the program for development and run it with the arguments; `--` goes before them when the first starts with `-` |
| `truss build` | Build the program for release, into a file named after the package |
| `truss holes` | List every `todo` with its type and the names in scope |
| `truss show NAME` | Print the signatures of a module, type, or function; `--body` prints whole definitions |
| `truss explain FILE:LINE:COLUMN` | Print the meaning, type, and signature of the name at a position |

- Run a command in the package's directory, or pass `-C DIRECTORY`.
- `--json` prints one JSON document in place of the report.
- The exit status is 0 when the code has no error, 1 when it has one, and 2
  when the command could not run.
- `truss test` and `truss run` do not wait for the prover. A program can run
  and pass its tests while a proof fails. The code is done when `truss check`
  exits with status 0.
- The commands share a background process. After the `truss` executable is
  rebuilt, a command can report that the database "is open in another
  process" until the old process exits, within a minute. `truss stop` ends it
  at once.

## A first program

`truss new fizzbuzz` creates `fizzbuzz/truss.toml` and `fizzbuzz/main.truss`.
Replace `main.truss` with:

```truss
fn fizzbuzz(n: Int64) -> String {
  if n % 15 == 0 {
    "FizzBuzz"
  } else if n % 3 == 0 {
    "Fizz"
  } else if n % 5 == 0 {
    "Buzz"
  } else {
    "${n}"
  }
}

test "multiples of three and five" {
  assert fizzbuzz(3) == "Fizz"
  assert fizzbuzz(10) == "Buzz"
  assert fizzbuzz(30) == "FizzBuzz"
  assert fizzbuzz(7) == "7"
}

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  for n in 1..=100 {
    Console.print_line(fizzbuzz(n))
  }
  ExitCode.success
}
```

```
$ cd fizzbuzz
$ truss check
$ truss test
1 passed in 0.2s (check 0.0s, build 0.2s, tests 0.0s)
$ truss run
1
2
Fizz
```

- `main` takes the command-line arguments and returns `ExitCode.success` or
  `ExitCode.failure`. `arguments[0]` is the program's name.
- `uses Console` declares the capability that `main` prints with. A function
  without `uses` is pure: it does no input or output.
- `"${n}"` interpolates a value whose type implements `Display`. Strings have
  no `+`.
- A block's value is its last expression, and `if` and `match` are
  expressions.
- Every argument after the first is labeled with its parameter's name, as in
  `add_numbers(left, right: text)`, unless it is a variable of that name:
  `add_numbers(left, right)`. See
  [Calls and arguments](SPECIFICATION.md#calls-and-arguments).

## Files and modules

- The `.truss` files beside `truss.toml` are the package's root module. They
  share one namespace: each file names the others' definitions without a
  `use`.
- Each subdirectory is a module. In the package `shapes`, the files of
  `geometry/` are the module `shapes::geometry`. After
  `use shapes::geometry`, another module writes `geometry::Point`.
- `use` imports a module, never a name: `use standard::json`, then
  `json::parse(text)`. An unused `use` is an error.
- A definition is visible only in its module. `internal` makes it visible in
  its package, and `public` in every package.
- The prelude needs no `use`. It holds the integer and float types, `Bool`,
  `Character`, `String`, `StringSlice`, `List`, `Slice`, `Map`, `Set`,
  `Option`, `Result`, `ExitCode`, `Path`, and the capabilities.

See [Modules and visibility](SPECIFICATION.md#modules-and-visibility).

## Types

```truss
public type Point(x: Int64, y: Int64)
  derives Equal, Hash, Ordered

public type Shape =
  | Circle(center: Point, radius: Int64)
  | Square(corner: Point, side: Int64)
```

| Expression | Value |
|---|---|
| `Point(x: 3, y: 4)` | A record, with its fields by name |
| `point.x` | A field |
| `point with (x: 0)` | A copy of `point` with `x` replaced |
| `Shape.Square(corner: origin, side: 4)` | A variant, named with its type |

- Truss has no tuples. Fields are built, matched, and read by name.
- `derives Equal` gives the type `==`. `Hash` and `Ordered` let it be a key of
  a `Map` or an element of a `Set`. A type without `Equal` cannot be compared;
  `ExitCode` is one, so a test compares `code.code == 0`.

A method is a function named `Type.name`:

```truss
public fn Shape.area(self) -> Option[Int64] {
  match self {
    Circle(radius, ..) => radius.checked_multiply(radius)?.checked_multiply(3)
    Square(side, ..) => side.checked_multiply(side)
  }
}

impl Display for Point {
  fn display(self, output: mut TextBuilder) {
    mut output.write("(${self.x}, ${self.y})")
  }
}
```

- A method whose first parameter is `self`, `mut self`, or `own self` is
  called on a value: `shape.area()`. A method without `self`, such as
  `fn TaskList.new() -> TaskList`, is called on the type: `TaskList.new()`.
- A pattern names a variant without its type. A bare name binds the field of
  that name, and `..` skips the other fields.
- A `match` covers every case, and every arm is reachable.
- An `impl Display` makes the type usable in `"${...}"`.

## Values and ownership

Every variable holds its own value, and no two names alias a value that
either can mutate.

| Code | Meaning |
|---|---|
| `let total = 0` | An immutable binding |
| `var total = 0` | A mutable binding |
| `fn TaskList.add(mut self, title: own String)` | `add` mutates its receiver and takes ownership of `title` |
| `mut list.add(own title)` | The call passes `list` as `mut` and moves `title`, which is unusable afterward |
| `mut list.add(title.copy())` | The call passes a copy, and `title` stays usable |
| `mut list.add("${count} items")` | A temporary takes no keyword |

- A parameter without a mode is read-only, and its argument is passed as a
  view, without a copy.
- The call site repeats `mut` or `own` for each place it passes to a `mut` or
  `own` parameter, the receiver included: `mut numbers.sort()`.
- `Plain` types copy implicitly: the integers, the floats, `Bool`,
  `Character`, and records and sum types made only of those.
- `String`, `List`, `Map`, and `Set` own heap memory. A `var`, a record
  field, a collection element, and a return value need an owned value, so a
  place there is written `own name`, which moves it, or `name.copy()`.
- While a view of a value is live, the value cannot be mutated or moved. A
  view is live until its last use.
- `list.get(index)` and `map.get(key)` lend the element for the rest of the
  statement. A `Plain` element can be bound, as in
  `if counts.get(word) is Some(count)`. Any other element is used in that
  statement or copied: `names.get(0).map(fn(name) { name.copy() })`.

See [Values and ownership](SPECIFICATION.md#values-and-ownership) and
[Lending methods](SPECIFICATION.md#lending-methods).

## Strings

- `String` owns its text, and `StringSlice` is a view of one. A string literal
  is a `String`, or a `StringSlice` where one is expected.
- A `String` passes to a `StringSlice` parameter as a view. `==` needs one
  type on both sides: `task.title.slice() == title`.
- `slice.to_string()` copies a `StringSlice` into a `String`, and
  `name.copy()` copies a `String`.
- Build text by interpolation, `"${count} lines"`, or by pushing onto a
  `var`: `mut text.push(line)`.
- Strings cannot be indexed. `lines()`, `split_whitespace()`, `split(",")`,
  `trim()`, `characters()`, `find(...)`, and `starts_with(...)` take them
  apart; `truss show StringSlice` lists the rest.
- `Int64.parse(text)` returns a `Result`, as does `parse` on every integer
  type.

## Collections and loops

| Literal | Value |
|---|---|
| `[1, 2, 3]` | A `List` |
| `["http": 80, "https": 443]` | A `Map` |
| `[]`, `[:]` | An empty `List` or `Map`, whose `let` or `var` states its type |

| Loop | Meaning |
|---|---|
| `for item in items` | Read each element |
| `for item in mut items` | Mutate each element in place |
| `for item in own items` | Move each element out |
| `for i in 0..n`, `for i in 1..=n` | Count up, excluding or including `n` |
| `while condition` | Repeat while the condition holds |
| `while mut queue.pop() is Some(item)` | Repeat until `pop` returns `None` |

- `items[i]` reads an element, and `truss check` proves `i` in bounds.
  `items.get(i)` returns an `Option` instead.
- `counts[own word] = 1` inserts or replaces a `Map` entry, and
  `counts.get(word)` returns an `Option`.
- A `for` loop over a `Map` visits its entries, `entry.key` and
  `entry.value`, in insertion order.
- A `List` passes to a `Slice` parameter, so `Slice` methods such as `sort`,
  `contains`, and `filter` work on a `List`. `List` has no `map`: build the
  new list with a loop and `push`.
- A lambda is `fn(item) { item % 2 == 0 }`. It reads the variables around it
  and cannot mutate them.

This program counts the words of its standard input:

```truss
fn count_words(text: StringSlice) -> Map[String, UInt64] {
  var counts: Map[String, UInt64] = [:]
  for word in text.split_whitespace() {
    let key = word.to_string()
    if counts.get(key) is Some(count) {
      counts[own key] = count.saturating_add(1)
    } else {
      counts[own key] = 1
    }
  }
  counts
}

test "words are counted" {
  let counts = count_words("a b a")
  assert counts.get("a") == Some(2)
  assert counts.get("b") == Some(1)
}

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  var text = ""
  while Console.read_line() is Some(line) {
    mut text.push(line)
    mut text.push(" ")
  }
  for entry in count_words(text) {
    Console.print_line("${entry.key}: ${entry.value}")
  }
  ExitCode.success
}
```

## Errors

```truss
type CalcError =
  | NotANumber(text: String)
  | Overflow
  derives Equal

fn parse_number(text: StringSlice) -> Result[Int64, CalcError] {
  Int64.parse(text).map_error(fn(_) { CalcError.NotANumber(text.to_string()) })
}

fn add_numbers(left: StringSlice, right: StringSlice) -> Result[Int64, CalcError] {
  parse_number(left)?.checked_add(parse_number(right)?).ok_or(CalcError.Overflow)
}
```

- `?` after a `Result` returns its error from the function unchanged, so the
  function's error type is the same type. `map_error` converts an error
  first.
- `?` after an `Option` works in a function that returns an `Option`.
- `if result is Ok(value) { ... }` tests and binds.
  `let Some(user) = find(id) else { return ... }` binds or leaves the
  function.
- `Option` and `Result` have `unwrap_or`, `ok_or`, `map`, and `and_then`.
  Their `unwrap` and `expect` stop the program on `None` or `Err`, so they
  need `uses Panic`.

## Integer arithmetic

`truss check` proves that no `+`, `-`, or `*` overflows, that no `/` or `%`
divides by zero, and that every index is in bounds. A literal takes its type
from its context, and is an `Int64` where nothing decides it. `length()`
returns a `UInt64`. Where the prover cannot prove an operation safe, the
diagnostic gives a counterexample if the prover found one. One of these makes
the operation safe:

| Choice | Code |
|---|---|
| Establish a bound | `if count < 100 { count + 1 } else { count }` |
| Require the bound of every caller | `requires value >= 0 && value < 1000` on the function |
| Saturate | `total.saturating_add(item)` |
| Return `None` on overflow | `total.checked_add(item)` |
| Wrap | `hash.wrapping_multiply(31)` |
| Stop the program | `total.checked_add(item).expect("the total overflows")` in a function with `uses Panic` |

- Division has `checked_divide` and `checked_remainder`.
  `Int64.minimum / -1` overflows, so a negative divisor needs them too.
- `Int64.from(byte)` widens, and `Int64.try_from(length)` narrows and
  returns a `Result`.
- `truss show FixedWidthInteger` lists every integer method.
- [Failure](SPECIFICATION.md#failure) says that `uses Panic` alone admits an
  operation that may fail. Stage0 does not implement that yet, so write the
  `expect` form above.

A recursive function or a loop needs no proof that it ends unless its
function states a `cost time` clause; see
[Termination](SPECIFICATION.md#termination).

## Capabilities

A function that does input or output declares the capabilities it uses, and
so does each caller, up to `main`:

```truss
fn count_lines(name: StringSlice) -> Result[UInt64, SystemError]
  uses FileRead
{
  let text = FileRead.read_text(Path.new(name))?
  Ok(text.lines().length())
}
```

| Capability | Methods |
|---|---|
| `Console` | `print`, `print_line`, `print_error`, `read_line` |
| `FileRead` | `read_text`, `read`, `open` |
| `FileWrite` | `write_text`, `write`, `create_directory`, `remove`, `rename` |
| `Clock` | `now`, `monotonic`, `sleep` |
| `Random` | `next`; `standard::random::below(bound)` uses it |
| `Environment` | `variable`, `current_directory`, `platform` |
| `Panic` | `Panic.crash(message)` |

`truss show Console` prints a capability's methods. See
[Capabilities](SPECIFICATION.md#capabilities).

## Tests

```truss
use standard::console
use standard::files

fn echo_lines() -> UInt64
  uses Console
{
  var count: UInt64 = 0
  while Console.read_line() is Some(line) {
    Console.print_line(line)
    count = count.saturating_add(1)
  }
  count
}

test "input lines are echoed" {
  var console = console::CapturedConsole.new(input: ["one", "two"])
  let count = provide mut console {
    echo_lines()
  }
  assert count == 2
  assert console.output() == "one\ntwo\n"
}

test "lines are counted in a file" {
  var disk = files::MemoryFiles.new().with_text(Path.new("notes.txt"), contents: "a\nb\n")
  let counted = provide mut disk {
    count_lines("notes.txt")
  }
  assert counted.ok() == Some(2)
}
```

- A test is `test "name" { ... }` in any file of the package. A failed
  `assert` fails the test.
- A test provides every capability its code uses, except `Panic`.
  `console::CapturedConsole` records output and supplies input lines, and
  `files::MemoryFiles` holds files for `FileRead` and `FileWrite`. Each is
  provided `mut`, since it changes as the code runs.
- A test that declares `uses Console` gets the real console. In stage0, such
  a test that prints breaks the test report, so test output through
  `CapturedConsole`.
- A test without `uses` is deterministic, and its result is cached until its
  code changes. `truss test --rerun` runs it again.

See [Tests](SPECIFICATION.md#tests).

## Unfinished code

- `todo` stands for any expression, body, or type definition. `truss check`
  and `truss test` accept it, and `truss holes` lists each one with its type
  and the names in scope. `truss build` refuses a program whose `main` can
  reach one.
- `echo expression` writes the value to standard error with its location,
  and returns the value. `truss build` refuses it too.

## Diagnostics

A diagnostic gives a position, a code, and a message, and often a `fix:`.
`truss check --fix` applies a fix that is its diagnostic's only fix. These
are the diagnostics a newcomer meets most:

| Code | Cause | Change |
|---|---|---|
| `types.missing_mode` | A place passed to a `mut` or `own` parameter without the keyword | `mut list.push(item)`, `own name` |
| `types.not_assignable` | An assignment to a `let` | Declare it with `var` |
| `ownership.lent_part_escapes` | A `let` binds an element that `get` lent | Use it in the statement, or `copy()` it |
| `types.mismatch` between `String` and `StringSlice` | Two string types where one is expected | `.slice()` or `.to_string()` |
| `types.unknown_member`, "A bare pattern must name a field" | A tuple pattern | Name the fields: `entry.key` |
| `types.no_impl` for `Equal` | `==` on a type without `Equal` | `derives Equal` on the type |
| `capabilities.not_available` | A call uses a capability that its function does not declare | `uses Console`, or `provide` in a test |
| `capabilities.provide_mode` | `provide` of a place without `mut` | `provide mut console` |
| `resolve.unused_import` | A `use` that nothing names | Delete it |
| `usage.unused_variable` | A binding that nothing reads | `_` in place of the name |
| `prover.overflow`, `prover.division` | An operation the prover cannot prove safe | See [Integer arithmetic](#integer-arithmetic) |
| `prover.requires` | An index, a slice, or a `requires` the prover cannot prove | Test the length or the condition with an `if` first |
| `parser.unexpected_token` at `let` in `while let` | Truss has no `while let` | `while mut queue.pop() is Some(item)` |

`truss explain FILE:LINE:COLUMN` prints the type of the expression at a
position.

## The standard library

`truss show` prints the standard library's signatures:

| To find | Run |
|---|---|
| A prelude type and its methods | `truss show String`, `truss show List`, `truss show Map` |
| One method | `truss show StringSlice.split` |
| A module's public definitions | `truss show standard::json` |
| A whole definition | `truss show standard::console::strip_styles --body` |

`truss show standard` prints every public definition, over ten thousand
lines, so show one module at a time. These modules serve small programs:

| Module | Contents |
|---|---|
| `standard::text` | `String`, `StringSlice`, `TextBuilder`, and `Parse` |
| `standard::list` | `List`, `Slice`, and `Array` |
| `standard::map`, `standard::set` | `Map` and `Set` |
| `standard::collections` | `Deque`, `Heap`, `SortedMap`, `SortedSet`, `BitSet`, and `LruCache` |
| `standard::console` | `CapturedConsole`, text styles, and terminal input |
| `standard::files` | `MemoryFiles`, file handles, and globs |
| `standard::arguments` | A parser of command-line flags, values, and subcommands |
| `standard::json` | Parsing, encoding, and decoding JSON |
| `standard::random` | Random numbers |
| `standard::time` | Dates, times, and durations |
| `standard::math` | `BigInteger` and functions on numbers |
