# The Truss Programming Language

## Introduction

Truss is a programming language in which the compiler proves that a program
does what its signatures say. When `truss check` accepts a program, no
integer in it overflows, no index is out of bounds, no value is used after
it is freed, no two parallel branches race on one value, and every function
meets the contract it states and terminates. The compiler also knows every
effect a function can have, such as reading a file, printing, or running
forever, because each effect is a *capability* that the function declares.

This guide teaches the language from the beginning. It assumes that you
have programmed before, in any language, but not that you know Truss or
have proven a program correct. Each chapter builds on the ones before it,
so read them in order the first time. The appendices at the end are for
looking things up.

[SPECIFICATION.md](SPECIFICATION.md) is the reference: it defines every rule
precisely, and the guide links to it where a rule has details the guide
leaves out. [DESIGN.md](DESIGN.md) gives the reason for each rule.

### What makes Truss different

Four decisions shape the language, and you will meet each of them early.

- **Every definition is checked alone, against the signatures it calls.** A
  function's signature states its types, the capabilities it uses, its
  contract, and its cost. The compiler proves the body meets them, and a
  caller depends only on the signature.
- **No two names alias a value that either can mutate.** A function can
  change only the arguments it is given as `mut`. Values are freed when
  their owner is done with them, with no garbage collector and no lifetimes
  to write.
- **Effects are capabilities.** A function that prints declares
  `uses Console`. A function with no `uses` clause is pure. Tests replace
  the real console, file system, and clock with fakes, so every test is
  deterministic.
- **Every operation that can fail is a proof obligation.** Where the
  compiler cannot prove that an addition fits its type, the code does not
  compile until you show why it fits or handle the case where it does not.
  Stopping the program is one way to handle it, which the code writes out
  and declares with `uses Panic`.

Truss has no comments. A comment can go stale without the compiler
noticing, so what a comment would say lives in a form the compiler checks:
a name, a contract, an invariant, or a test.

### How to use this guide

The chapters fall into three parts:

| Chapters | Part |
|---|---|
| 1 to 3 | Getting a program running, a first project, and the basics every language has |
| 4 to 11 | What makes Truss Truss: ownership, types, modules, collections, errors, traits, functions as values, and capabilities |
| 12 to 16 | Testing, contracts and proofs, parallel and concurrent code, advanced features, and a larger project |

Code in this guide comes in two kinds. A block of Truss code compiles: it is
a whole file, or one file of a larger program that the chapter shows in
pieces. A block of plain text shows a command, its output, or code that the
compiler rejects, with the error it reports.

### Contents

1. [Getting Started](#1-getting-started)
2. [Programming a Guessing Game](#2-programming-a-guessing-game)
3. [Common Programming Concepts](#3-common-programming-concepts)
4. [Ownership](#4-ownership)
5. [Records and Sum Types](#5-records-and-sum-types)
6. [Packages and Modules](#6-packages-and-modules)
7. [Collections](#7-collections)
8. [Error Handling](#8-error-handling)
9. [Generics, Traits, and Laws](#9-generics-traits-and-laws)
10. [Lambdas and Function Types](#10-lambdas-and-function-types)
11. [Capabilities](#11-capabilities)
12. [Writing Tests](#12-writing-tests)
13. [Contracts and Proofs](#13-contracts-and-proofs)
14. [Parallelism and Concurrency](#14-parallelism-and-concurrency)
15. [Advanced Features](#15-advanced-features)

Appendices: [A. Keywords](#appendix-a-keywords),
[B. Operators](#appendix-b-operators),
[C. The truss Command](#appendix-c-the-truss-command),
[D. The Standard Library](#appendix-d-the-standard-library).

## 1. Getting Started

### Installation

The `truss` command is the whole toolchain: it checks, tests, builds, and
runs Truss code. It needs two other programs on your `PATH`:

| Program | Used for | Override |
|---|---|---|
| A C compiler, `clang` or `cc` | Building programs | `TRUSS_CC` |
| Z3 5.3.3, as `z3` | Proving programs correct | `TRUSS_Z3` |

Truss builds programs for Linux and macOS. [README.md](README.md) says how
to build `truss` from this repository. Check that the toolchain runs:

```text
$ truss --version
stage0 (Truss 0.1, code generation 28, Unicode 18.0.0)
```

### Hello, world

`truss new` creates a package, the unit of Truss code that has a name and a
manifest:

```text
$ truss new hello
Created the package hello in hello.
$ cd hello
```

The directory holds two files. `truss.toml` is the package's manifest:

```toml
[package]
name = "hello"
truss = "0.1"
```

`truss = "0.1"` names the version of the language the package is written
in. `main.truss` holds the program. Replace its contents with:

```truss
fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  Console.print_line("Hello, world!")
  ExitCode.success
}
```

Then run it:

```text
$ truss run
Hello, world!
```

Four things in this program recur in every Truss program:

- **`fn main`** is where a program starts. It takes the command-line
  arguments as a `List[String]`, whose first element is the program's name,
  and returns an `ExitCode`, the status the program exits with.
- **`uses Console`** declares that `main` uses the console. A function can
  print only if its signature says so. Without the clause, `truss check`
  rejects the call to `Console.print_line`.
- **`Console.print_line("Hello, world!")`** calls the `print_line` method
  of the `Console` capability.
- **`ExitCode.success`** is the last expression of the body, so it is the
  value the function returns. Truss has no semicolons: a line break ends a
  statement.

### The truss command

You will use these commands all the time:

| Command | Effect |
|---|---|
| `truss check` | Report every error: syntax, types, ownership, capabilities, and proofs |
| `truss run` | Build the program for development and run it |
| `truss test` | Run the package's tests |
| `truss build` | Build the program for release, into a file named after the package |

```text
$ truss check
$ truss build
Built hello.
$ ./hello
Hello, world!
```

`truss check` prints nothing when the code has no errors or warnings. It is
the command that matters most: **code is finished when `truss check` reports
no errors.** A warning, such as for a private function nothing uses, points
at code to clean up, but it does not stop a build.
`truss run`, `truss test`, and `truss build` stop at any error, a failed
proof included.

Every command exits with status 0 when the code has no error, 1 when it has
one, and 2 when it could not run. Each runs in the package's directory, or
in the directory that `-C DIRECTORY` names, and prints one JSON document in
place of its report with `--json`. [Appendix C](#appendix-c-the-truss-command)
lists every command.

### Reading a diagnostic

Leave out the `uses Console` line and check the program again:

```text
$ truss check
main.truss:3:3: error[capabilities.not_available]: This call uses `Console`, which is not available here. Declare it with `uses Console`, or `provide` an implementation.
  |   Console.print_line("Hello, world!")
  |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
1 error
```

A diagnostic gives the file, line, and column; a code, such as
`capabilities.not_available`, that names the kind of error; and a message
that says how to fix it. Many diagnostics also carry a `fix:`, an edit that
makes the code compile. `truss check --fix` applies every fix that is its
diagnostic's only fix, then reports what is left. When a check reports
errors, run it first, then read what it changed: a missing label or a
misplaced `own` is gone, and a diagnostic with a choice of fixes is left for
you to decide. A fix can add a `.copy()`, which allocates, so keep only the
copies you want.

## 2. Programming a Guessing Game

This chapter builds a small program to show how a Truss program comes
together. The program picks a random number from 1 to 100, asks you to guess
it, and says whether each guess is too small, too big, or right. Later
chapters explain each feature it uses.

```text
$ truss new guessing_game
Created the package guessing_game in guessing_game.
$ cd guessing_game
```

### Reading a guess

The first version asks for a guess and prints it back:

```truss
fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  Console.print_line("Guess the number!")
  Console.print_line("Please input your guess.")
  let Some(guess) = Console.read_line() else {
    return ExitCode.failure
  }
  Console.print_line("You guessed: ${guess}")
  ExitCode.success
}
```

`Console.read_line()` reads one line of standard input. Its result is an
`Option[String]`: `Some(line)` when there is a line, or `None` at the end of
the input. A first attempt that prints the result directly does not compile:

```text
let guess = Console.read_line()
Console.print_line("You guessed: ${guess}")
```

```text
main.truss:7:38: error[types.no_impl]: `Option[String]` does not implement `Display`, so it cannot be interpolated.
  |   Console.print_line("You guessed: ${guess}")
  |                                      ^^^^^
1 error
```

Truss never lets you forget the case where a value is missing. `let
Some(guess) = ... else { ... }` takes the line out of the `Some`, binding it
to `guess`, and runs the `else` block when the result is `None`. The `else`
block must leave the function, here by returning `ExitCode.failure`.

`"You guessed: ${guess}"` is a string with an *interpolation*: the value
inside `${...}` is written into the text.

```text
$ echo 42 | truss run
Guess the number!
Please input your guess.
You guessed: 42
```

### Generating a secret number

Randomness is an effect, like printing, so it is a capability too:

```truss
use standard::random

fn main(arguments: List[String]) -> ExitCode
  uses Console, Random
{
  Console.print_line("Guess the number!")
  let secret = random::below(100) + 1
  Console.print_line("The secret number is: ${secret}")
  ExitCode.success
}
```

`use standard::random` imports the standard library's `random` module, and
`random::below(100)` calls its `below` function. Truss imports modules, not
names, so the module's name stays in front of every name from it.

`below` uses `Random`, so `main` must too. Without `Random` in the `uses`
clause, the call does not compile:

```text
main.truss:6:16: error[capabilities.not_available]: This call uses `Random`, which is not available here. Declare it with `uses Random`, or `provide` an implementation.
  |   let secret = random::below(100) + 1
  |                ^^^^^^^^^^^^^^^^^^
1 error
```

`truss show` prints the signature of any definition:

```text
$ truss show standard::random::below
standard/random/random.truss:258
public fn below(bound: UInt64) -> UInt64
  uses Random
  requires bound > 0
  ensures result < bound
```

The signature is more than types. `requires bound > 0` is a precondition
that every call must meet, and `ensures result < bound` is a postcondition
that every caller may rely on. That is why `random::below(100) + 1`
compiles: the compiler proves that a value below 100, plus 1, fits in a
`UInt64`. An addition it could not prove safe would be an error. You will
see that happen in [Chapter 3](#integer-overflow).

### Comparing the guess

To compare the guess with the secret, the program first needs the guess as
a number. Comparing the line with the secret does not compile:

```text
match guess.compare(secret) {
```

```text
main.truss:13:23: error[types.mismatch]: Expected `String`, found `UInt64`.
  |   match guess.compare(secret) {
  |                       ^^^^^^
1 error
```

`UInt64.parse` turns text into a number:

```truss
use standard::random

fn main(arguments: List[String]) -> ExitCode
  uses Console, Random
{
  Console.print_line("Guess the number!")
  let secret = random::below(100) + 1
  Console.print_line("The secret number is: ${secret}")
  Console.print_line("Please input your guess.")
  let Some(line) = Console.read_line() else {
    return ExitCode.failure
  }
  let Ok(guess) = UInt64.parse(line.trim()) else {
    Console.print_line("Please type a number!")
    return ExitCode.failure
  }
  Console.print_line("You guessed: ${guess}")
  match guess.compare(secret) {
    Less => Console.print_line("Too small!")
    Greater => Console.print_line("Too big!")
    Equal => Console.print_line("You win!")
  }
  ExitCode.success
}
```

- `line.trim()` removes the spaces and line ending around the text.
- `UInt64.parse` returns a `Result[UInt64, ParseIntegerError]`: `Ok` of the
  number, or `Err` of what was wrong with the text. `let Ok(guess) = ...
  else` takes the number out, as `let Some(...)` did with the line.
- `guess.compare(secret)` returns an `Ordering`, a type with three values,
  `Less`, `Equal`, and `Greater`.
- `match` picks the arm whose pattern matches the value. A `match` must
  cover every case, so leaving out the `Equal` arm is an error.

```text
$ echo 50 | truss run
Guess the number!
The secret number is: 37
Please input your guess.
You guessed: 50
Too big!
```

### Guessing until right

A `while true` loop asks again until the guess is right. `break` leaves the
loop, and `continue` starts the next guess when the text is not a number.
Written with only `uses Console, Random`, the loop does not compile:

```text
main.truss:8:3: error[capabilities.not_available]: This loop has no measure, so it uses `RunForever`, which is not available here. Declare it with `uses RunForever`, or give the loop a `decreases` clause.
  |   while true {
  |   ^^^^^^^^^^^^
1 error
```

Nothing guarantees that the player ever guesses right, so this loop may run
forever. **In Truss, every function terminates unless it says otherwise**, and
running forever is a capability like printing: a function that may do it
declares `uses RunForever`. A loop that the compiler can see ends, such as a
`for` loop over a range, needs nothing. [Chapter 13](#termination) covers
termination.

```truss
use standard::random

fn main(arguments: List[String]) -> ExitCode
  uses Console, Random, RunForever
{
  Console.print_line("Guess the number!")
  let secret = random::below(100) + 1
  while true {
    Console.print_line("Please input your guess.")
    let Some(line) = Console.read_line() else {
      return ExitCode.failure
    }
    let Ok(guess) = UInt64.parse(line.trim()) else {
      Console.print_line("Please type a number!")
      continue
    }
    Console.print_line("You guessed: ${guess}")
    match guess.compare(secret) {
      Less => Console.print_line("Too small!")
      Greater => Console.print_line("Too big!")
      Equal => {
        Console.print_line("You win!")
        break
      }
    }
  }
  ExitCode.success
}
```

The program no longer prints the secret. An arm's body is one statement or
a block in braces, as the `Equal` arm shows.

### Testing the verdict

Deciding what to say about a guess needs no console, so it can be a pure
function with tests of its own:

```truss
use standard::random

fn verdict(guess: UInt64, secret: UInt64) -> String {
  match guess.compare(secret) {
    Less => "Too small!"
    Greater => "Too big!"
    Equal => "You win!"
  }
}

test "a guess below the secret is too small" {
  assert verdict(10, secret: 50) == "Too small!"
}

test "the secret itself wins" {
  assert verdict(50, secret: 50) == "You win!"
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, Random, RunForever
{
  Console.print_line("Guess the number!")
  let secret = random::below(100) + 1
  while true {
    Console.print_line("Please input your guess.")
    let Some(line) = Console.read_line() else {
      return ExitCode.failure
    }
    let Ok(guess) = UInt64.parse(line.trim()) else {
      Console.print_line("Please type a number!")
      continue
    }
    Console.print_line(verdict(guess, secret))
    if guess == secret {
      break
    }
  }
  ExitCode.success
}
```

```text
$ truss test
2 passed in 0.2s (check 0.0s, build 0.1s, tests 0.0s)
```

`verdict` has no `uses` clause, so it is pure: it cannot print, read, pick
a random number, or run forever, and its tests give the same answer every
run. Notice
the call `verdict(10, secret: 50)`. Every argument after the first names its
parameter, unless it is a variable with the parameter's name, as in
`verdict(guess, secret)`.

You have now used variables, functions, `match`, loops, options, results,
capabilities, termination, and tests. The next chapter covers the basics in detail.

## 3. Common Programming Concepts

This chapter covers what most languages have: variables, types, functions,
and control flow. The examples are written as tests, which run with `truss
test`; [Chapter 12](#12-writing-tests) covers tests fully. For now, `test
"name" { ... }` is a block of code that runs, and `assert condition` fails
the test when the condition is false.

### Variables

`let` binds a name to a value that does not change, and `var` binds one that
can:

```truss
test "variables" {
  let width = 5
  var area = width * 3
  area += 1
  assert area == 16
}
```

Assigning to a `let` is an error:

```text
main.truss:3:3: error[types.not_assignable]: `count` cannot be mutated here: only a `var`, a `mut` parameter, or `mut self`, and their parts, can be assigned.
  |   count = 1
  |   ^^^^^
1 error
```

A few rules about names hold everywhere in Truss:

- Values, functions, fields, and modules are `lower_snake_case`. Types,
  variants, traits, and capabilities are `UpperCamelCase`.
- **A name cannot shadow another name in scope.** Writing `let name =
  name.trim()` inside a function whose parameter is `name` is an error, so a
  name means one thing throughout its scope:

  ```text
  main.truss:2:7: error[resolve.shadowed_name]: `name` is already a parameter, and a name cannot shadow another. Choose another name.
    |   let name = name.trim()
    |       ^^^^
  1 error
  ```

- **Every variable is used.** A binding that nothing reads is an error. Write
  `_` in place of a name you do not need.
- **Every value is used.** A statement whose value is not `Unit` is an error,
  so a result cannot be dropped by accident. `let _ = expression` discards
  one on purpose.

### Constants

A `let` outside any function is a constant. It states its type, and its
value is computed when the program is compiled:

```truss
let seconds_per_hour: UInt64 = 60 * 60

test "a constant" {
  assert seconds_per_hour == 3600
}
```

Truss has no mutable global variables: a top-level `let` never changes, and
`var` appears only inside functions. State that changes lives in variables,
in the values passed to functions, or behind a capability.

### Data types

Every value has a type, and the compiler infers the type of each variable
from the statement that declares it. You write a type where the statement
alone does not decide it, as in `let small: UInt8 = 3`.

#### Integers

| Type | Range |
|---|---|
| `Int8`, `Int16`, `Int32`, `Int64` | Signed, from -2<sup>n-1</sup> to 2<sup>n-1</sup> - 1 |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | Unsigned, from 0 to 2<sup>n</sup> - 1 |

```truss
test "integer literals" {
  let million = 1_000_000
  let mask: UInt8 = 0b1010_0101
  let color: UInt32 = 0xFF8800
  let permissions: UInt16 = 0o755
  assert million == 1000000
  assert mask == 165
  assert color == 16746496
  assert permissions == 493
}
```

A literal takes its type from where it is used. `let million = 1_000_000`
is an `Int64`, the type a literal has when nothing else decides it. Sizes and
counts, such as the result of `length()`, are `UInt64`.

**Integer types never convert implicitly.** Adding a `UInt8` to a `UInt64`
is an error, with a fix that converts the narrower one:

```text
main.truss:2:3: error[types.mismatched_integers]: Integer types never convert implicitly: this compares or combines `UInt8` with `UInt64`.
  |   small + large
  |   ^^^^^^^^^^^^^
  fix: Convert the left side to `UInt64`.
    replace "small" with "UInt64.from_integer(small)" at main.truss:2:3
1 error. `truss check --fix` fixes it.
```

A conversion between built-in number types is a method of the target type.
`from_integer` converts a value that the prover can show fits, which a value
of a narrower type always does. In code that has `Panic`, it also converts a
value that may not fit, and panics if the value does not. `try_from_integer`
returns a `Result` for a value that may not fit:

```truss
test "conversions" {
  let small: UInt8 = 200
  let wide = UInt64.from_integer(small)
  assert wide == 200
  assert UInt8.try_from_integer(wide).is_ok()
  assert UInt8.try_from_integer(wide * 2).is_err()
  assert wide.to_float64() == 200.0
}
```

`to_float64` and `to_float32` turn an integer into a float, and
`Int64.try_from_float64` turns a float back into an integer when it fits.

#### Integer overflow

In most languages, adding two large integers either wraps around silently or
stops the program. In Truss, **the compiler proves that no integer operation
overflows.** This function does not compile:

```text
fn add(left: UInt8, right: UInt8) -> UInt8 {
  left + right
}
```

```text
main.truss:2:3: error[prover.overflow]: `left + right` may overflow `UInt8`. For example, when `left` is 255, `right` is 1. It can also be checked first with an `if`, or done with the checked operation.
  |   left + right
  |   ^^^^^^^^^^^^
  fix: Add `requires left + right <= UInt8.maximum`
    replace " " with "\n  requires left + right <= UInt8.maximum\n" at main.truss:1:43
1 error
```

The prover found inputs for which the addition overflows, and the message
lists the ways to fix it. Each makes a different promise:

```truss
fn add_small(left: UInt8, right: UInt8) -> UInt8
  requires left <= 100 && right <= 100
{
  left + right
}

fn add_or_stay(left: UInt8, right: UInt8) -> UInt8 {
  if left <= 100 && right <= 100 { left + right } else { left }
}

fn add_saturating(left: UInt8, right: UInt8) -> UInt8 {
  left.saturating_add(right)
}

fn add_checked(left: UInt8, right: UInt8) -> Option[UInt8] {
  left.checked_add(right)
}

fn add_wrapping(left: UInt8, right: UInt8) -> UInt8 {
  left.wrapping_add(right)
}

fn add_or_stop(left: UInt8, right: UInt8) -> UInt8
  uses Panic
{
  left + right
}

test "the ways an addition can fit" uses Panic {
  assert add_small(100, right: 100) == 200
  assert add_or_stay(200, right: 100) == 200
  assert add_saturating(200, right: 100) == 255
  assert add_checked(200, right: 100) == None
  assert add_wrapping(200, right: 100) == 44
  assert add_or_stop(1, right: 2) == 3
}
```

| Function | Promise |
|---|---|
| `add_small` | Every caller proves that its arguments are at most 100: a `requires` clause is a precondition |
| `add_or_stay` | The `if` establishes the bound before adding |
| `add_saturating` | The result stops at the type's maximum |
| `add_checked` | The result is `None` when the sum does not fit |
| `add_wrapping` | The result wraps around, as hardware arithmetic does |
| `add_or_stop` | The program stops when the sum does not fit |

`uses Panic` declares that a function may stop the program, and the test
that calls `add_or_stop` declares it too. In code that has `Panic`, an
addition that does not fit stops the program with `arithmetic overflow`, so
nothing about it is proven. Code without `Panic` proves every addition, and
its release build checks none. To stop with a message of your own, write
`left.checked_add(right).expect("the sum fits in a UInt8")`.
[Chapter 8](#8-error-handling) covers failure in detail.

Division by zero and a shift by too many bits follow the same rule. An index
out of bounds is proven even in code that has `Panic`.

#### Floating point

`Float64` and `Float32` follow IEEE 754. A float operation never fails:
dividing by zero gives an infinity, and `0.0 / 0.0` gives NaN. Float
literals have a decimal point, `0.5`, or an exponent, `1e-9`, and are
`Float64` unless the context says otherwise.

```truss
test "floats" {
  let ratio = 0.5
  assert ratio * 2.0 == 1.0
  let tiny: Float32 = 1e-3
  assert tiny < 1.0
}
```

#### Booleans, characters, and strings

`Bool` has two values, `true` and `false`. Conditions are always `Bool`:
Truss never treats a number or a string as true or false.

`Character` is a Unicode scalar value. A character literal is a string
tagged with its type, `Character"é"`, which the compiler checks holds
exactly one character.

`String` is UTF-8 text. A string literal is written in double quotes, and
`${...}` interpolates a value into it. Strings have no `+` operator.
[Chapter 7](#strings) covers strings.

```truss
test "booleans, characters, and strings" {
  let is_ready = true
  assert is_ready && !false
  let letter = Character"é"
  assert letter != Character"e"
  let name = "Ada"
  assert "Hello, ${name}!" == "Hello, Ada!"
}
```

#### Unit and Never

`Unit` is the type with one value, also written `Unit`. A function that
returns nothing returns `Unit`. `Never` is the type with no values: an
expression of type `Never`, such as `return` or `break`, never finishes, so
it can stand where any type is expected.

#### Arrays

`Array[Element, count]` holds exactly `count` elements, stored in place
rather than on the heap. An array literal is written like a list literal,
where an array is expected:

```truss
test "arrays" {
  let flags: Array[Bool, 3] = [true, false, true]
  assert flags[2]
}
```

Most collections are `List`s, which grow; [Chapter 7](#7-collections)
covers both.

Where another language returns a tuple, a Truss function returns a record
with named fields, which [Chapter 5](#5-records-and-sum-types) introduces.

### Functions

A function is declared with `fn`, its parameters with their types, and its
result type after `->`:

```truss
fn area(width: UInt64, height: UInt64) -> UInt64
  requires width <= 1000 && height <= 1000
{
  width * height
}

fn greeting(name: StringSlice, punctuation: StringSlice = "!") -> String {
  "Hello, ${name}${punctuation}"
}

fn describe(count: UInt64) -> String {
  if count == 0 {
    return "none"
  }
  "${count} items"
}

test "calling functions" {
  assert area(3, height: 4) == 12
  let width: UInt64 = 5
  let height: UInt64 = 6
  assert area(width, height) == 30
  assert greeting("Ada") == "Hello, Ada!"
  assert greeting("Ada", punctuation: "?") == "Hello, Ada?"
  assert describe(0) == "none"
  assert describe(3) == "3 items"
}
```

- **A block's value is its last expression.** `area` returns `width *
  height`. `return` leaves a function early. A function without `->` returns
  `Unit`.
- **Every argument after the first is labeled with its parameter's name,** as
  in `area(3, height: 4)`, unless the argument is a variable with that name,
  as in `area(width, height)`. A call says what each argument means, and
  reordering parameters of the same type cannot silently swap arguments.
- **A parameter can have a default,** as `punctuation` does, and a call can
  leave the argument out.
- **Clauses between the signature and the body** state what the function
  promises. `requires` is one. [Chapter 13](#13-contracts-and-proofs) covers
  them all.

Truss has no overloading by argument types: one name in a scope is one
function. The order of definitions in a file never matters, so a function
can call one defined below it.

### Comments

Truss has no comments. When you want to explain code, put the explanation
where the compiler checks it:

| What a comment would say | Where it goes in Truss |
|---|---|
| What a definition is for | Its name |
| What a function does | Its signature, `requires`, and `ensures` |
| A fact that always holds | An invariant or a law |
| How long a call takes | A `cost` clause |
| An example of use | A test, named for what it shows |
| Why a piece of code exists | A name, such as `treat_missing_account_as_empty` |
| What a package is for | A Markdown file beside the code |

### Control flow

#### if

`if` takes a `Bool` condition and is an expression, so it can produce a
value:

```truss
fn parity(number: Int64) -> String {
  if number % 2 == 0 { "even" } else { "odd" }
}

fn sign(number: Int64) -> Int64 {
  if number > 0 {
    1
  } else if number < 0 {
    -1
  } else {
    0
  }
}

test "if is an expression" {
  assert parity(4) == "even"
  assert sign(-5) == -1
}
```

When an `if` is used as a value, both branches have the same type. An `if`
without an `else` has type `Unit`.

#### Loops

`while` repeats while its condition holds, and `for` visits each value of a
range or a collection:

```truss
test "loops" {
  var count = 0
  while count < 3 {
    count += 1
  }
  assert count == 3
  var seen: List[UInt64] = []
  for value in 1..=5 {
    if value == 2 {
      continue
    }
    if value == 5 {
      break
    }
    mut seen.push(value)
  }
  assert seen == [1, 3, 4]
}
```

| Range | Values |
|---|---|
| `0..n` | From 0 up to, but not including, `n` |
| `1..=n` | From 1 up to and including `n` |

`continue` starts the next iteration, and `break` leaves the loop. A loop is
a statement: it has no value. `while true` with no `break` has type `Never`,
since it never ends.

`mut seen.push(value)` calls a method that changes `seen`. The `mut` in
front of the call is required, and the next chapter explains why.

#### match

`match` compares a value against patterns and runs the first arm that
matches:

```truss
fn describe_count(count: UInt64) -> String {
  match count {
    0 => "none"
    1 => "one"
    2..=9 => "a few"
    _ => "many"
  }
}

test "match on a number" {
  assert describe_count(1) == "one"
  assert describe_count(5) == "a few"
  assert describe_count(50) == "many"
}
```

A `match` covers every possible value, and `_` matches anything. [Chapter
5](#pattern-matching) covers patterns fully.

## 4. Ownership

Ownership is how Truss manages memory and keeps code from changing a value
behind your back. It replaces both a garbage collector and the references of
languages such as C++ and Rust. There are no references to store and no
lifetimes to write. Instead, one rule holds everywhere:

**Every variable holds its own value, and no two names alias a value that
either can mutate.**

When a function receives a list, no other part of the program can change
that list while the function runs. When a variable goes out of scope, its
value is freed, because nothing else can refer to it. And code running in
parallel cannot race, because two branches never share a value that one of
them changes.

### Values and copies

Assigning a value to a new variable gives that variable its own value.
Changing one never changes the other:

```truss
test "a copy is independent" {
  var first: List[Int64] = [1, 2]
  var second = first.copy()
  mut second.push(3)
  assert first == [1, 2]
  assert second == [1, 2, 3]
}
```

Some types copy implicitly, and some do not:

- **`Plain` types copy implicitly.** A type made only of fixed-size data with
  nothing on the heap is `Plain`: the integers, the floats, `Bool`,
  `Character`, and the records, sum types, and arrays made only of those.
  `let b = a` copies `a`.
- **Other types copy only with `copy()`.** A `String`, a `List`, a `Map`, or
  a `Set` owns memory on the heap, and copying one allocates, so Truss makes
  every such copy visible. These types are `Copyable`: they have a `copy()`
  method.
- **A handle, such as an open file, is not `Copyable` at all.**

The compiler decides which of these traits a type has from its fields, so
you do not declare them, except on an opaque type ([Chapter
6](#visibility)), which states `derives Copyable` or `derives Plain` because
other packages cannot see its fields.

### Moving

A non-`Plain` value can also be *moved*: its ownership passes to another
variable, a field, a collection, or a function, and the original name can
no longer be used. `own` marks a move:

```truss
fn collect_names(first: own String, second: own String) -> List[String] {
  var names: List[String] = []
  mut names.push(own first)
  mut names.push(own second)
  names
}

test "moved names end up in the list" {
  assert collect_names("Ada", second: "Grace") == ["Ada", "Grace"]
}
```

`push` takes ownership of its argument, so the call writes `own first`. Using
`first` again after the move is an error, and the compiler offers to copy at
the move instead:

```text
main.truss:3:22: error[ownership.use_after_move]: `name` is used after it was moved.
  |   mut names.push(own name)
  |                      ^^^^
  note: main.truss:2:22: `name` is moved here.
  fix: Pass a copy at the move instead.
    delete "own " at main.truss:2:18
    insert ".copy()" at main.truss:2:26
1 error. `truss check --fix` fixes it.
```

Leaving out `own` is an error too, because a move or a copy is always
written where it happens:

```text
main.truss:2:18: error[ownership.needs_owned]: An owned value is needed here, and `name` is a place. Pass it `own` to move it, or copy it.
  |   mut names.push(name)
  |                  ^^^^
  fix: Move it with `own`.
    insert "own " at main.truss:2:18
  fix: Copy it.
    insert ".copy()" at main.truss:2:22
1 error
```

An owned value is needed wherever a value is stored: in a `var`, an `own`
parameter, a record field, a collection element, and a function's result. A
*place*, that is, a variable or a field or element of one, written there
needs `own` or `.copy()`. A *temporary*, a value that a call or a literal
just produced, needs neither, since nothing else holds it.

### Parameter modes

A parameter has one of three modes, and the call site repeats the mode for
every place it passes:

| Parameter | Call | The function may |
|---|---|---|
| `items: List[Int64]` | `total(items)` | Read the caller's value, which it sees without a copy |
| `items: mut List[Int64]` | `clear(mut items)` | Change the caller's value, which the caller sees afterward |
| `item: own String` | `keep(own item)` | Keep the value: the caller gives it up |

```truss
fn total(numbers: Slice[Int64]) -> Int64 {
  var sum: Int64 = 0
  for number in numbers {
    sum = sum.saturating_add(number)
  }
  sum
}

fn reset(numbers: mut List[Int64]) {
  for number in mut numbers {
    number = 0
  }
}

test "parameter modes" {
  var numbers = [3, 4, 5]
  assert total(numbers) == 12
  reset(mut numbers)
  assert numbers == [0, 0, 0]
}
```

The `mut` at the call site is not decoration. It tells a reader of the call
which arguments may change, without opening the function. The same keyword
precedes a method's receiver when the method changes it, as in `mut
numbers.push(9)`. `for number in mut numbers` lends each element `mut` to
the loop's body.

A mode keyword applies to the longest place at the start of the expression
after it. `mut config.servers.sort()` passes `config.servers` as `mut`.

### Views

A read-only parameter does not copy its argument. It is a *view* of the
caller's value. So is a `let` bound to a place, the variable of a `for` loop,
and a slice:

```truss
fn tail(items: Slice[Int64]) -> Slice[Int64]
  requires items.length() > 0
{
  items[1..]
}

test "a slice views part of a list" {
  let items = [1, 2, 3, 4]
  let middle = items[1..3]
  assert middle == [2, 3]
  assert tail(items) == [2, 3, 4]
}
```

`Slice[Int64]` is a view of a run of elements, and `StringSlice` is a view
of a `String`'s text. A `List` passes to a `Slice` parameter, and a `String`
to a `StringSlice` parameter, as a view: this is Truss's one implicit
conversion.

Views come with two rules, which are what let Truss do without stored
references:

**While a view is live, what it views cannot change or move.** A view is
live until its last use:

```text
fn grow(items: mut List[Int64]) -> UInt64 {
  let middle = items[1..]
  mut items.push(9)
  middle.length()
}
```

```text
main.truss:3:7: error[ownership.mutated_while_viewed]: `items` cannot be passed `mut` while `middle`, which views it, is still live.
  |   mut items.push(9)
  |       ^^^^^
1 error
```

`push` might move the list's elements to a larger buffer, and `middle` would
then point into freed memory. Using `middle` before the `push`, and not
after it, compiles.

**A view never outlives what it views.** A function returns a view only of
what its parameters view, as `tail` does. Returning a view of a local is an
error, because the local is freed when the function returns:

```text
main.truss:1:4: error[ownership.view_escapes]: This returns a view of `items`, which is dropped when the function returns, so the view would dangle. A function returns a view only of its parameters.
  | fn numbers() -> Slice[Int64] {
  |    ^^^^^^^
1 error
```

A view cannot be stored where an owned value goes, such as a field of a
type that outlives the function. A view held in a local record or list makes
that record or list a view too.

### Lending methods

Some methods hand back a part of their receiver instead of a new value. A
*lending* method declares `lends` where a result type would go:

```text
public fn Slice[Element].get(self, index: UInt64) lends Option[Element]
```

The lent part is the caller's to use **for the rest of the statement**, not
to keep. Binding it to a name is an error, whose fix copies the part:

```text
main.truss:2:7: error[ownership.lent_part_escapes]: This part is lent only until the statement ends, so it cannot be bound to a name. Use it in this statement, or copy it.
  |   let first = names.get(0)
  |       ^^^^^
  fix: Copy the scrutinee.
    insert ".copy()" at main.truss:2:27
1 error. `truss check --fix` fixes it.
```

Use the part within the statement, or copy it:

```truss
fn first_name(names: Slice[String]) -> Option[String] {
  names.get(0).map(fn(name) { name.copy() })
}

fn count_of(counts: Map[String, UInt64], word: String) -> UInt64 {
  if counts.get(word) is Some(count) {
    count
  } else {
    0
  }
}

test "using lent parts" {
  assert first_name(["Ada", "Grace"]) == Some("Ada")
  assert count_of(["the": 3], word: "the") == 3
}
```

A `Plain` part, such as the `UInt64` in `count_of`, can be bound, because
binding it copies it. Indexing a place, as in `names[0]`, gives a place, not
a lent part, so `let first = names[0]` binds a view of the element.

### Moving out of a place

A field can be moved out of a value with `own`, and the value is whole again
once the field is given a new value. A `mut` parameter can be moved out of
the same way, as long as it is given a value again before the function
returns. `Option.take` is written this way, and leaves `None` behind:

```truss
fn take_first(names: mut List[String]) -> Option[String] {
  if names.is_empty() {
    return None
  }
  Some(mut names.remove_at(0))
}

test "taking a value leaves something behind" {
  var slot = Some("draft")
  let taken = mut slot.take()
  assert taken == Some("draft")
  assert slot == None
  var names = ["Ada", "Grace"]
  assert take_first(mut names) == Some("Ada")
  assert names == ["Grace"]
}
```

A pattern binds views of the scrutinee's fields, so a `match` cannot move a
field out of its scrutinee. `match own` moves the scrutinee into the `match`
instead, and each binding owns its field:

```truss
type Entry =
  | Empty
  | Named(name: String, count: UInt64)

fn into_name(entry: own Entry) -> Option[String] {
  match own entry {
    Empty => None
    Named(name, ..) => Some(own name)
  }
}

test "a match moves fields out of an owned scrutinee" {
  assert into_name(Entry.Named(name: "Ada", count: 1)) == Some("Ada")
  assert into_name(Entry.Empty) == None
}
```

Without `own`, `name` is a view of `entry`, and `Some(own name)` is an error.
`is` and `let ... else` take `own` the same way, as in `if own entry is
Named(name, ..)`.

### Temporaries

A temporary is dropped at the end of its statement, unless a `let` keeps
it. `let middle = make_list()[1..4]` keeps the list as long as `middle` can
be used, because `middle` views it.

### Why ownership works this way

| Bug | What prevents it |
|---|---|
| A function changes a list its caller still reads | Only a `mut` argument can change, and the call says `mut` |
| Use after free | A value is freed only when its one owner is done with it, and no view outlives it |
| A dangling pointer into a grown list | A list cannot change while a view of it is live |
| A data race | Parallel branches cannot share a value that one of them mutates ([Chapter 14](#14-parallelism-and-concurrency)) |
| A hidden expensive copy | A non-`Plain` value copies only where `copy()` is written |

## 5. Records and Sum Types

Truss has two ways to define a type. A *record* has named fields, like a
struct. A *sum type* has variants, each of which may carry fields, like an
enum with data. Together they replace classes, structs, enums, tuples, and
null.

### Records

```truss
type Rectangle(width: UInt64, height: UInt64)
  derives Equal

test "building and reading a record" {
  let frame = Rectangle(width: 30, height: 50)
  assert frame.width == 30
  let wide = frame with (width: 60)
  assert wide == Rectangle(width: 60, height: 50)
  assert frame.width == 30
}
```

- A record is built the way a function is called, with each field labeled.
  The labels can come in any order.
- `frame.width` reads a field.
- `frame with (width: 60)` makes a new value with some fields replaced. The
  original does not change.
- `derives Equal` gives the type `==`. Without it, two rectangles cannot be
  compared. [Chapter 9](#deriving) lists the traits a type can derive.

A field can have a default, as a parameter can, and a type can have
constants of its own:

```truss
type Config(retries: UInt64 = 3, verbose: Bool = false)
  derives Equal

let Config.quiet: Config = Config(retries: 0)

test "defaults and type constants" {
  assert Config() == Config(retries: 3, verbose: false)
  assert Config(verbose: true).retries == 3
  assert Config.quiet.retries == 0
}
```

A record with one field takes a bare value, `UserId(7)`. Such a record is a
new type, not another name for its field's type: a `UserId` cannot be passed
where a `UInt64` is expected, which keeps IDs and counts apart.

```truss
type UserId(number: UInt64)
  derives Equal

test "a record of one field is a type of its own" {
  assert UserId(7) == UserId(number: 7)
}
```

A record pattern takes a value apart by field name. A bare name binds the
field of that name:

```truss
type Point(x: Int64, y: Int64)

fn sum(point: Point) -> Int64 {
  let (x, y) = point
  x.saturating_add(y)
}

test "a record pattern" {
  assert sum(Point(x: 1, y: 2)) == 3
}
```

A *tuple type* is a record whose field order is part of the type. A list of
patterns without parentheses, after `let`, `var`, or `for`, matches its
fields by position, so each binding takes the name you choose:

```truss
tuple type Span(start: UInt64, end: UInt64)

fn width(span: Span) -> UInt64
  requires span.start <= span.end
{
  let low, high = span
  high - low
}

test "a tuple pattern" {
  assert width(Span(start: 2, end: 7)) == 5
}
```

- In parentheses, fields match by name in every record, so
  `let (start, end) = span` works and `let (low, high) = span` is an error.
- A name that belongs to another field is an error: `let end, start = span`
  would bind `end` to the field `start`.
- A map's entries, `enumerate`, and `zip` give tuple types, so a loop over
  them names the parts by position ([Chapter 7](#7-collections)).

### Methods

A method is a function whose name is its type's name, a dot, and its own
name:

```truss
type Rectangle(width: UInt64, height: UInt64)
  derives Equal

fn Rectangle.square(size: UInt64) -> Rectangle {
  Rectangle(width: size, height: size)
}

fn Rectangle.area(self) -> UInt64 {
  self.width.saturating_multiply(self.height)
}

fn Rectangle.can_hold(self, other: Rectangle) -> Bool {
  self.width > other.width && self.height > other.height
}

fn Rectangle.double_width(mut self) {
  self.width = self.width.saturating_multiply(2)
}

test "methods" {
  var frame = Rectangle(width: 30, height: 50)
  assert frame.area() == 1500
  assert frame.can_hold(Rectangle.square(10))
  mut frame.double_width()
  assert frame.width == 60
  assert Rectangle.area(frame) == 3000
}
```

- A method whose first parameter is `self` is called on a value:
  `frame.area()`. `self` takes a mode as any parameter does: `self`,
  `mut self`, or `own self`.
- A method without `self`, such as `Rectangle.square`, is called on the
  type. It is how Truss writes a constructor.
- Every method can also be called through its type's name, as
  `Rectangle.area(frame)`.
- A method is defined in its type's package. You cannot add methods to a
  type from another package; to extend one, write a function, or implement a
  trait ([Chapter 9](#9-generics-traits-and-laws)).

A method can have up to three overloads that differ only in the mode of
`self`. The mode written at the call site picks one, as `filter` on a list
copies the elements it keeps when called on a view, and moves them when
called on an owned list.

### Sum types

A sum type lists its variants:

```truss
type Message =
  | Quit
  | Move(x: Int64, y: Int64)
  | Write(text: String)
  | ChangeColor(red: UInt8, green: UInt8, blue: UInt8)

fn Message.describe(self) -> String {
  match self {
    Quit => "quit"
    Move(x, y) => "move to ${x}, ${y}"
    Write(text) => "write ${text}"
    ChangeColor(red, green, blue) => "color ${red} ${green} ${blue}"
  }
}

test "a sum type" {
  let message = Message.Move(x: 3, y: -1)
  assert message.describe() == "move to 3, -1"
  assert Message.Quit.describe() == "quit"
}
```

In an expression, a variant is written under its type, `Message.Move`. In a
pattern, it is written alone, `Move(x, y)`, because the compiler looks it up
in the type of the value being matched.

#### Recursive types

A type that contains itself marks the recursive variant `indirect`, which
keeps its fields on the heap:

```truss
type Expression =
  | Number(value: Int64)
  | indirect Sum(left: Expression, right: Expression)
  | indirect Product(left: Expression, right: Expression)

fn Expression.evaluate(self) -> Option[Int64] {
  match self {
    Number(value) => Some(value)
    Sum(left, right) => left.evaluate()?.checked_add(right.evaluate()?)
    Product(left, right) => left.evaluate()?.checked_multiply(right.evaluate()?)
  }
}

test "evaluating an expression tree" {
  let tree = Expression.Sum(
    left: Expression.Number(2),
    right: Expression.Product(left: Expression.Number(3), right: Expression.Number(4)),
  )
  assert tree.evaluate() == Some(14)
}
```

`?` after an `Option` returns `None` from the function when the value is
`None`, and otherwise takes the value out. [Chapter 8](#8-error-handling)
covers it with `Result`.

### Option and Result

Truss has no null. A value that may be missing is an `Option`, and an
operation that may fail returns a `Result`. Both are sum types from the
prelude:

```text
type Option[Value] = Some(value: Value) | None
type Result[Value, Error] = Ok(value: Value) | Err(error: Error)
```

Their variants are written bare: `Some(3)`, `None`, `Ok(value)`, `Err(error)`.
Both have many methods, which `truss show Option` and `truss show Result`
list:

```truss
fn parse_port(text: StringSlice) -> Option[UInt16] {
  UInt16.parse(text).ok()
}

test "working with options" {
  assert parse_port("8080") == Some(8080)
  assert parse_port("eighty") == None
  assert parse_port("eighty").unwrap_or(80) == 80
  assert parse_port("443").map(fn(port) { port == 443 }) == Some(true)
  assert parse_port("80").is_some()
}
```

### Pattern matching

A `match` compares a value against patterns, one arm at a time:

```truss
fn status_text(code: UInt16) -> String {
  match code {
    200 => "ok"
    301 | 302 | 307 => "redirect"
    400..=499 => "client error"
    500..=599 => "server error"
    _ => "other"
  }
}

fn classify(left: Int64, right: Int64) -> String {
  match left, right {
    0, 0 => "both zero"
    0, _ => "one zero"
    _, 0 => "one zero"
    x, y if x == y => "equal"
    _, _ => "different"
  }
}

test "patterns" {
  assert status_text(302) == "redirect"
  assert status_text(503) == "server error"
  assert classify(0, right: 4) == "one zero"
  assert classify(3, right: 3) == "equal"
}
```

| Pattern | Matches |
|---|---|
| `_` | Anything, and binds nothing |
| `name` | Anything, and binds it to `name` |
| `200`, `true`, `"text"` | That literal |
| `400..=499` | An integer or character in the range |
| `301 \| 302` | Either pattern; both bind the same names |
| `Some(value)`, `Move(x, y)` | That variant, binding its fields by name |
| `Move(x: 0, ..)` | That variant with `x` equal to 0; `..` skips the other fields |
| `(x, y)` | A record, binding its fields `x` and `y` |
| `http::ok`, `Status.teapot` | A constant, written with its module or its type |
| `pattern if condition` | The pattern, when the guard is also true |

`match left, right` matches two values at once, one pattern for each in
every arm.

**A bare name in a pattern always binds a variable.** A constant in a
pattern is written with its module or its type, so adding a constant to a
module never changes what a pattern means. Writing a constant of the root
module bare, in a package named `lottery`, binds a new variable instead, and
the compiler says how to match the constant:

```text
main.truss:1:5: warning[usage.unused_constant]: Nothing in `lottery` uses the private constant `lottery::lucky`. Delete it.
  | let lucky: Int64 = 7
  |     ^^^^^
main.truss:5:5: error[usage.unused_variable]: `lucky` is never used. A bare name in a pattern binds a variable, which matches every value. To match the constant, write `lottery::lucky`.
  |     lucky => "lucky"
  |     ^^^^^
  fix: Write `lottery::lucky`.
    replace "lucky" with "lottery::lucky" at main.truss:5:5
  fix: Write `_`.
    replace "lucky" with "_" at main.truss:5:5
main.truss:6:5: error[patterns.unreachable_arm]: Earlier arms already match everything this arm matches, so it is never reached. `lucky` in an earlier arm binds a variable, which matches every value. To match the constant, write `lottery::lucky`.
  |     _ => "plain"
  |     ^^^^^^^^^^^^
  fix: Write `lottery::lucky`.
    replace "lucky" with "lottery::lucky" at main.truss:5:5
2 errors and 1 warning. `truss check --fix` fixes 1 of them.
```

A constant of a type, such as `Config.quiet`, is written with its type, as
in `Config.quiet => ...`.

The compiler checks two things about every `match`. It covers every case,
and every arm can be reached:

```text
main.truss:7:3: error[patterns.not_covered]: This `match` does not cover every case: `Empty` is not covered.
  |   match shape {
  |   ^^^^^^^^^^^^^
  fix: Add an arm for each missing case.
    insert "\n    Empty => todo" at main.truss:9:32
1 error. `truss check --fix` fixes it.
```

```text
main.truss:4:5: error[patterns.unreachable_arm]: Earlier arms already match everything this arm matches, so it is never reached.
  |     0 => "none"
  |     ^^^^^^^^^^^
  fix: Delete the arm.
    delete "\n    0 => \"none\"" at main.truss:3:15
1 error. `truss check --fix` fixes it.
```

#### is

`value is pattern` is `true` when the value matches. The names the pattern
binds can be used where the test is known to be true: later in an `&&`
chain, and in the block of the `if` or `while`:

```truss
use standard::console

fn first_long_word(words: Slice[String]) -> Option[UInt64] {
  if words.get(0) is Some(word) && word.length() > 3 {
    return Some(word.length())
  }
  None
}

fn count_lines() -> UInt64
  uses Console, RunForever
{
  var count: UInt64 = 0
  while Console.read_line() is Some(_) {
    count = count.saturating_add(1)
  }
  count
}

test "is" uses RunForever {
  assert first_long_word(["truss", "go"]) == Some(5)
  var screen = console::CapturedConsole.new(input: ["first", "second"])
  let count = provide mut screen {
    count_lines()
  }
  assert count == 2
}
```

`count_lines` reads until the input ends, which nothing guarantees will
happen, so it declares `uses RunForever`, and so does its test.

#### let else

`let pattern = value else { ... }` binds the pattern's names for the rest of
the block, and runs the `else` block when the value does not match. The
`else` block cannot continue: it returns, breaks, continues, or stops the
program.

```truss
fn double_first(numbers: Slice[Int64]) -> Option[Int64] {
  let Some(first) = numbers.get(0) else {
    return None
  }
  first.checked_multiply(2)
}

test "let else" {
  assert double_first([21]) == Some(42)
  assert double_first([]) == None
}
```

A pattern in a plain `let`, a `var`, a `for`, or a lambda's parameters
matches every value of its type, as `let (x, y) = point` did. For a pattern
that can fail, use `match`, `is`, or `let ... else`.

## 6. Packages and Modules

As a program grows, you split it into modules, and modules into packages:

| Unit | What it is |
|---|---|
| Module | A directory of `.truss` files that share one namespace |
| Package | A directory with a `truss.toml` manifest, and every module under it |
| Project | A set of packages that are built together |

### Modules

**Each directory of a package that holds `.truss` files is a module.** The
files beside the manifest are the package's *root module*, which has the
package's name. A subdirectory is a module whose path adds the directory's
name:

```text
geometry/
  truss.toml
  point.truss              module geometry
  measure/
    distance.truss         module geometry::measure
```

**The files of a module share one namespace.** A function in `point.truss`
can call one in another file of the same directory by its name alone, and a
file's name says nothing about what it holds. Moving a definition to another
file of its module changes nothing.

`point.truss`:

```truss
public type Point(x: Int64, y: Int64)
  derives Equal

public fn origin() -> Point {
  Point(x: 0, y: 0)
}

public fn report(point: Point)
  uses Console
{
  Console.print_line("(${point.x}, ${point.y})")
}
```

`measure/distance.truss`:

```truss
use geometry

public fn manhattan(from: geometry::Point, to: geometry::Point) -> Int64 {
  span(from.x, second: to.x).saturating_add(span(from.y, second: to.y))
}

fn span(first: Int64, second: Int64) -> Int64 {
  if first > second {
    first.saturating_subtract(second)
  } else {
    second.saturating_subtract(first)
  }
}
```

### Paths and use

`use` imports a module, never a single name. After `use geometry::measure`,
code writes `measure::manhattan`. The module's last name stays on every name
from it, so a reader always sees where a name comes from.

- Every path starts with a package's name, even inside that package. Truss
  has no relative paths such as `super` or `self::`.
- A full path works without a `use`: `geometry::measure::manhattan(...)`.
- There are no import aliases, and importing two modules with the same last
  name is an error.
- An unused `use` is an error, with a fix that deletes it.
- The modules of a package may use each other in a cycle.

The *prelude* is in scope everywhere with no `use`. It holds the built-in
types, `Option`, `Result`, `List`, `Slice`, `Map`, `Set`, `String`,
`StringSlice`, `ExitCode`, `Path`, the core traits such as `Equal` and
`Ordered`, and the standard capabilities such as `Console`. No definition can
take a prelude name.

### Visibility

A definition is visible only within its module unless it says otherwise:

| Keyword | Visible to |
|---|---|
| *(none)* | Its own module: every file of its directory |
| `internal` | Its whole package |
| `public` | Every package |
| `public opaque` | Every package, which can name the type but cannot see, build, or match its fields |

`span` above has no keyword, so only `geometry::measure` can call it. Using
a private definition from elsewhere is an error:

```text
app/main.truss:8:54: error[resolve.not_visible]: `geometry::origin` is private to its module, so it cannot be used here.
  |   Console.print_line("${measure::manhattan(geometry::origin(), to: corner)}")
  |                                                      ^^^^^^
geometry/point.truss:4:4: warning[usage.unused_function]: Nothing in `geometry` uses the private function `geometry::origin`. Delete it.
  | fn origin() -> Point {
  |    ^^^^^^
1 error and 1 warning
```

The warning comes with it: a private definition that nothing in its package
uses is dead code.

An *opaque* type hides its representation outside its package, so the
package can change the representation without breaking anyone. Other
packages build such a type only through its public functions:

```text
app/main.truss:7:16: error[types.private_field]: `Point` is opaque, so only its own package can build it.
  |   let corner = geometry::Point(x: 3, y: 4)
  |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^
1 error
```

A public signature cannot mention a private or internal type, since a
caller could not name it.

### Packages

A package's manifest, `truss.toml`, names it and lists the packages it
depends on:

```toml
[package]
name = "app"
truss = "0.1"

[dependencies]
geometry = ["Console"]
```

- A package's name is `lower_snake_case`, or an owner and a name joined by
  `::`, such as `acme::geometry`. A package is published to the registry
  under an owner.
- A package whose root module has a `main` is a program. One without is a
  library.
- The standard library, `standard`, is in no manifest: every package may
  use it.

#### Grants

Each dependency lists the capabilities it is granted. `geometry = []`
grants none: then `geometry` can only compute, and calling any of its
functions that prints, reads files, or uses the network is an error. This is
how Truss stops a dependency from doing more than you expect:

```text
app/main.truss:9:3: error[capabilities.not_granted]: `geometry::report` uses `Console`, which the manifest does not grant `geometry`. To grant it, add "Console" to the entry for `geometry` in `truss.toml`.
  |   geometry::report(corner)
  |   ^^^^^^^^^^^^^^^^^^^^^^^^
```

The compiler checks grants at signatures, so a dependency cannot gain a
capability by any route: calling it, passing its function as a value, or
providing one of its types. No tool ever widens a grant for you.

A dependency the package never uses is an error, as an unused `use` is.

### Projects

A manifest with a `[project]` table makes its directory a *project*. Every
package under it is built together, and one package depends on another by
its name:

```text
workshop/
  truss.toml               [project]
  geometry/
    truss.toml             [package] name = "geometry"
    point.truss
    measure/
      distance.truss
  app/
    truss.toml             [package] name = "app", depends on geometry
    main.truss
```

`app/main.truss`:

```truss
use geometry
use geometry::measure

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  let corner = geometry::Point(x: 3, y: 4)
  Console.print_line("${measure::manhattan(geometry::origin(), to: corner)}")
  geometry::report(corner)
  ExitCode.success
}
```

```text
$ truss check
$ cd app
$ truss run
7
(3, 4)
```

`truss check` in the project's directory checks every package of the
project. A project's manifest can also set how long each test may run:

```toml
[project]

[test]
time_limit = 10
```

A package that is not inside a project is a project of its own, as every
package in the earlier chapters was.

### The registry

Packages from the registry are named with their owner, as in
`acme::geometry`. `truss add acme::geometry` adds one to the manifest, with
no capabilities granted, and records its version in the project's lock
file, `truss.lock`. `truss upgrade` moves to newer versions, and `truss
publish 1.4.2` publishes a package that is finished, as version 1.4.2: no
errors, every proof done, no `todo`, and every deterministic test passing.

Every release under one name is compatible with the ones before it, which its
author promises: a public definition stays at its path, a `requires` gets no
stronger, an `ensures` no weaker, and a cost no greater. An incompatible
change is a new package, named with `_v2` after the old name, so both
versions can be used in one build. [PACKAGES.md](PACKAGES.md) defines packages, versions, and the
registry in full.

## 7. Collections

The prelude has four collections, `List`, `Map`, `Set`, and `String`, and
the views `Slice` and `StringSlice`. The standard library's `collections`
module has more.

### Lists

A `List` is a growable sequence of elements of one type. A `Slice` is a view
of a run of a list's elements, and every read-only method of a slice works
on a list.

```truss
test "building a list" {
  var numbers = [5, 3, 8]
  mut numbers.push(1)
  mut numbers.insert_at(0, item: 9)
  assert numbers == [9, 5, 3, 8, 1]
  assert mut numbers.remove_at(1) == 5
  assert mut numbers.pop() == Some(1)
  assert numbers.length() == 3
  let zeros = List.filled(0, count: 3)
  assert zeros == [0, 0, 0]
  var names: List[String] = []
  assert names.is_empty()
  mut names.push("Ada")
  assert names.length() == 1
}
```

An empty literal does not say what it holds, so its `let` or `var` states the
type:

```text
main.truss:2:3: error[types.cannot_infer]: The types in this statement cannot be inferred from it alone. Give the `let` a type, or the call type arguments, such as `var names: List[String] = []`.
  |   var names = []
  |   ^^^^^^^^^^^^^^
1 error
```

#### Reading elements

```truss
fn second(numbers: Slice[Int64]) -> Option[Int64] {
  if numbers.length() < 2 {
    return None
  }
  Some(numbers[1])
}

test "reading elements" {
  let numbers = [9, 3, 8]
  assert second(numbers) == Some(3)
  assert numbers.get(5) == None
  assert numbers.contains(8)
  assert numbers.index_of(3) == Some(1)
  assert numbers.sorted() == [3, 8, 9]
  assert numbers.join(", ") == "9, 3, 8"
  assert numbers[1..] == [3, 8]
}
```

- `numbers[1]` reads an element, and **the compiler proves the index is in
  bounds.** In `second`, the `if` above establishes it. When no fact shows
  that an index is in bounds, check it first with an `if`, or read the
  element with `get`, which returns `None` for an index out of bounds.
- `numbers[1..3]` is a slice of the elements at 1 and 2. A slice's bounds are
  proven too. `numbers[..2]` and `numbers[1..]` leave out an end.
- `truss show List` lists every method of a list, including those of its
  view `Slice`.

#### Changing elements

```truss
fn double_each(numbers: mut List[Int64]) {
  for number in mut numbers {
    number = number.saturating_multiply(2)
  }
}

test "changing elements" {
  var numbers = [3, 1, 2]
  mut numbers.sort()
  assert numbers == [1, 2, 3]
  double_each(mut numbers)
  assert numbers == [2, 4, 6]
  numbers[0] = 10
  assert numbers == [10, 4, 6]
}
```

#### Iterating

| Loop | Each iteration |
|---|---|
| `for item in items` | Reads an element, as a view |
| `for item in mut items` | Changes an element in place |
| `for item in own items` | Takes an element, moving it out of the list |
| `for index, item in items.enumerate()` | Reads each element with its position |
| `for item in items.reversed()` | Reads the elements from the last to the first |

```truss
fn longest(names: own List[String]) -> String {
  var best = ""
  for name in own names {
    if name.length() > best.length() {
      best = own name
    }
  }
  best
}

test "iterating" {
  let numbers = [7, 8, 9]
  var positions: List[UInt64] = []
  for index, _ in numbers.enumerate() {
    mut positions.push(index)
  }
  assert positions == [0, 1, 2]
  var backwards: List[Int64] = []
  for value in numbers.reversed() {
    mut backwards.push(value)
  }
  assert backwards == [9, 8, 7]
  assert longest(["Ada", "Grace", "Alan"]) == "Grace"
}
```

A `mut` loop changes elements but never adds or removes them, so the loop
always visits each position once.

#### Transforming a list

A list, a slice, an array, a range, and a map are *iterable*: each
implements the prelude trait `Iterable`, which gives them methods that
transform every element at once:

```truss
fn evens(numbers: Slice[Int64]) -> List[Int64] {
  numbers.filter(fn(number) { number % 2 == 0 })
}

fn lengths(words: Slice[String]) -> List[UInt64] {
  words.map(fn(word) { word.length() })
}

fn parsed(texts: Slice[String]) -> List[Int64] {
  texts.filter_map(fn(text) { Int64.parse(text).ok() })
}

fn total_length(words: Slice[String]) -> UInt64 {
  words.fold[UInt64](0, combine: fn(total, word) { total.saturating_add(word.length()) })
}

test "transforming" {
  assert evens([1, 2, 3, 4]) == [2, 4]
  assert lengths(["a", "abc"]) == [1, 3]
  assert parsed(["1", "x", "3"]) == [1, 3]
  assert total_length(["ab", "cde"]) == 5
}
```

| Method | Result |
|---|---|
| `map(transform)` | A list of the transformed elements, as long as the original |
| `filter(keep)` | The elements for which `keep` returns `true` |
| `filter_map(transform)` | The `Some` values that `transform` returns |
| `flat_map(transform)` | The lists that `transform` returns, joined |
| `fold(initial, combine)` | One value, combined from each element in turn |

- `fn(number) { number % 2 == 0 }` is a lambda, a function written in place.
  [Chapter 10](#10-lambdas-and-function-types) covers lambdas.
- `fold[UInt64](0, ...)` gives the type argument because the literal `0`
  alone would be an `Int64`.
- **A lambda knows that its argument is an element of the collection,** and
  nothing more. In `numbers.map(fn(number) { number * 2 })`, the
  multiplication fits only where the caller's `requires` bounds every
  element. Otherwise use `saturating_multiply`.

### Strings

Truss has two text types:

| Type | What it is |
|---|---|
| `String` | Owned, growable UTF-8 text |
| `StringSlice` | A view of a `String`'s text |

A string literal is a `String`, or a `StringSlice` where one is expected. A
function that only reads text takes a `StringSlice`, and a `String` passes
to it as a view. A `String` and a `StringSlice` compare with `==` directly,
as a `List` and a `Slice` do. `viewed.to_string()` copies a `StringSlice`
into a new `String`, and `owned.slice()` views a whole `String`.

**A string literal is a constant,** so reading it and binding it with `let`
cost nothing: the `let` views the constant's text. Where an owned `String`
is needed, as in a `var`, an `own` argument, or a returned value, the
literal is copied:

```truss
fn keep(text: own String) -> String {
  text
}

test "a literal is copied where a String is owned" {
  let name = "Ada"
  assert keep(name.copy()) == "Ada"
  assert keep("Grace") == "Grace"
  var greeting = "Hello"
  mut greeting.push(", world")
  assert keep(own greeting) == "Hello, world"
}
```

A `let` of a literal is a view, so it cannot be moved. With
`keep(own name)` in place of `keep(name.copy())`:

```text
main.truss:7:19: error[ownership.not_owned]: `name` views a string literal, so it cannot be moved: its new owner would free the literal's static buffer. Copy it instead.
  |   assert keep(own name) == "Ada"
  |                   ^^^^
  fix: Copy it.
    delete "own " at main.truss:7:15
    insert ".copy()" at main.truss:7:23
1 error. `truss check --fix` fixes it.
```

#### Building text

Strings have no `+` operator. Build text with interpolation, or by pushing
onto a `var`:

```truss
fn label(name: StringSlice, count: UInt64) -> String {
  var text = "${name}: "
  mut text.push("${count}")
  mut text.push_character(Character"!")
  text
}

test "building text" {
  assert label("apples", count: 3) == "apples: 3!"
}
```

A literal has the escapes `\n`, `\t`, `\r`, `\0`, `\\`, `\"`, `\${` for the
text `${`, and `\u{e9}` for a code point. A raw string, opened and closed
with three quotes, has no escapes. When it spans lines, its indentation is
removed:

```truss
test "raw strings" {
  let poem = """
    roses are red
    violets are blue
    """
  assert poem.lines().length() == 2
  assert """C:\path\to""".length() == 10
}
```

#### Taking text apart

```truss
test "taking text apart" {
  assert "a,b,c".split(",").length() == 3
  assert "  padded  ".trim() == "padded"
  assert "two words".split_whitespace().length() == 2
  assert "hello".replace("l", replacement: "L") == "heLLo"
  assert "truss".to_uppercase() == "TRUSS"
  assert "prefix-name".strip_prefix("prefix-") == Some("name")
  assert "needle in a haystack".find("in") == Some(7)
  assert "ab".repeated(3) == "ababab"
  assert "naïve".length() == 6
  assert "naïve".character_count() == 5
}
```

**A string's `length` is its size in bytes.** `ï` takes two bytes in UTF-8,
so `"naïve"` has length 6 and five characters. Strings cannot be indexed,
because an index could fall in the middle of a character:

```text
main.truss:2:3: error[types.not_indexable]: Strings cannot be indexed: say which you mean with `bytes()` or `characters()`.
  |   text[0]
  |   ^^^^^^^
1 error
```

`characters()` gives the characters one at a time, `bytes()` gives the
bytes, and `graphemes()` gives the units a reader sees as one character.
`truss show StringSlice` lists the rest.

#### Parsing

Every integer and float type has `parse`, which returns a `Result`:

```truss
test "parsing" {
  assert Int64.parse("-42") == Ok(-42)
  assert UInt8.parse("300").is_err()
  assert Float64.parse("2.5") == Ok(2.5)
}
```

### Maps

A `Map` associates keys with values. Its iteration order is the order in
which keys were first inserted, so a program that walks a map gives the same
output every run.

```truss
fn count_words(text: StringSlice) -> Map[String, UInt64] {
  var counts: Map[String, UInt64] = [:]
  for word in text.split_whitespace() {
    mut counts.update(word.to_string(), default: 0, change: fn(count) {
      count = count.saturating_add(1)
    })
  }
  counts
}

fn group_by_lowercase(words: Slice[String]) -> Map[String, List[String]] {
  var groups: Map[String, List[String]] = [:]
  for word in words {
    let key = word.to_lowercase()
    mut groups.get_or_insert(own key, default: []).push(word.copy())
  }
  groups
}

test "maps" {
  var ports = ["http": 80, "https": 443]
  assert ports.get("https") == Some(443)
  assert ports.get("ftp") == None
  ports["ssh"] = 22
  assert ports.contains("ssh")
  mut ports.remove("http")
  assert ports.length() == 2
  var names: List[String] = []
  for name, port in ports {
    if port > 100 {
      mut names.push(name.copy())
    }
  }
  assert names == ["https"]
  let counts = count_words("the cat saw the dog")
  assert counts.get("the") == Some(2)
  assert group_by_lowercase(["Ab", "ab", "c"]).get("ab") == Some(["Ab", "ab"])
}
```

- `[:]` is an empty map, and `["http": 80]` a map literal.
- `ports["ssh"] = 22` inserts a key or replaces its value. `ports[key]`
  reads a value, and the compiler proves the key is present; `get` returns
  an `Option`.
- `update` changes the value for a key in place, inserting the default
  first when the key is missing. Its lambda takes the value `mut`. Nothing
  bounds how often a word repeats, so the count saturates rather than
  overflowing.
- `get_or_insert` also inserts the default when the key is missing, then
  lends the value `mut` for the rest of the statement. `group_by_lowercase`
  pushes onto each key's list this way, with no index into a separate list.
  The key is stored in the map, so `key`, a place, is passed `own`; a
  temporary such as `word.to_lowercase()` written in the call would need no
  `own`.
- A `for` loop over a map visits its entries. Their type, `map::Entry`, is a
  tuple type, so `name, port` binds each key and value. `ports.keys()` and
  `ports.values()` visit one of the two.

A key type implements `Hash` and `Ordered`, which a record or sum type
derives. A type without them cannot be a key:

```text
main.truss:3:16: error[types.unsatisfied_bound]: `Map[Point, UInt64]` needs `Point: Hash`, which does not hold here.
  | fn visits() -> Map[Point, UInt64] {
  |                ^^^^^^^^^^^^^^^^^^
```

`derives Equal, Hash, Ordered` on `Point` makes it a key type.

### Sets

A `Set` holds distinct elements, in the order they were inserted:

```truss
test "sets" {
  var seen: Set[Int64] = [1, 2]
  mut seen.insert(3)
  assert seen.contains(3)
  mut seen.remove(1)
  assert !seen.contains(1)
  assert seen.length() == 2
}
```

A set literal is written like a list literal, where a `Set` is expected.
Inserting an element twice keeps one.

### More collections

`standard::collections` holds the rest:

| Type | Holds |
|---|---|
| `Deque` | A queue that adds and removes at both ends |
| `Heap` | A priority queue |
| `SortedMap`, `SortedSet` | A map and a set in the order of their keys |
| `BitSet` | A set of small unsigned integers, one bit each |
| `LruCache` | A map of bounded size that drops the least recently used entry |

```truss
use standard::collections

test "a deque" {
  var queue: collections::Deque[String] = []
  mut queue.push_back("first")
  mut queue.push_back("second")
  mut queue.push_front("zeroth")
  assert mut queue.pop_front() == Some("zeroth")
  assert queue.length() == 2
}
```

## 8. Error Handling

Truss has no exceptions. An operation that can fail in a way the caller
should handle returns a `Result`, and the type system makes sure the caller
handles it. An operation that would be a bug, such as an overflow or an
index out of bounds, is either proven impossible or declared with
`uses Panic`.

### Recoverable errors with Result

A function that can fail returns `Result[Value, Error]`. Its error type is
usually a sum type of its own, with a variant for each way it can fail:

```truss
type SettingError =
  | MissingEquals(line: String)
  | BadNumber(name: String, text: String)
  derives Equal

impl Display for SettingError {
  fn display(self, output: mut String) {
    match self {
      MissingEquals(line) => mut output.push("no `=` in `${line}`")
      BadNumber(name, text) => mut output.push("`${name}` is not a number: `${text}`")
    }
  }
}

type Setting(name: String, value: UInt64)
  derives Equal

fn parse_setting(line: StringSlice) -> Result[Setting, SettingError] {
  let parts = line.split_at_most("=", parts: 2)
  if parts.length() != 2 {
    return Err(SettingError.MissingEquals(line.to_string()))
  }
  let name = parts[0].trim()
  let text = parts[1].trim()
  let value = UInt64.parse(text).map_error(fn(_) {
    SettingError.BadNumber(name: name.to_string(), text: text.to_string())
  })?
  Ok(Setting(name: name.to_string(), value))
}

fn parse_settings(text: StringSlice) -> Result[List[Setting], SettingError] {
  var settings: List[Setting] = []
  for line in text.lines() {
    if line.trim().is_empty() {
      continue
    }
    mut settings.push(parse_setting(line)?)
  }
  Ok(own settings)
}

test "settings parse one per line" {
  let parsed = parse_settings("retries = 3\n\ntimeout = 30")
  assert parsed == Ok([Setting(name: "retries", value: 3), Setting(name: "timeout", value: 30)])
}

test "a line without an equals sign is an error" {
  assert parse_settings("retries") == Err(SettingError.MissingEquals("retries"))
}

fn main(arguments: List[String]) -> ExitCode
  uses Console
{
  match parse_settings("retries = 3\ntimeout = thirty") {
    Ok(settings) => {
      for setting in settings {
        Console.print_line("${setting.name} is ${setting.value}")
      }
      ExitCode.success
    }
    Err(error) => {
      Console.print_error("${error}")
      ExitCode.failure
    }
  }
}
```

```text
$ truss run
`timeout` is not a number: `thirty`
```

This example shows the parts of error handling in Truss:

- **The error type says how the function can fail.** A caller matches on
  `SettingError` and knows it has handled every case.
- **`impl Display for SettingError`** gives the error a message, so it can
  be interpolated, as `main` does. [Chapter 9](#9-generics-traits-and-laws)
  explains traits and `impl`.
- **`?` passes an error up.** After an expression of type `Result`, `?`
  returns the error from the enclosing function unchanged, and otherwise
  takes the value out of `Ok`. `parse_settings` uses it to stop at the first
  bad line.
- **`map_error` converts an error,** because `?` never converts. Applying
  `?` to `UInt16.parse` in a function that returns a `ConfigError` is an
  error:

  ```text
  main.truss:4:14: error[types.wrong_try]: `?` returns the error unchanged, so it needs the function's error type `ConfigError`, not `ParseIntegerError`. Convert it first with `map_error`.
    |   let port = UInt16.parse(text)?
    |              ^^^^^^^^^^^^^^^^^^^
  1 error
  ```

- **`Ok(own settings)` moves the list into the result.** A variant's field
  is owned, as [Chapter 4](#moving) says, so a place there is moved or
  copied.
- **`main` handles the error at the top,** printing it to standard error with
  `Console.print_error` and exiting with `ExitCode.failure`.

`?` works on `Option` too, in a function that returns an `Option`, and
`option.ok_or(error)` turns an `Option` into a `Result`. These methods
combine results without a `match`:

| Method | Result |
|---|---|
| `result.map(transform)` | `Ok` of the transformed value, or the same `Err` |
| `result.map_error(transform)` | The same `Ok`, or `Err` of the transformed error |
| `result.and_then(next)` | The `Result` that `next` returns from the value, or the same `Err` |
| `result.unwrap_or(fallback)` | The value, or `fallback` |
| `result.ok()` | `Some` of the value, or `None` |
| `result.is_ok()`, `result.is_err()` | Whether the result is `Ok` or `Err` |

### Operations that can fail

Some operations fail not because the input was bad but because the program
has a bug: an integer overflows, a divisor is zero, an index is out of
bounds, a slice runs past the end of its list, or a shift amount is at least
the width of its type. In Truss, **each of these is a proof obligation, in
every function and every test.** The compiler proves the operation is safe,
or the code is an error.

You saw the overflow in [Chapter 3](#integer-overflow). Wherever the
compiler cannot prove such an operation safe, one of three changes makes the
code compile:

| Approach | Example |
|---|---|
| Establish the fact locally, with an `if` | `if index < items.length() { items[index] } else { 0 }` |
| Require it of every caller, with `requires` | `requires divisor != 0` |
| Call a method that returns an `Option` or a `Result` | `items.get(index)`, `total.checked_add(item)` |

The third approach hands the failure back as a value, and the code decides
what to do with it, including stopping the program, as the next section
shows.

`unreachable` marks code that should never run. It is a proof obligation
too, and only the first approach meets it: you must show the point cannot be
reached.

```text
main.truss:2:24: error[prover.unreachable]: This `unreachable` may be reached. For example, when `flag` is false. On that path, `flag` is false.
  |   if flag { 1 } else { unreachable }
  |                        ^^^^^^^^^^^
1 error
```

### Unrecoverable errors with Panic

`Panic` is a capability, so **code stops the program only where its
signature declares `uses Panic`.** A caller can see from a signature that a
call may end the program, and a server that must keep running can require
handlers whose types have no `Panic`.

`uses Panic` permits a crash. An integer operation that fails stops the
program there, as in `add_or_stop` above. Indexing is still proven, so code
that should stop on a missing element writes the stop, with the checked
form of the operation:

```truss
fn third(items: Slice[Int64]) -> Int64
  uses Panic
{
  items.get(2).expect("the list holds at least three items")
}

fn parse_known_port(text: StringSlice) -> UInt16
  uses Panic
{
  UInt16.parse(text).expect("the port is a constant of this program")
}

fn checked_count(count: UInt64) -> UInt64
  uses Panic
{
  if count > 1000 {
    Panic.crash("more than a thousand items is a bug in the caller")
  }
  count
}

fn main(arguments: List[String]) -> ExitCode
  uses Console, Panic
{
  Console.print_line("${parse_known_port("8080")} ${checked_count(3)}")
  Console.print_line("${third([1, 2])}")
  ExitCode.success
}
```

```text
$ truss run
8080 3
panic: the list holds at least three items
  at standard/option/option.truss:239:13
  called at main.truss:4:3
  called at main.truss:26:25
$ echo $?
101
```

- **`expect(message)`** takes the value out of an `Option` or a `Result`,
  and stops the program when there is none. `third` writes
  `items.get(2).expect(...)` where `items[2]` would need a proof that the
  list is long enough.
- **`expect` declares `uses Panic unless self is Some(_)`.** A function that
  proves the value present calls `expect` without `uses Panic`. One that
  cannot declares `uses Panic`, as `third` does.
- **The standard library's other checked functions do the same.**
  `List.remove_at` declares `uses Panic unless index < self.length()`, and
  `Duration.seconds` that the count of nanoseconds fits an `Int64`. Code
  without `Panic` proves the condition, and code with `Panic` calls them
  as they are.
- **`Panic.crash(message)`** stops the program on purpose. The panic's
  message goes to standard error with where it happened and the chain of
  calls that led there, and the program exits with status 101.
- **A panic cannot be caught.** Code that caught one could go on with a
  value whose invariant was broken partway through an update. A program that
  must not stop proves that it cannot panic instead.
- **A test that calls code that may panic declares `uses Panic`**, as
  [Chapter 12](#12-writing-tests) shows.

### Choosing an approach

| Situation | Approach |
|---|---|
| The input comes from outside the program: a user, a file, the network | Return a `Result`, and say what went wrong |
| A value may be absent as a normal case | Return an `Option` |
| The caller can be expected to know the fact | `requires`, so every caller proves it |
| The code just checked the fact | Nothing: the prover knows it |
| A failure would be a bug, and proving otherwise is not worth it | `uses Panic`: an integer operation then stops the program, and `expect` does for a checked one |

`expect` is a fine choice for a script or a prototype. Code that others
depend on usually proves its operations safe, since `Panic` in a signature
spreads to every caller.

## 9. Generics, Traits, and Laws

Generics let one definition work for many types. Traits say what a type can
do, and laws say what must always be true of a trait's implementations.

### Generic functions

A function's type parameters go in brackets after its name. A *bound* after
a colon says what the type must support:

```truss
fn largest[Element: Ordered + Copyable](items: Slice[Element]) -> Option[Element] {
  var best: Option[Element] = None
  for item in items {
    if best is Some(current) && current >= item {
      continue
    }
    best = Some(item.copy())
  }
  best
}

test "one function for many types" {
  assert largest([3, 9, 4]) == Some(9)
  assert largest(["b", "c", "a"]) == Some("c")
  assert largest([0.5, 0.25]) == Some(0.5)
}
```

`Ordered` gives `largest` the comparison operators, and `Copyable` gives it
`copy()`. Inside the function, a value of type `Element` can do only what
its bounds allow. The compiler infers the type arguments at each call. Where
it cannot, a call writes them in brackets, as in
`List[String].with_capacity(8)`.

Generic code is *monomorphized*: it is compiled once for each set of type
arguments, so a generic function is as fast as one written for a single
type.

#### Value parameters

A lowercase type parameter is a `UInt64` known when the code is compiled. An
array's length is one:

```truss
fn sum_array[count: UInt64](values: Array[Int64, count]) -> Int64 {
  var total: Int64 = 0
  for value in values {
    total = total.saturating_add(value)
  }
  total
}

test "a value parameter" {
  let triple: Array[Int64, 3] = [1, 2, 3]
  assert sum_array(triple) == 6
}
```

### Generic types

A type takes parameters the same way, and a method states the bounds it
needs. The method exists only for the types that meet them:

```truss
type Pair[Value](first: Value, second: Value)
  derives Equal

fn Pair[Value: Ordered + Copyable].larger(self) -> Value {
  if self.first >= self.second { self.first.copy() } else { self.second.copy() }
}

test "a generic type" {
  assert Pair(first: 3, second: 8).larger() == 8
  assert Pair(first: "x", second: "y") == Pair(first: "x", second: "y")
}
```

`Pair[Value]` derives `Equal` only where `Value` has it.

### Traits

A trait declares methods that types implement. A method with a body is
*provided*: every implementation has it, and an implementation can replace
it.

```truss
trait Summary {
  fn headline(self) -> String

  fn summarize(self) -> String
  {
    "Read more: ${self.headline()}"
  }
}

type Article(title: String, author: String)
type Post(author: String, text: String)

impl Summary for Article {
  fn headline(self) -> String
  {
    "${self.title}, by ${self.author}"
  }
}

impl Summary for Post {
  fn headline(self) -> String
  {
    "@${self.author}"
  }

  fn summarize(self) -> String
  {
    "@${self.author}: ${self.text}"
  }
}

fn announce[Item: Summary](item: Item) -> String {
  "New! ${item.summarize()}"
}

test "traits" {
  let article = Article(title: "Truss 1.0", author: "Ada")
  assert announce(article) == "New! Read more: Truss 1.0, by Ada"
  assert announce(Post(author: "grace", text: "hi")) == "New! @grace: hi"
}
```

- `impl Summary for Article` implements the trait for a type. `Article`
  keeps the provided `summarize`, and `Post` replaces it.
- Every method terminates unless its trait's `uses` names `RunForever`, so
  neither the trait nor the `impl` writes anything about termination.
  [Chapter 13](#termination) explains termination.
- `announce[Item: Summary]` accepts any type that implements `Summary`.
- No trait is imported: calling `item.summarize()` finds the method through
  the type's `impl`s.

A trait can require others: `trait Ordered: Equal` means every `Ordered`
type is `Equal` first, and a bound of `Ordered` includes `Equal`.

#### Where an impl can live

An `impl` lives in the package of the trait, of the type, or of the
outermost type of one of the trait's arguments. Your package can implement
its own trait for `Int64`, or a standard trait for its own type, but not a
standard trait for a standard type. A type has at most one `impl` of each
trait, so two packages can never disagree about which one applies.

An `impl` for a generic type states its conditions on the type's
parameters:

```truss
type Pair[Value](first: Value, second: Value)

impl Display for Pair[Value: Display] {
  fn display(self, output: mut String) {
    mut output.push("(${self.first}, ${self.second})")
  }
}

test "a conditional impl" {
  assert "${Pair(first: 1, second: 2)}" == "(1, 2)"
}
```

### Standard traits

| Trait | Gives | Usually |
|---|---|---|
| `Equal` | `==` and `!=` | Derived |
| `Ordered` | `<`, `<=`, `>`, `>=`, `compare`, `max`, `min`, `clamp` | Derived |
| `Hash` | Use as a `Map` key or a `Set` element, with `Ordered` | Derived |
| `Default` | `Type.default()` | Derived |
| `Display` | Use in `"${...}"` | Written by hand |
| `From[Source]`, `TryFrom[Source]` | `Type.from(value)`, `Type.try_from(value)` | Written by hand |
| `Add[Right]`, `Subtract[Right]`, `Multiply[Right]`, `Divide[Right]`, `Remainder[Right]`, `Negate` | The arithmetic operators | Written by hand |
| `Index`, `IndexMut`, `IndexAssign` | `collection[key]` | Written by hand ([Chapter 15](#indexing-your-own-types)) |
| `Cursor` | Use in a `for` loop, one value at a time | Written by hand ([Chapter 15](#cursors)) |

`Copyable`, `Plain`, and `Storable` are traits too, but the compiler gives
them to a type from its fields, and no `impl` can.

#### Deriving

`derives` asks the compiler to write an implementation from the type's
fields:

```truss
use standard::json
use standard::serialization

type Settings(retries: UInt64 = 3, name: String = "default")
  derives Equal, Default

type Account(owner: String, balance: Int64)
  derives Equal, serialization::Serialize, serialization::Deserialize

test "derived implementations" uses RunForever {
  assert Settings.default() == Settings(retries: 3, name: "default")
  let account = Account(owner: "Ada", balance: 10)
  let text = json::encode(account)
  assert text == "{\"owner\":\"Ada\",\"balance\":10}"
  let decoded: Result[Account, json::Error] = json::decode(text)
  assert own decoded.ok() == Some(own account)
}
```

| Derived trait | Meaning |
|---|---|
| `Equal` | Equal variants with equal fields |
| `Ordered` | Variants in declaration order, then fields in declaration order |
| `Hash` | A hash of the fields |
| `Default` | Each field's default, or its type's `default()` |
| `serialization::Serialize`, `serialization::Deserialize` | The type's form in JSON, TOML, and the other formats of the standard library |

`json::decode` declares `uses RunForever`, so the test that calls it does
too.

A derived trait needs every field to have it, and `Ordered` and `Hash` need
a derived `Equal` too.

#### Display

`Display` is the trait that interpolation uses. Its one method pushes the
value's text onto a `String`:

```text
public trait Display {
  fn display(self, output: mut String)
}
```

[Chapter 8](#recoverable-errors-with-result) implemented it for an error
type. Every type also has *debug output*, which needs no trait:
[Chapter 12](#echo) shows it.

#### Operators

The arithmetic operators call traits. `a + b` calls `Add.add`, which uses
`Panic unless add_is_defined`, so a type of your own states where its
operation is defined, just as the integers do:

```truss
type Cents(amount: Int64)
  derives Equal, Hash, Ordered

impl Add[Cents] for Cents {
  type Output = Cents

  fn add_is_defined(self, right: Cents) -> Bool
    ensures result == (Int64.minimum <= self.amount + right.amount && self.amount + right.amount <= Int64.maximum)
    cost time O(1)
  {
    self.amount.checked_add(right.amount).is_some()
  }

  fn add(self, right: Cents) -> Cents
    uses Panic unless self.add_is_defined(right)
  {
    Cents(self.amount + right.amount)
  }
}

test "an operator of your own" {
  assert Cents(250) + Cents(100) == Cents(350)
  assert Cents(1) < Cents(2)
}
```

- `type Output = Cents` chooses the trait's *associated type*: each `impl`
  of `Add` picks the type its sums have.
- The `ensures` on `add_is_defined` tells callers exactly when the addition
  is defined, so the prover can show that `Cents(250) + Cents(100)` is. Code
  without `Panic` proves it, and code with `Panic` adds without a proof.
- `add` repeats the condition after its own `Panic unless`. Where the
  condition holds, the prover shows `self.amount + right.amount` fits.
  Where it fails, the `Int64` addition panics, since `add` has `Panic`.
  Arithmetic inside a contract is exact, so `self.amount + right.amount`
  there cannot overflow.
- `derives Ordered` gives `Cents` its comparisons.

### Associated types

An associated type is a type that each `impl` chooses. `Index`, which gives
`collection[key]` its meaning, has two:

```text
trait Index {
  type Key
  type Output
  fn contains_key(self, key: Self.Key) -> Bool
  fn at(self, key: Self.Key) lends Self.Output
    requires self.contains_key(key)
}
```

Generic code names an associated type through its parameter, as
`Collection.Key`, and a bound can fix one, as `Cursor[Element = Int64]`.

### Laws

A *law* is a fact that every implementation of a trait must satisfy. The
compiler proves it for each `impl`. `Equal`, for example, has the laws that
make `==` behave like equality:

```text
law reflexive(value: Self) {
  value == value
}

law symmetric(first: Self, second: Self)
  requires first == second
{
  second == first
}
```

A derived implementation satisfies its trait's laws. A hand-written one must
prove them, which is what keeps generic code honest: a `Map` can rely on
`==` being an equality because every key type's `impl` was proven to make it
one. A trait of your own can have laws:

```truss
trait Combine: Equal {
  fn empty() -> Self
  fn combine(self, other: Self) -> Self

  law left_identity(value: Self) {
    Self.empty().combine(value) == value
  }
}

type Maximum(value: Int64)
  derives Equal

impl Combine for Maximum {
  fn empty() -> Maximum
    ensures result.value == Int64.minimum
  {
    Maximum(Int64.minimum)
  }

  fn combine(self, other: Maximum) -> Maximum
    ensures result.value >= self.value && result.value >= other.value
    ensures result.value == self.value || result.value == other.value
  {
    if self.value >= other.value { self } else { other }
  }
}

fn combine_all[Item: Combine + Copyable](items: Slice[Item]) -> Item {
  var total = Item.empty()
  for item in items {
    total = total.combine(item.copy())
  }
  total
}

test "a trait with a law" {
  assert combine_all([Maximum(3), Maximum(7)]) == Maximum(7)
}
```

**A law is proven from the contracts of the `impl`'s methods, never from
their bodies.** Without the two `ensures` clauses on `combine`, the compiler
reports that the law may not hold, even though the body satisfies it:

```text
main.truss:13:1: error[prover.law]: The law `Combine.left_identity` may not hold for `Maximum`.
  | impl Combine for Maximum {
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^
1 error
```

This is a rule you will meet again in [Chapter 13](#13-contracts-and-proofs):
what other code may rely on is what a signature says.

When the prover cannot prove a law from the contracts alone, a *law proof*
gives the steps: `proof Combine.left_identity for Maximum { ... }`.
[Chapter 13](#theorems-and-proof-blocks) shows proofs.

### Dynamic dispatch with any

Generic code is compiled for each type. When one list must hold values of
different types, `any Trait` holds a value of any type that implements the
trait, and calls its methods through the trait:

```truss
trait Shape {
  fn area(self) -> Float64
}

type Square(side: Float64)
type Circle(radius: Float64)

impl Shape for Square {
  fn area(self) -> Float64
  {
    self.side * self.side
  }
}

impl Shape for Circle {
  fn area(self) -> Float64
  {
    3.14159 * self.radius * self.radius
  }
}

fn total_area(shapes: Slice[any Shape]) -> Float64 {
  var total = 0.0
  for shape in shapes {
    total = total + shape.area()
  }
  total
}

test "values of different types in one list" {
  let shapes: List[any Shape] = [any Square(side: 2.0), any Circle(radius: 1.0)]
  assert total_area(shapes) > 7.0
}
```

- `any Square(side: 2.0)` takes ownership of the value and allocates once.
- A method can be called through `any` if it takes `self`, has no type
  parameters of its own, and neither takes nor returns `Self`.
- An `any` value cannot be turned back into its original type.

### Method names

A call with a dot finds the type's own methods and the methods of every
trait the type implements from the standard library, the calling package,
and the packages its manifest lists. When two traits give one name, the call
writes the trait: `Ordered.compare(first, second)`.

## 10. Lambdas and Function Types

Functions are values in Truss. A function can take another function as an
argument, and a *lambda* writes a function in place.

### Lambdas

```truss
fn apply_twice(value: Int64, step: fn(Int64) -> Int64) -> Int64 {
  step(step(value))
}

fn above(numbers: Slice[Int64], threshold: Int64) -> List[Int64] {
  numbers.filter(fn(number) { number > threshold })
}

test "lambdas" {
  assert apply_twice(5, step: fn(value) { value.saturating_multiply(2) }) == 20
  assert above([1, 5, 10], threshold: 4) == [5, 10]
  var scores = [10, 20, 30]
  mut scores.update_each(fn(score) { score = score / 2 })
  assert scores == [5, 10, 15]
}
```

- **`fn(value) { ... }` is a lambda.** Its body's last expression is its
  result.
- **A lambda's types come from where it is used.** `apply_twice` declares
  `step: fn(Int64) -> Int64`, so `value` is an `Int64`. The types flow from
  outside in, never from the lambda's body, so a lambda with nothing to give
  it types is an error:

  ```text
  main.truss:2:15: error[types.lambda_needs_type]: A lambda's parameter types come from where it is used, and nothing here gives them. Give the `let` a function type, or the call type arguments.
    |   let twice = fn(value) { value * 2 }
    |               ^^^^^^^^^^^^^^^^^^^^^^^
  1 error
  ```

- **A lambda reads the variables around it,** as the lambda in `above` reads
  `threshold`, but it cannot change them:

  ```text
  main.truss:4:5: error[types.not_assignable]: A lambda cannot mutate its captures, and `total` is from outside it. Return the new value instead, or use a loop.
    |     total = 1
    |     ^^^^^
  1 error
  ```

- **A lambda's parameter can be `mut`** when its function type says so.
  `update_each` lends each element to the lambda `mut`, so `score = score /
  2` changes the list.
- **A lambda's capabilities come from its body.** A lambda that prints uses
  `Console`, and one with a loop that may never end uses `RunForever`.
- `return` and `?` in a lambda leave the lambda, not the function around it.
  `break` and `continue` cannot reach a loop outside it.
- A lambda is always passed inside the call's parentheses.

### Function types

A function type is written `fn(Input, ...) -> Output`. Clauses on a function
type go inside parentheses:

| Type | Takes a function that |
|---|---|
| `fn(Int64) -> Int64` | Takes and returns an `Int64`, uses no capabilities, and terminates |
| `(fn(String) uses Console)` | May print |
| `(fn(String) uses RunForever)` | May run forever |
| `(fn(Item) uses generic Granted)` | May use whatever the function passed uses, as the next section explains |
| `(fn(Int64) -> Bool cost time O(1))` | Takes constant time |
| `(fn(element: Element) -> Output requires items.contains(element))` | May rely on a precondition, which the caller proves at each call |
| `(fn(count: UInt64) -> UInt64 ensures result < count)` | Promises a postcondition of each result, which the caller may rely on |

**A function type takes only functions whose capabilities its `uses`
names,** exactly as a function declaration uses only the capabilities it
declares. A function type without `uses` takes only pure functions that
terminate. A named function is a value too, and passes wherever its
signature fits:

```truss
fn is_even(number: Int64) -> Bool {
  number % 2 == 0
}

test "a named function as a value" {
  assert [1, 2, 3, 4].filter(is_even) == [2, 4]
}
```

`truss show` tells you what a callback may do and what it is told. `filter`'s
callback may use whatever its caller can, and may rely on receiving an
element of the slice. The result holds the elements for which it answered
`true` ([Callback contracts](#callback-contracts)):

```text
$ truss show Slice.filter
standard/list/slice/slice.truss:533
public fn Slice[Element: Copyable].filter(
  self,
  keep: (fn(element: Element) -> Bool uses generic Granted requires self.model().contains(element)),
) -> List[Element]
  uses generic Granted
  ensures result.length() <= self.length()
  ensures forall i in 0..result.length() => keep.ensures(result.model()[i], true)
  cost time O(self.length() * (time(keep) + time(Element.copy)))
```

### Capability parameters

A function that calls a callback can pass on whatever capabilities the
callback uses, without knowing them in advance, through a *capability
parameter*:

```truss
use standard::console

fn visit_all[Item](items: Slice[Item], visit: (fn(Item) uses generic Granted))
  uses generic Granted
{
  for item in items {
    visit(item)
  }
}

fn print_all(names: Slice[String])
  uses Console
{
  visit_all(names, visit: fn(name) { Console.print_line(name) })
}

fn wait_for_each(names: Slice[String])
  uses Console, RunForever
{
  visit_all(names, visit: fn(name) {
    while Console.read_line() is Some(line) {
      if line == name {
        return
      }
    }
  })
}

test "a pure lambda needs no capability" {
  visit_all([1, 2, 3], visit: fn(_) {})
}

test "a printing lambda" {
  var screen = console::CapturedConsole.new()
  provide mut screen {
    print_all(["a", "b"])
  }
  assert screen.output() == "a\nb\n"
}

test "a lambda that may run forever" uses RunForever {
  var screen = console::CapturedConsole.new(input: ["x", "a", "b"])
  provide mut screen {
    wait_for_each(["a", "b"])
  }
}
```

- **`generic Granted` names a capability parameter,** a set of capabilities
  that each call fills in from the functions it passes. Nothing declares it
  but its uses: every `generic Granted` in one signature is the same set.
- `uses generic Granted` on `visit_all` says it uses exactly what `visit`
  uses. A pure caller passing a pure lambda needs nothing, and `print_all`,
  whose lambda prints, needs `uses Console`.
- **Termination is passed on the same way.** `RunForever` is a capability,
  so `visit_all` terminates when the lambda passed to it does. In
  `wait_for_each`, the lambda's loop may never end, so the call to
  `visit_all` may not either, and `wait_for_each` must say so. Without
  `RunForever`:

  ```text
  main.truss:4:3: error[capabilities.not_available]: This call uses `RunForever`, which is not available here. Declare it with `uses RunForever`.
    |   visit_all(names, visit: fn(name) {
    |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  ```

This is *polymorphic termination*: a higher-order function terminates
exactly when the functions passed to it do, with no promise written for
either.

### Callback contracts

A parameter's function type can promise its callee something of each
result, and a callee's contract can say what the function passed returned:

```truss
fn pick(
  items: Slice[UInt8],
  choose: (fn(count: UInt64) -> UInt64 uses generic Granted requires count > 0 ensures result < count),
) -> UInt8
  uses generic Granted
  requires items.length() > 0
{
  items[choose(items.length())]
}

fn mapped(value: Option[Int64], transform: (fn(Int64) -> Int64 uses generic Granted)) -> Option[Int64]
  uses generic Granted
  ensures match value {
    Some(inner) => result is Some(output) && transform.ensures(inner, output)
    None => result is None
  }
{
  match value {
    Some(inner) => Some(transform(inner))
    None => None
  }
}

fn halved(value: Option[Int64]) -> Option[Int64]
  ensures match value {
    Some(inner) => result is Some(half) && half == inner / 2
    None => result is None
  }
{
  mapped(value, transform: fn(inner) { inner / 2 })
}

test "callback contracts" {
  assert pick([1, 2, 3], choose: fn(count) { count - 1 }) == 3
  assert halved(Some(4)) == Some(2)
}
```

- **The function passed keeps the `ensures` of its parameter's type.** `pick`
  indexes with `choose`'s result, which the type promises is below `count`.
  A lambda passed for `choose` proves that, as `fn(count) { count - 1 }`
  does, and a named function's own `ensures` must imply it.
- **`transform.ensures(inner, output)` names the postcondition of the
  function passed:** it holds where that function may return `output` for
  `inner`. `mapped` promises it of its result, and `halved` learns
  `half == inner / 2` from its lambda's body.
- **It is a relation, not a call.** A callback that reads `Random` may answer
  differently each time, so a specification writes `transform(inner)` only
  for a pure `transform`.
- **A lambda states no `requires` or `ensures`:** its body is its contract.
  A callback that needs a contract of its own is a named function.

### Returning and storing functions

A lambda that reads variables around it is a view of them, so it follows the
rules of [views](#views): it cannot outlive the function that made it. A
lambda that reads nothing from around it can be returned and stored:

```truss
fn incrementer() -> fn(Int64) -> Int64 {
  fn(value) { value.saturating_add(1) }
}

test "a returned lambda" {
  let next = incrementer()
  assert next(41) == 42
}
```

```text
main.truss:1:4: error[ownership.view_escapes]: This returns a capturing lambda. A lambda's captured variables live in this function's stack frame, so the lambda would dangle. A function returns a view only of its parameters.
  | fn make(threshold: Int64) -> fn(Int64) -> Bool {
  |    ^^^^
1 error
```

A function-typed parameter can be called but not stored. One declared `own`
can be stored, in a field or a list, and accepts only functions that capture
nothing.

## 11. Capabilities

In most languages, any function can read a file, open a connection, or read
the clock, and nothing in its signature says so. In Truss, every effect is a
*capability*, and a function can use only the capabilities its signature
lists.

- **A function with no `uses` clause is pure.** Given the same arguments, it
  returns the same result, and it cannot touch the outside world.
- **Each caller lists the capabilities of its callees,** up to `main`, so a
  signature says everything a call can do.
- **The caller decides what each capability does.** `main` gets the real
  console and file system. A test gets fakes, so it is fast and
  deterministic.
- **A dependency can use only what its manifest grants it** ([Chapter
  6](#grants)).

### Using capabilities

A capability's methods are called through its name:

```truss
use standard::console
use standard::files

fn archive(name: StringSlice) -> Result[UInt64, SystemError]
  uses FileRead, FileWrite, Console
{
  let text = FileRead.read_text(Path.new(name))?
  FileWrite.write_text(Path.new("${name}.bak"), contents: text)?
  Console.print_line("archived ${name}")
  Ok(text.length())
}

test "fake files and a fake console" uses RunForever {
  var disk = files::MemoryFiles.new().with_text(Path.new("notes.txt"), contents: "hello")
  var screen = console::CapturedConsole.new()
  let size = provide mut disk, mut screen {
    archive("notes.txt")
  }
  assert size.ok() == Some(5)
  assert disk.text(Path.new("notes.txt.bak")) == Some("hello")
  assert screen.output() == "archived notes.txt\n"
}

fn main(arguments: List[String]) -> ExitCode
  uses FileRead, FileWrite, Console
{
  match archive("notes.txt") {
    Ok(_) => ExitCode.success
    Err(error) => {
      Console.print_error("cannot archive notes.txt: ${error}")
      ExitCode.failure
    }
  }
}
```

**`provide implementation { body }`** runs the body with the given
implementations of capabilities. `MemoryFiles` implements `FileRead` and
`FileWrite` with files held in memory, and `CapturedConsole` implements
`Console` by recording what is printed. Both change as the code runs, so
they are provided `mut`, and the test reads them afterward. Providing a type
provides every capability it implements.

`MemoryFiles` declares that its implementations may run forever, and
providing an implementation requires the capabilities it uses. So the test
declares `uses RunForever`. That keeps the test deterministic: a test whose
`uses` names only `Panic` and `RunForever` still gets no real capability.

`main` needs no `provide`: the runtime gives it the real implementation of
every capability in its `uses` clause, and of nothing else.

### The standard capabilities

| Capability | Allows | A fake for tests |
|---|---|---|
| `Console` | Standard input, output, and error | `console::CapturedConsole` |
| `FileRead` | Opening and reading files, listing directories | `files::MemoryFiles` |
| `FileWrite` | Creating, writing, renaming, and deleting files | `files::MemoryFiles` |
| `Handles` | Using open handles: files, connections, and running programs | `files::MemoryFiles` for its files |
| `NetworkClient` | Outgoing connections and name lookups | `simulation::World` |
| `NetworkServer` | Listening for connections | `simulation::World` |
| `Clock` | The time, a monotonic clock, and sleeping | `time::FixedClock`, `time::ManualClock` |
| `Random` | Random numbers from the operating system | `random::SeededRandom` |
| `Environment` | Environment variables, the current directory, and the platform | `environment::FixedEnvironment` |
| `Processes` | Running other programs | `simulation::World` |
| `Signals` | Waiting for a signal sent to the program | `simulation::World` |
| `Tasks` | Running `concurrent` code ([Chapter 14](#concurrent-code)) | `tasks::SeededTasks` |
| `Log` | Writing to the program's log | `log::DiscardLog` |
| `Panic` | Stopping the program ([Chapter 8](#unrecoverable-errors-with-panic)) | None: a panic cannot be caught |
| `RunForever` | Running without a proof that the code ends ([Chapter 13](#termination)) | None: nothing implements it |

`simulation::World` simulates a whole machine: files, a network, processes,
and a clock, all deterministic from a seed. `truss show Console` prints a
capability's methods.

```truss
use standard::time

fn stamp(message: StringSlice) -> String
  uses Clock
{
  "${Clock.now().unix_seconds()} ${message}"
}

test "a fixed clock" {
  let clock = time::FixedClock(time: Instant.from_unix_nanoseconds(1_700_000_000_000_000_000))
  let line = provide clock {
    stamp("started")
  }
  assert line == "1700000000 started"
}
```

### Handles

A *handle* stands for something the operating system holds, such as an
open file. `FileRead.open` returns a `FileReader`, a handle, and using it
needs `Handles`:

```truss
use standard::files

fn count_lines(name: StringSlice) -> Result[UInt64, SystemError]
  uses FileRead, Handles, RunForever
{
  var reader = FileRead.open(Path.new(name))?
  var count: UInt64 = 0
  while mut reader.read_line()? is Some(_) {
    count = count.saturating_add(1)
  }
  Ok(count)
}

test "a handle on a memory file" uses RunForever {
  var disk = files::MemoryFiles.new().with_text(Path.new("a.txt"), contents: "one\ntwo\n")
  let counted = provide mut disk {
    count_lines("a.txt")
  }
  assert counted.ok() == Some(2)
}
```

Reading until the end of a file has no measure the compiler can see, so
`count_lines` declares `uses RunForever`. A handle is closed when its owner
is done with it, on every path, and closing it never fails. A handle is not `Copyable`, so it has exactly one
owner.

### Implementing a capability

Any type can implement a capability, and code that uses the capability
cannot tell which implementation it got:

```truss
fn roll_die() -> UInt64
  uses Random
{
  Random.next() % 6 + 1
}

type LoadedDie(face: UInt64)

impl Random for LoadedDie {
  fn next(self) -> UInt64 {
    self.face
  }
}

test "a loaded die" {
  let rolled = provide LoadedDie(face: 4) {
    roll_die()
  }
  assert rolled == 5
}
```

An implementation's methods take `self`, or `mut self` when they change its
state. Code never calls an implementation directly, only the capability.

### Defining a capability

A capability of your own declares its methods without bodies and without
`self`:

```truss
capability Inventory {
  fn count(item: StringSlice) -> UInt64
  fn take(item: StringSlice) -> Bool
}

type StockRoom(counts: Map[String, UInt64])

impl Inventory for StockRoom {
  fn count(self, item: StringSlice) -> UInt64 {
    self.counts.get(item.to_string()).unwrap_or(0)
  }

  fn take(mut self, item: StringSlice) -> Bool {
    let key = item.to_string()
    if self.counts.get(key) is Some(count) && count > 0 {
      self.counts[own key] = count - 1
      true
    } else {
      false
    }
  }
}

type ReadOnly()

impl Inventory for ReadOnly
  uses Inventory
{
  fn count(self, item: StringSlice) -> UInt64 {
    Inventory.count(item)
  }

  fn take(self, item: StringSlice) -> Bool {
    false
  }
}

fn restock_report(item: StringSlice) -> String
  uses Inventory
{
  if Inventory.take(item) { "took one ${item}" } else { "none taken, ${Inventory.count(item)} left" }
}

test "an inventory, and a narrowed one" {
  var room = StockRoom(counts: ["apple": 2])
  let first = provide mut room {
    restock_report("apple")
  }
  assert first == "took one apple"
  let second = provide mut room {
    provide ReadOnly() {
      restock_report("apple")
    }
  }
  assert second == "none taken, 1 left"
}
```

- **`ReadOnly` narrows another implementation.** Inside an implementation,
  a call of the capability it implements goes to the next provider out. So
  `ReadOnly` passes `count` on to the `StockRoom` and refuses every `take`.
  The standard library's `files::FilesWithin` narrows the file system to one
  directory the same way.
- **An implementation with a `uses` clause** can use those capabilities, and
  providing it requires them.
- **A capability method always returns to its caller, once,** and keeps no
  view it is given.
- **Only the standard capabilities have real implementations from the
  runtime.** A program provides its own capabilities in `main`, as the test
  does, with whatever implementation it chooses.

### Why capabilities

| Question | How a capability answers it |
|---|---|
| What can this function do? | Its `uses` clause lists every effect |
| Can a dependency send my data over the network? | Only if its manifest grants `NetworkClient` |
| Why does this test fail only sometimes? | It cannot: a test without `uses` gets fakes, and its result is cached |
| How do I test code that reads the clock? | Provide a `FixedClock` |
| Can I run a plugin with less access? | Provide a narrowing implementation around it |

## 12. Writing Tests

Tests in Truss sit beside the code they test, in any file of a module, and
`truss test` runs them. Because effects are capabilities, a test controls
everything its code can observe, so tests are deterministic: a test that
passes once passes every time, until its code changes.

### Writing a test

```truss
fn price_with_tax(cents: UInt64) -> UInt64
  requires cents <= 1_000_000
{
  cents + cents / 10
}

test "tax is ten percent" {
  assert price_with_tax(1000) == 1100
}

test "tax rounds down" {
  assert price_with_tax(1005) == 1105
}
```

- **`test "name" { ... }`** defines a test. Name it for what it shows: the
  name is the documentation.
- **`assert condition`** fails the test when the condition is false. It
  appears only in tests and proofs. After an `assert`, the rest of the test
  can rely on the asserted fact.
- **A test is code like any other.** `truss check` type-checks and proves it,
  so the call `price_with_tax(1005)` must meet the function's `requires`.

```text
$ truss test
2 passed in 0.4s (check 0.0s, build 0.4s, tests 0.0s)
```

A failed test shows the `assert` that failed and where. With `1106` in
place of `1105` in the second test:

```text
$ truss test
shop "tax rounds down": failed
    assert price_with_tax(1005) == 1106
      at main.truss:12:10

1 passed, 1 failed in 0.3s (check 0.0s, build 0.3s, tests 0.0s)
```

A test that panics fails with the panic's message, and a panic ends only its
own test. A test that calls code that may panic declares `uses Panic`, and
one whose code may run forever declares `uses RunForever`, as a function
does.

### Running tests

| Command | Runs |
|---|---|
| `truss test` | Every test of the package that has no cached result |
| `truss test FILE_OR_DIRECTORY` | The tests in those files |
| `truss test --match TEXT` | The tests whose names contain `TEXT` |
| `truss test --rerun` | Every selected test, ignoring cached results |
| `truss test --timings` | The tests, then each one's duration, slowest first |

`truss test` runs the tests only once every proof passes. To run them while
you are still working on a proof, write `todo` in the proof, as
[Chapter 13](#theorems-and-proof-blocks) shows. A test build checks each
operation that could fail, so a test that reaches a real bug stops at the
operation, and `truss build` refuses the `todo` until the proof is written.
Each test has a time limit, 10 seconds unless the project's manifest sets
another, and a test that runs past it fails.

### Deterministic tests and caching

**A test provides the capabilities its code uses, or declares them.** A
test whose code prints must provide a console:

```truss
use standard::console

fn greet(name: StringSlice)
  uses Console
{
  Console.print_line("Hello, ${name}!")
}

test "greet prints a greeting" {
  var screen = console::CapturedConsole.new()
  provide mut screen {
    greet("Ada")
  }
  assert screen.output() == "Hello, Ada!\n"
}

test "a captured console supplies input" {
  var screen = console::CapturedConsole.new(input: ["first", "second"])
  let lines = provide mut screen {
    Console.read_line()
  }
  assert lines == Some("first")
}
```

Without the `provide`, the test does not compile:

```text
main.truss:8:3: error[capabilities.not_available]: This call uses `Console`, which is not available here. Declare it with `uses Console`, or `provide` an implementation.
  |   greet("Ada")
  |   ^^^^^^^^^^^^
1 error
```

A test's standard input is empty, so `Console.read_line()` in a test without
a `CapturedConsole` returns `None`.

A test whose `uses` names nothing but `Panic` and `RunForever` gets no real
capability, so its result depends only on its code: it is *deterministic*.
**`truss test` caches each passing deterministic test's result** and runs it
again only when the code it reaches changes. In a large project, `truss test`
after an edit runs only the tests the edit can affect.

### External tests

A test whose `uses` names any other capability gets the real
implementations of exactly those capabilities. It is *external*: it runs
every time, and its result is never cached.

```truss
test "the monotonic clock never goes backward" uses Clock {
  let first = Clock.monotonic()
  let second = Clock.monotonic()
  assert second >= first
}
```

Use external tests sparingly, for code whose point is the real outside
world. A test of what code prints is better written with a
`CapturedConsole`, which it can check.

### Unfinished code

`todo` stands for anything not yet written: an expression, a function's
body, or a type's definition. Code with a `todo` type-checks and is proven,
so you can write a program top-down and fill it in:

```truss
fn discount(cents: UInt64) -> UInt64 {
  todo
}

test "discounts are coming" {
  assert discount(100) == 90
}
```

`truss holes` lists every `todo` with its type, the names in scope there,
and the tests and `main` that reach it:

```text
$ truss holes
main.truss:2:3: hole of type UInt64
    in scope: cents: UInt64
    blocks: test shop "discounts are coming"
```

A test that reaches a `todo` is *incomplete*, not failed:

```text
shop "discounts are coming": incomplete
    todo reached
      at main.truss:2:3
```

`truss build` refuses a program whose `main` can reach a `todo`. In a
development build from `truss run`, a `todo` that runs stops the program
and reports where.

### echo

`echo expression` records the value's debug output with its position, and
returns the value, so it can wrap any expression without changing what the
code does:

```truss
fn price_with_tax(cents: UInt64) -> UInt64
  requires cents <= 1_000_000
{
  cents + (echo cents / 10)
}

test "echo shows a value" {
  assert price_with_tax(1000) == 1100
}
```

In a test, the output is attached to the test's report:

```text
$ truss test
shop "echo shows a value": passed
    main.truss:4:12: 100

1 passed in 0.1s (check 0.0s, build 0.1s, tests 0.0s)
```

Outside a test, `echo` writes to standard error. It needs no `uses` clause,
and every type has debug output. `truss build` refuses a program whose
`main` can reach an `echo`, and a package that holds one cannot be
published, so none is left behind by accident. `echo` takes everything after
it, so as an operand it goes in parentheses.

## 13. Contracts and Proofs

Every chapter so far has leaned on the prover: it showed that additions fit,
indexes are in bounds, and `match`es are complete. This chapter shows how to
state your own promises, and how to help the prover when it cannot see why
one holds.

The prover is Z3, an SMT solver. You never call it directly. `truss check`
turns each promise into a question for Z3, and reports each one Z3 cannot
answer as an error, often with a counterexample: values for which the promise
fails.

### Preconditions and postconditions

A `requires` clause is a *precondition*: every caller proves it. An
`ensures` clause is a *postcondition*: the function's body proves it, and
every caller may rely on it. `result` names the returned value.

```truss
fn double(value: Int64) -> Int64
  requires value >= -1000 && value <= 1000
  ensures result == value * 2
{
  value * 2
}

fn quadruple(value: Int64) -> Int64
  requires value >= -500 && value <= 500
  ensures result == value * 4
{
  double(double(value))
}

test "contracts" {
  assert quadruple(3) == 12
}
```

**A caller knows a function only by its signature.** The prover never looks
inside `double` when it checks `quadruple`. Without `ensures result == value
* 2`, nothing tells it that `double(value)` is small enough to pass to
`double` again:

```text
main.truss:10:3: error[prover.requires]: `value >= -1000 && value <= 1000` may not hold for this call to `double`. For example, when `value` is 0.
  |   double(double(value))
  |   ^^^^^^^^^^^^^^^^^^^^^
  note: main.truss:2:12: This is the clause that must hold.
1 error
```

The counterexample shows how little the caller knows: even when `value` is
0, nothing bounds what `double(0)` returns.

This rule is what makes Truss scale. Each function is proven once, against
the signatures it calls, and an edit to a body never invalidates the proofs
of its callers.

#### Writing good contracts

State what callers need, not a copy of the body. `ensures result ==
value * 2` is the body here only because the body is a single expression. A
sorting function's useful contract is that the result is sorted and holds
the same elements, not the steps of the algorithm. Tight contracts are
short, and they leave the body free to change.

`old(expression)` is an expression's value when the function was called,
which is how a contract describes a change:

```truss
type Counter(count: UInt64)

fn Counter.increment(mut self)
  requires self.count < 100
  ensures self.count == old(self.count) + 1
{
  self.count += 1
}

fn add_two(counter: mut Counter)
  requires counter.count < 50
  ensures counter.count == old(counter.count) + 2
{
  mut counter.increment()
  mut counter.increment()
}

test "old values" {
  var counter = Counter(count: 3)
  add_two(mut counter)
  assert counter.count == 5
}
```

### Invariants

An `invariant` on a type is a fact about every value of the type:

```truss
type Percent(value: UInt8)
  invariant value <= 100

fn Percent.new(value: UInt8) -> Option[Percent] {
  if value <= 100 { Some(Percent(value)) } else { None }
}

fn Percent.complement(self) -> Percent {
  Percent(100 - self.value)
}

test "an invariant" {
  assert Percent.new(30).map(fn(percent) { percent.complement().value }) == Some(70)
  assert Percent.new(130).is_none()
}
```

- **Every value is proven to meet the invariant where it is built,** or
  updated with `with`, so `Percent(self.value + 1)` is an error:

  ```text
  main.truss:5:3: error[prover.invariant]: The invariant of `Percent` may not hold for the value built here.
    |   Percent(self.value + 1)
    |   ^^^^^^^^^^^^^^^^^^^^^^^
  1 error
  ```

- **Code may rely on the invariant of every value it receives.** In
  `complement`, the prover knows `self.value <= 100`, so `100 - self.value`
  cannot go below zero.
- **Invariants are proven, never checked at run time.** A program pays
  nothing for them.

An invariant with an opaque type is how a package guarantees its values are
always valid: other packages cannot build the type's fields directly, and
every function that builds one is proven to keep the invariant.

### Specifications

A *specification* is a clause, an invariant, a law, or a proof. A
specification can say more than code can:

| Form | Meaning |
|---|---|
| `forall index in 0..count => items[index] >= 0` | True for every value in a range or a collection |
| `exists item in items => item == target` | True for at least one value |
| `forall value: Int64 => value + 0 == value` | True for every value of a type |
| `condition ==> consequence` | When the condition holds, so does the consequence |
| `old(self.items)` | A value as it was when the function was called |
| `identical(first, second)` | The same value, for any type |
| `items.model()` | A collection's value as a mathematical `Sequence`, `FiniteSet`, or `FiniteMap` |

- **Arithmetic in a specification is exact.** It works on `Integer`, a type
  that exists only in specifications, so `self.count + 1` in a contract
  never overflows, and comparisons can mix integer types.
- A function called in a specification uses no capability, so it
  terminates. A function whose `uses` is a capability parameter, such as
  `map`, can be called in one with a pure lambda.
- A quantifier over a range is also an expression in code, which runs as a
  loop that stops when it knows the answer. A quantifier over a type, and
  `==>`, appear only in specifications.

```truss
fn contains_zero(numbers: Slice[Int64]) -> Bool
  ensures result == (exists index in 0..numbers.length() => numbers[index] == 0)
  cost allocations == 0
{
  exists index in 0..numbers.length() => numbers[index] == 0
}

test "a quantifier in code" {
  assert contains_zero([1, 0])
  assert !contains_zero([1, 2])
}
```

### Loops

**Across a loop's iterations, the prover keeps only the facts the loop's
*invariant* states.** It reasons about one iteration at a time, so after the
first iteration it knows nothing else about the variables the loop changes.
In [Chapter 3](#integer-overflow), an accumulating sum would not compile.
This is why:

```text
main.truss:6:5: error[prover.overflow]: `total += value` may overflow `UInt64`. For example, when `limit` is 2, `total` is 18446744073709551615, `value` is 1. It can also be checked first with an `if`, or done with the checked operation.
  |     total += value
  |     ^^^^^^^^^^^^^^
1 error
```

The counterexample has `total` at the largest `UInt64` after one iteration,
because nothing said otherwise. A loop invariant says how large `total` can
be:

```truss
fn sum_below(limit: UInt64) -> UInt64
  requires limit <= 1000
  ensures result <= limit * limit
{
  var total: UInt64 = 0
  for value in 0..limit
    invariant total <= value * limit
  {
    total += value
  }
  total
}

fn all_positive(numbers: Slice[Int64]) -> Bool
  ensures result == (forall index in 0..numbers.length() => numbers[index] > 0)
{
  for index in 0..numbers.length()
    invariant forall earlier in 0..index => numbers[earlier] > 0
  {
    if numbers[index] <= 0 {
      return false
    }
  }
  true
}

test "loops with invariants" {
  assert sum_below(4) == 6
  assert all_positive([1, 2])
  assert !all_positive([1, -2])
}
```

- **An invariant holds at the start of every iteration and when the loop
  ends.** The prover checks that it holds on entry, and that one iteration
  that starts with it ends with it.
- **In a range loop's clauses, the loop variable is the next iteration's
  index:** `value` is 0 on entry, and `limit` when the loop ends. So at the
  end, `total <= limit * limit`, which is the function's `ensures`.
- `all_positive`'s invariant says every element before `index` is positive.
  When the loop ends, `index` is the length, so the invariant is the
  `ensures`.
- In the clauses of a loop over a collection, `visited` is the `Sequence` of
  the elements the loop has visited.

### Termination

**A function terminates unless its `uses` names `RunForever`.** The compiler
proves that every loop and every recursion in such a function ends, so a
function that may hang says so in its signature. Most code needs nothing
written for this:

| Code | Its measure |
|---|---|
| A `for` loop over a range or a collection | The elements left to visit |
| A `for` loop over a cursor whose type implements `FiniteCursor`, such as `text.characters()` | `remaining()` |
| A `while` loop whose condition compares two sides with `<`, `<=`, `>`, or `>=`, or begins with such a comparison joined by `&&` | The distance between the two sides |
| A recursive call on a part of a parameter, such as `Expression.evaluate` in [Chapter 5](#recursive-types) | The parameter, which gets smaller |
| A loop or a function with a `decreases` clause | The clause |
| A loop or a function with `decreases m when C`, such as `decreases cursor.remaining() when Items: FiniteCursor` | `m` where `C` holds; elsewhere it uses `RunForever unless C` |

A `decreases` clause names a measure: an integer that every iteration, or
every recursive call, makes smaller, and that never goes below zero.

```truss
fn gcd(first: UInt64, second: UInt64) -> UInt64
  decreases second
{
  if second == 0 { first } else { gcd(first: second, second: first % second) }
}

fn halve_until_odd(value: UInt64) -> UInt64
  requires value > 0
{
  var current = value
  while current % 2 == 0
    invariant current > 0
    decreases current
  {
    current /= 2
  }
  current
}

test "terminating code" {
  assert gcd(12, second: 18) == 6
  assert halve_until_odd(12) == 3
}
```

Notice `gcd(first: second, second: first % second)`. A bare argument that is
a variable named like a parameter goes to that parameter, wherever it
appears, so `gcd(second, ...)` would pass `second` to `second` twice. Writing
both labels avoids that.

A recursion without a measure is an error. A function `countdown` that
calls itself on `count / 2`, which is not a part of `count`, states none:

```text
main.truss:2:30: error[prover.termination]: This recursive call may not end: give the function a `decreases` clause for the prover to show that the recursion ends. For example, when `count` is 1. On that path, `count == 0` is false.
  |   if count == 0 { 0 } else { countdown(count / 2) }
  |                              ^^^^^^^^^^^^^^^^^^^^
1 error
```

A loop with no measure at all uses `RunForever`, and so does a call of a
function that uses it. Without its `decreases`, the loop in
`halve_until_odd` is rejected:

```text
main.truss:5:3: error[capabilities.not_available]: This loop has no measure, so it uses `RunForever`, which is not available here. Declare it with `uses RunForever`, or give the loop a `decreases` clause.
  |   while current % 2 == 0
  |   ^^^^^^^^^^^^^^^^^^^^^^
1 error
```

A comparison's measure is proven to decrease like a written one, so the
loop's invariant must give the prover what it needs. Here `power` must stay
positive, or doubling it would not bring it closer to `limit`:

```truss
fn first_power_of_two_above(limit: UInt64) -> UInt64
  requires limit < 1_000_000
{
  var power: UInt64 = 1
  while power <= limit
    invariant power >= 1 && power <= 2_000_000
  {
    power *= 2
  }
  power
}

test "a loop measured by its comparison" {
  assert first_power_of_two_above(5) == 8
}
```

Without `power >= 1` in the invariant:

```text
main.truss:5:3: error[prover.termination]: This loop's measure may not decrease. For example, when `limit` is 0, `power` is 0.
  |   while power <= limit
  |   ^^^^^^^^^^^^^^^^^^^^
1 error
```

Code that really may run forever, such as a server's loop or a loop that
reads until its input ends, declares `uses RunForever`. A function that uses
`RunForever` has no `time` clause, and cannot be called in a specification.

### Cost

A `cost` clause bounds a resource that a call uses, and the compiler proves
it from the body and from the cost clauses of the calls the body makes:

```truss
fn total(numbers: Slice[Int64]) -> Int64
  cost time O(numbers.length())
{
  var sum: Int64 = 0
  for number in numbers {
    sum = sum.saturating_add(number)
  }
  sum
}

test "a cost bound" {
  assert total([1, 2, 3]) == 6
}
```

| Clause | Promises |
|---|---|
| `cost time O(f)` | At most `c * f + d` steps, for some constants `c` and `d` |
| `cost allocations == 0` | No heap allocation |
| `cost allocated_bytes <= n` | At most `n` bytes allocated |
| `cost calls(visit) == items.length()` | Exactly one call of the parameter `visit` per item |
| `cost amortized time O(1)` | Constant time on average over a sequence of calls, as `List.push` promises |

A bound can use the parameters, their fields, pure methods, `log(n)`, `power(base, exponent)`, and `time(visit)`, the bound of a
function parameter. The standard library states costs for every function,
which is what lets you prove your own: `truss show List.push` shows `cost
amortized time O(1)`.

### Theorems and proof blocks

Sometimes a fact follows from what the prover knows, but too indirectly for
it to find alone. Then you write the steps down.

A `theorem` is a fact with its proof. Its `requires` are its assumptions, its
`ensures` its conclusions, and its body the proof. An empty body asks the
prover to prove it alone. Calling a theorem makes its `ensures` available.

A `proof` block inside a function holds steps of a proof: calls of
theorems, and `assert`s, which in a proof are proven, not checked at run
time. A proof block is removed from the compiled program.

```truss
fn double(value: Int64) -> Int64
  requires value >= -1000 && value <= 1000
  ensures result == value * 2
{
  value * 2
}

theorem doubling_is_even(value: Int64)
  requires value >= -1000 && value <= 1000
  ensures double(value) % 2 == 0
{
}

theorem doubles_are_even(values: List[Int64])
  requires forall i in 0..values.length() => values[i] >= -1000 && values[i] <= 1000
  ensures forall i in 0..values.length() => double(values[i]) % 2 == 0
{
  assert forall i in 0..values.length() => {
    doubling_is_even(values[i])
    double(values[i]) % 2 == 0
  }
}

fn half_of_double(value: Int64) -> Int64
  requires value >= -1000 && value <= 1000
  ensures result == value
{
  let doubled = double(value)
  proof {
    doubling_is_even(value)
    assert doubled % 2 == 0
  }
  doubled / 2
}

fn low_bit(value: UInt64) -> UInt64
  ensures result == value % 2
{
  proof {
    assert (value & 1) == value % 2 by bit_vector
  }
  value & 1
}

test "proofs" {
  assert half_of_double(21) == 21
  assert low_bit(7) == 1
}
```

- A theorem that calls itself on smaller input is a proof by induction.
- A theorem called in a quantifier's body proves its fact for every value,
  as in `doubles_are_even`. The prover proves the theorem's `requires` for
  each value, and the quantifier's body states the fact.
- `assert condition by bit_vector` proves a fact about bitwise operations,
  treating the integers it names as bits. It names only integers and
  booleans, and states as a hypothesis any fact it needs from around it.
- A theorem is called only in specifications and proofs. It has no compiled
  body.

### When the prover needs help

| The error says | Try |
|---|---|
| A counterexample, such as "when `count` is 255" | The promise really fails for those values: add a `requires`, an `if`, or a checked operation |
| "a value the prover knows nothing more about" | A callee's result or a loop variable is unconstrained: add an `ensures` to the callee, or an `invariant` to the loop |
| "The solver ran out of steps, so it may hold but needs help" | Break the step into smaller ones: an `assert` in a `proof` block, or a theorem |
| A `requires` of a callee "may not hold" | Find which fact the caller lacks; the note points at the clause |
| A `forall` "may not hold", though a theorem proves its body for one value | Call the theorem in the quantifier's body, then state the body, as `doubles_are_even` does |

The prover never guesses. It knows the facts in scope: the `requires` of
the function, the conditions of the `if`s around the code, the `ensures` of
each call, the invariants of the values, and the loop invariants. When a
proof fails, ask which of those is missing.

## 14. Parallelism and Concurrency

Truss runs code at the same time in two ways:

| Form | For | Capabilities |
|---|---|---|
| `parallel` | Computing faster on several cores | None but `Panic` and `RunForever`: a function with `parallel` stays pure |
| `concurrent` | Waiting on several things at once, such as files or connections | Those of the code around it, plus `Tasks` |

Both follow the ownership rules of [Chapter 4](#4-ownership), which is why
neither can race.

### Parallel blocks

A `parallel` block runs each statement directly inside it, a *branch*, at
the same time, and ends when every branch has ended:

```truss
fn sum(numbers: Slice[Int64]) -> Int64 {
  var total: Int64 = 0
  for number in numbers {
    total = total.saturating_add(number)
  }
  total
}

fn parallel_sum(numbers: Slice[Int64]) -> Int64 {
  let halves = numbers.split_at(numbers.length() / 2)
  parallel {
    let left = sum(halves.first)
    let right = sum(halves.second)
  }
  left.saturating_add(right)
}

fn square_all(numbers: mut List[Int64]) {
  parallel for number in mut numbers {
    number = number.saturating_multiply(number)
  }
}

test "parallel code" {
  assert parallel_sum([1, 2, 3, 4]) == 10
  var numbers = [1, 2, 3]
  square_all(mut numbers)
  assert numbers == [1, 4, 9]
}
```

- **A `let` in a branch is in scope after the block,** as `left` and `right`
  are.
- **A parallel block means what its branches would mean run in order,** so
  you can reason about it as sequential code.
- **`parallel for`** runs the iterations at the same time. Its body changes
  only its own element and its own variables.
- **A branch cannot leave the block** with `return`, `break`, `continue`, or
  `?`.

**Branches cannot race.** Any branch may read any place, but a place one
branch changes is used by no other branch:

```text
main.truss:3:9: error[ownership.data_race]: Data race: one branch of this `parallel` block mutates `numbers`, and another branch uses it.
  |     mut numbers.push(1)
  |         ^^^^^^^
main.truss:4:9: error[ownership.data_race]: Data race: one branch of this `parallel` block mutates `numbers`, and another branch uses it.
  |     mut numbers.push(2)
  |         ^^^^^^^
2 errors
```

`parallel for` can change the elements of a `List`, a `Slice`, or an
`Array` in place because each iteration gets a different element. The
compiler proves two slices disjoint before it lets two branches change
them, as in `sort(mut items[..middle])` beside `sort(mut items[middle..])`.

### Concurrent code

A `concurrent` block runs each branch as a *task*. Tasks are for waiting: a
task that waits for a file or a connection lets the others run. The
function declares `uses Tasks`:

```truss
use standard::files
use standard::tasks

fn total_size(first: StringSlice, second: StringSlice) -> Result[UInt64, SystemError]
  uses Tasks, FileRead
{
  concurrent {
    let one = FileRead.read_text(Path.new(first))?
    let two = FileRead.read_text(Path.new(second))?
  }
  Ok(one.length().saturating_add(two.length()))
}

test "concurrent reads" uses Panic, RunForever {
  var disk = files::MemoryFiles.new()
    .with_text(Path.new("a"), contents: "abc")
    .with_text(Path.new("b"), contents: "de")
  let size = provide mut disk, tasks::SeededTasks.new(1) {
    total_size("a", second: "b")
  }
  assert size.ok() == Some(5)
}
```

- **Branches follow the rules of `parallel` branches,** except that they may
  use the capabilities of the code around them, and may leave the block.
- **A branch that leaves the block with `?`, `return`, or `break` cancels
  the others,** waits for them to end, and then leaves. Here, if the first
  read fails, the second is cancelled and `total_size` returns the error.
- **In a cancelled task, a standard capability call that would wait returns
  at once,** with `Err(SystemError.Cancelled)`, `None`, or nothing.
  `Tasks.cancelled()` tells a task whether it is cancelled.
- **`concurrent for`** runs each iteration as a task.
- **`tasks::SeededTasks` runs tasks deterministically in tests.** Its seed
  picks one order of the tasks, so a test that passes always passes, and
  trying several seeds tries several orders. It stops the test with a panic
  when every task is waiting on another, a deadlock, and it runs the tasks
  in a loop with no measure. So a test that provides it declares
  `uses Panic, RunForever`.

### Communicating between tasks

The standard library's `tasks` module holds the tools tasks share:

| Type | For |
|---|---|
| `Channel` | Sending messages from one task to another |
| `Cell` | A value several tasks update, one at a time |
| `Counter` | A number several tasks add to |
| `Limiter` | Limiting how many tasks do something at once |
| `Pool` | Reusing expensive resources, such as connections |

```truss
use standard::tasks

fn produce_and_consume() -> Int64
  uses Tasks, RunForever
{
  let channel: tasks::Channel[Int64] = tasks::Channel.new()
  concurrent {
    {
      for number in 1..=3 {
        let _ = channel.send(number)
      }
      channel.close()
    }
    let received = {
      var total: Int64 = 0
      while channel.receive() is Some(number) {
        total = total.saturating_add(number)
      }
      total
    }
  }
  received
}

test "a channel between two tasks" uses Panic, RunForever {
  let received = provide tasks::SeededTasks.new(7) {
    produce_and_consume()
  }
  assert received == 6
}
```

The first branch is a block that sends three numbers and closes the
channel. The second receives until the channel is closed. A block is a
statement, so each can be one branch.

`send` and `receive` use `RunForever`: a task that receives from a channel
no task ever sends on or closes waits forever, so nothing proves that the
call returns. `Cell` and `Counter` hold their lock only while a callback that
uses no capability runs, so their calls terminate.

### Shared capabilities

A capability implementation provided `mut` to code that can use `Tasks`
handles one call at a time: each call holds the implementation's lock from
start to end. Such an implementation can take no callback that uses a
capability, so these locks cannot deadlock. One provided without `mut` has
no lock, because nothing in it changes.

## 15. Advanced Features

This chapter covers features you need less often: making your own types
work with `for` loops and `[]`, lending parts of your own values, and string
literals that the compiler checks.

### Cursors

A *cursor* gives values one at a time. It is a value of a type that
implements the prelude trait `Cursor`:

```text
trait Cursor {
  type Element
  capability Uses
  fn next(mut self) -> Option[Self.Element]
    uses Self.Uses
}
```

```truss
type Countdown(left: UInt64)

impl Cursor for Countdown {
  type Element = UInt64

  fn next(mut self) -> Option[UInt64]
    ensures (result is Some(_)) ==> self.left < old(self.left)
  {
    if self.left == 0 {
      return None
    }
    self.left -= 1
    Some(self.left)
  }
}

impl FiniteCursor for Countdown {
  fn remaining(self) -> UInt64
    ensures result == self.left
  {
    self.left
  }
}

test "a cursor" {
  var seen: List[UInt64] = []
  for value in Countdown(left: 3) {
    mut seen.push(value)
  }
  assert seen == [2, 1, 0]
}

test "a cursor's provided methods" {
  assert Countdown(left: 5).to_list() == [4, 3, 2, 1, 0]
  assert Countdown(left: 5).take(2).to_list() == [4, 3]
  assert Countdown(left: 5).skip(3).to_list() == [1, 0]
  assert Countdown(left: 4).count() == 4
  var sums: List[UInt64] = []
  for left, right in Countdown(left: 2).zip(Countdown(left: 2)) {
    mut sums.push(left.saturating_add(right))
  }
  assert sums == [2, 0]
}
```

- `next` returns `Some` of the next value, which the caller owns, or `None`
  when there are no more.
- A `for` loop over a cursor pulls it until it returns `None`. A cursor in a
  variable can be pulled again after a `break`.
- **A loop over a cursor terminates when the cursor measures itself.** Its
  type implements the prelude trait `FiniteCursor`, whose `remaining()`
  counts down: `FiniteCursor` promises that each `next` that returns `Some`
  makes `remaining()` smaller. `impl FiniteCursor for Countdown` proves that
  promise from the `ensures` of `next` and of `remaining`, so the loop in the
  first test needs nothing more. Without the `impl`:

  ```text
  main.truss:19:3: error[capabilities.not_available]: This loop has no measure, so it uses `RunForever`, which is not available here. Declare it with `uses RunForever`, or give the loop a `decreases` clause, or implement `FiniteCursor` for `Countdown`.
    |   for value in Countdown(left: 3) {
    |   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  1 error
  ```

- `Cursor` provides `to_list`, `count`, `last`, `fold`, and `find`, and the
  adapters `skip`, `take`, `step_by`, `chain`, `zip`, `enumerate`, and
  `peekable`. Each adapter returns a new cursor, so they chain.
- **The provided methods that pull a cursor to its end use `RunForever`
  unless the cursor is a `FiniteCursor`.** `to_list` declares
  `uses Self.Uses, RunForever unless Self: FiniteCursor`, so the second
  test, over a `Countdown`, needs no `RunForever`. A call over a channel's
  `Messages`, which may never end, uses it.
- `take` gives a `FiniteCursor` over any cursor, and `skip`, `step_by`,
  `enumerate`, and `zip` give one where their source does, `zip` where its
  first cursor does. `chain` and `peekable` give a plain `Cursor`: their
  count of remaining values could overflow a `UInt64`.
- A function generic over a cursor writes the same condition. One that
  collects `own items` of type `Items: Cursor` declares
  `uses Items.Uses, RunForever unless Items: FiniteCursor`, and its caller
  passes on the condition or meets it.
- `capability Uses` is an *associated capability set*: the capabilities
  `next` uses. A cursor that reads lines from a file has `Uses = FileRead,
  Handles`, and a function that pulls a generic cursor declares `uses
  Source.Uses`.
- An adapter whose `next` pulls its source in a loop, until a value
  matches, defines `capability Uses = Source.Uses, RunForever unless
  Source: FiniteCursor` and measures the loop
  `decreases self.source.remaining() when Source: FiniteCursor`. Over a
  list's cursor it then ends, and its callers need no `RunForever`.
- `items.cursor()` makes a cursor that owns a collection's elements, which
  is what `for item in own items` pulls. It measures itself, as
  `text.characters()` does.

### Loops over your own types

A `for` loop over a value that is not a cursor reads it by position. A type
supports this with two methods: `count(self) -> UInt64`, and
`element(self, position: UInt64)`, which lends the element at a position.

### Indexing your own types

`collection[key]` calls the `Index` trait, and `collection[key]` on the left
of a change calls `IndexMut`:

```truss
type Board(cells: List[Bool])

impl Index for Board {
  type Key = UInt64
  type Output = Bool

  fn contains_key(self, key: UInt64) -> Bool
    ensures result == (key < self.cells.length())
    cost time O(1)
  {
    key < self.cells.length()
  }

  fn at(self, key: UInt64) lends Bool
    requires key < self.cells.length()
  {
    self.cells[key]
  }
}

fn Board.count(self) -> UInt64
  ensures result == self.cells.length()
{
  self.cells.length()
}

fn Board.element(self, position: UInt64) lends Bool
  requires position < self.cells.length()
{
  self.cells[position]
}

fn filled(board: Board) -> UInt64 {
  var total: UInt64 = 0
  for cell in board {
    if cell {
      total = total.saturating_add(1)
    }
  }
  total
}

test "indexing and looping over a board" {
  let board = Board(cells: [true, false, true])
  assert board[2]
  assert filled(board) == 2
}
```

- `contains_key` says which keys the board has. `at`'s `requires` must
  follow from the trait's `requires self.contains_key(key)`, and the
  `ensures` on `contains_key` is what lets the prover see that it does.
- `count`'s `ensures` lets the loop prove that each position it passes to
  `element` is in bounds. Without it, the prover knows nothing about what
  `count` returns.
- `IndexAssign` gives `collection[key] = value` its meaning for a type, such
  as a `Map`, that inserts keys rather than lending a place for them.

### Lending methods of your own

A method that hands out a part of its receiver *lends* it. The caller uses
the part for the rest of its statement:

```truss
type Item(name: String, count: UInt64)

type Shelf(items: List[Item])

fn Shelf.first_item(mut self) lends mut Item
  requires self.items.length() > 0
  ensures self.items.length() == old(self.items.length())
{
  mut self.items[0]
}

test "a lent part" {
  var shelf = Shelf(items: [Item(name: "pen", count: 1)])
  mut shelf.first_item().count = 5
  assert shelf.items[0].count == 5
}
```

- `lends mut Item` lends the part `mut`, and the body writes `mut` on the
  place it lends.
- No code of the method runs after it lends.
- A clause of a lending method that mentions `result` holds where the
  method lends, and every other clause holds when the lend ends. The
  `ensures` here promises that the shelf keeps its length while the caller
  changes the item, so the test can still index it afterward.
- In an `ensures`, `final(result)` is the part as the caller left it.
- A lending method is not a value: a function type cannot lend, since its
  caller could keep the part too long.

### Tagged templates

A string literal can be *tagged* with a type, which turns the literal into a
value of that type. The compiler checks the literal's text when the code is
compiled:

```truss
use standard::html
use standard::regex

test "tagged templates" {
  let word = regex::Regex"[a-z]+"
  assert word.is_full_match("truss")
  assert !word.is_full_match("Truss")
  let name = "<script>"
  let page = html::Html"<p>Hello, ${name.copy()}</p>"
  assert page.text() == "<p>Hello, &lt;script&gt;</p>"
}
```

- `regex::Regex"[a-z]+"` is a regular expression, checked when the code is
  compiled. An invalid one is a compile error:

  ```text
  main.truss:4:14: error[prover.requires]: This template may not meet `is_valid_template(template.literals)`, which its tag requires. Running it on this template's text gives `false`.
    |   let word = regex::Regex"[a-z"
    |              ^^^^^^^^^^^^^^^^^^
  1 error
  ```

- `html::Html"..."` escapes each interpolated value, so text from a user
  cannot become markup. A tag decides how its interpolations are converted,
  which is how a SQL tag would keep a query safe from injection.
- The standard library's tags include `regex::Regex`, `html::Html`,
  `url::Url`, `json::Value`, `files::Glob`, `processes::Command`,
  `http::Route`, and `time::Layout`.
- `Character"é"` and `UInt8"\n"` are tags too, checked to hold exactly one
  character.

A type becomes a tag by implementing the prelude trait `FromTemplate`. Its
`from_template` method states, with a `requires`, which literal text is
valid, and the compiler proves that `requires` by running the check on the
literal's text, as compiled code. See [Tagged
templates](SPECIFICATION.md#tagged-templates).

### Overloads by receiver mode

A method can have up to three overloads that differ only in the mode of
`self`. The keyword at the call site picks one:

```text
fn List[Element: Copyable].filter(self, keep: fn(Element) -> Bool) -> List[Element]
fn List[Element].filter(own self, keep: fn(Element) -> Bool) -> List[Element]
```

`names.filter(...)` copies the elements it keeps, and `own
names.filter(...)` moves them, which works for elements that cannot be
copied.

## Appendix A: Keywords

These words are reserved everywhere and cannot be names:

```text
any assert break capability concurrent continue cost decreases derives echo else
ensures exists false fn for forall if impl in indirect internal invariant is law
lends let match mut opaque own parallel proof provide public requires return self
Self test theorem todo trait true type unreachable use uses var while with
```

These are reserved for later use, and are an error if written:

```text
as async await const defer extern loop macro static unsafe where
```

These words have a meaning only in the places shown, and are ordinary names
elsewhere:

| Words | Meaning |
|---|---|
| `amortized`, `time`, `allocations`, `allocated_bytes`, `calls`, `O`, `potential` | The words of a `cost` clause |
| `result` | The return value, in `ensures` and `cost` |
| `old(expression)` | A value when the function was called, in a specification |
| `identical(first, second)` | Identity, in a specification |
| `visited` | The values a loop has visited, in a loop's clauses |
| `final(result)` | The lent part as the caller left it, in a lending method's `ensures` |
| `log(n)`, `power(base, exponent)` | Functions on exact integers, in a specification |
| `by bit_vector` | After an `assert`'s condition |
| `generic` | In a `uses` list, before the name of a capability parameter |

## Appendix B: Operators

From the tightest binding to the loosest:

| Operators | Meaning |
|---|---|
| `.field`, `.method()`, `[index]`, `(arguments)`, `?`, `with (...)` | Access, call, and propagate an error |
| `-a`, `!a`, `~a`, `mut place`, `own place`, `any value` | Negation, logical not, bitwise not, modes, dynamic dispatch |
| `*`, `/`, `%` | Multiplication, division rounding toward zero, remainder with the sign of the left side |
| `+`, `-` | Addition and subtraction |
| `..`, `..=` | Ranges, excluding and including the end |
| `==`, `!=`, `<`, `<=`, `>`, `>=`, `is` | Comparison and pattern test |
| `&&`, `\|\|` | Logical and and or, which evaluate the right side only when needed and do not mix |
| `==>` | Implication, in specifications |

- **Precedence is a partial order.** Bitwise operators `&`, `|`, `^`, `<<`,
  and `>>` combine only with themselves, `&&` and `||` do not mix, and
  comparisons, `is`, ranges, and `==>` do not chain. Each of those needs
  parentheses, and the compiler offers a fix that adds them.
- **Strings have no operators** but comparison: no `+`, no indexing.
- `a += b`, and the other compound assignments with `-`, `*`, `/`, `%`, `&`,
  `|`, `^`, `<<`, and `>>`, are statements.
- These sequences are errors, because other languages give them a meaning
  Truss does not: `//`, `/*`, `#`, `;`, `'`, `` ` ``, `@`, `++`, `--`,
  `===`, and `!==`.

## Appendix C: The truss Command

| Command | Effect |
|---|---|
| `truss new NAME` | Create the package `NAME` in a new directory |
| `truss check` | Report every diagnostic of the packages and of the packages they depend on |
| `truss check --fix` | Apply every fix that is its diagnostic's only fix, check again, and repeat |
| `truss test [PATH...]` | Check the packages, then run the tests without a cached result |
| `truss test --match TEXT` | Run only the tests whose names contain `TEXT` |
| `truss test --rerun` | Run the selected tests, ignoring cached results |
| `truss test --timings` | List each test's duration, slowest first |
| `truss run [ARGUMENT...]` | Build the program for development and run it; `--` goes before the arguments when the first starts with `-` |
| `truss run --release [ARGUMENT...]` | Build as `truss build` does, then run |
| `truss build [-o PATH]` | Build the program for release, refusing one whose `main` reaches a `todo` or an `echo` |
| `truss holes [PATH...]` | List every `todo` with its type, the names in scope, and the tests and `main` that reach it |
| `truss show PATH...` | Print the signatures of a package, module, type, or definition; `--body` prints whole definitions |
| `truss explain FILE:LINE:COLUMN` | Describe the name or expression at a position: its meaning, its type, and its definition's signature |
| `truss dependents NAME` | List the definitions that use a definition |
| `truss dependencies NAME` | List the definitions that a definition uses |
| `truss rename FROM TO` | Rename a definition, method, or module, and every reference to it |
| `truss add PACKAGE...` | Add registry packages as dependencies, granted nothing |
| `truss upgrade [PACKAGE...]` | Move registry packages to their newest versions |
| `truss publish VERSION` | Publish the package to the registry as `VERSION`, such as `1.4.2` |
| `truss status` | List the databases the background process holds |
| `truss stop` | Stop the background process |

- **Every command** takes `-C DIRECTORY`, to run as if from that directory,
  and `--json`, to print one JSON document in place of the report.
- **The exit status** is 0 when the code has no error, 1 when it has one,
  and 2 when the command could not run.
- **The commands share a background process** that keeps the project's
  checked state in memory, so a command after a small edit is fast. If a
  command reports that the database "is open in another process", the
  `truss` executable was rebuilt while the old process ran. It exits within
  a minute, or at once with `truss stop`. `--no-server`, or
  `TRUSS_NO_SERVER=1`, runs a command in its own process.
- **`TRUSS_CC`** names the C compiler, and **`TRUSS_Z3`** the Z3 executable.
- **A release build has a line table,** so a profiler, a debugger, and
  `objdump -S` attribute machine code to the Truss line it came from. Run
  `objdump -S` in the project's directory, where the table's file names
  resolve. Code that Truss generates, such as a drop, is on `<generated>`,
  and the runtime is on `<runtime>`. A release build keeps frame pointers,
  so `perf record -g` records call stacks. On macOS, `truss build` writes
  the line table to `PATH.dSYM` beside the program, where profilers and
  debuggers find it.

`truss show` takes a path to any definition, including the standard
library's, and a prelude name alone:

| To find | Run |
|---|---|
| A prelude type and its methods | `truss show String`, `truss show List`, `truss show Map` |
| One method | `truss show StringSlice.split` |
| A capability's methods | `truss show Console` |
| A module's public definitions | `truss show standard::json` |
| A whole definition, body and all | `truss show standard::console::strip_styles --body` |

The methods of the built-in integer types belong to the traits
`FixedWidthInteger`, `SignedInteger`, and `UnsignedInteger`: `truss show
FixedWidthInteger` lists them. `truss show standard` prints every public
definition of the standard library, over ten thousand lines, so show one
module at a time.

## Appendix D: The Standard Library

Every module is used as `use standard::name`, then `name::Item`.

| Module | Holds |
|---|---|
| `arguments` | A command-line parser with flags, values, subcommands, and help text |
| `base32`, `base64`, `hex` | Encoding bytes as text and back |
| `binary` | Encoding and decoding binary formats in either byte order |
| `checksum` | CRC, Adler, and xxHash checksums |
| `collections` | `Deque`, `Heap`, `SortedMap`, `SortedSet`, `BitSet`, and `LruCache` |
| `compression` | Compressing and decompressing data |
| `console` | `CapturedConsole`, terminal colors and styles, and reading a secret |
| `cron` | Parsing cron schedules and running work on them |
| `cryptography` | Hashing, message authentication, ciphers, signatures, and key agreement |
| `csv` | Reading and writing CSV |
| `cursors` | The cursor adapters: `Skip`, `Take`, `Zip`, `Chain`, `Enumerate`, `Peekable`, `StepBy` |
| `der`, `x509`, `jwk`, `jwt` | Certificates, keys, and tokens |
| `environment` | `FixedEnvironment`, and the platform, architecture, and well-known directories |
| `files` | `MemoryFiles`, `FilesWithin`, file handles, metadata, globs, and helpers such as `copy` and `create_directories` |
| `html` | The `Html` template, escaping, and sanitizing |
| `http` | An HTTP client and server, routes, cookies, forms, and CORS and CSRF policies |
| `json` | Parsing, encoding, and decoding JSON, and the `json::Value` template |
| `list`, `map`, `set` | `List`, `Slice`, `Map`, and `Set`, which are in the prelude |
| `log` | Logging, with levels, fields, `ConsoleLog`, and `DiscardLog` |
| `mail` | Sending mail over SMTP |
| `math` | `BigInteger`, `Decimal`, and statistics such as `mean` and `median` |
| `metrics` | Counters, gauges, and histograms |
| `network` | Connections, listeners, datagrams, and IP addresses |
| `otp`, `password` | One-time passwords and password hashing |
| `processes` | Running programs, with the `Command` template |
| `random` | `below`, random bytes, `Generator`, and `SeededRandom` |
| `regex` | The `Regex` template and matching |
| `serialization` | The `Serialize` and `Deserialize` traits that every format shares |
| `simulation` | `World`, a deterministic simulated machine for tests |
| `specification` | `Sequence`, `FiniteSet`, and `FiniteMap`, the types of specifications |
| `streams` | Buffered readers and writers over handles |
| `tasks` | `Channel`, `Cell`, `Counter`, `Limiter`, `Pool`, `SeededTasks`, and `with_timeout` |
| `text` | `String`, `StringSlice`, `Parse`, and `FromTemplate` |
| `time` | `Instant`, `Duration`, dates, time zones, layouts, `FixedClock`, and `ManualClock` |
| `tls` | TLS clients and servers |
| `toml` | Parsing, encoding, and decoding TOML |
| `trace` | Trace context for distributed tracing |
| `unicode` | Character categories, normalization, case folding, and display width |
| `url` | Parsing and building URLs, and the `Url` template |
| `uuid` | UUIDs: random, time-ordered, and from names |
