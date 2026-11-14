# Truss Language Specification

This document defines the Truss language: its grammar, and the rules that
decide a program's semantics and whether it compiles. [DESIGN.md](DESIGN.md)
gives the reasons for these rules, [PACKAGES.md](PACKAGES.md) defines
packages, and the Markdown files beside the modules of
[`standard/`](standard) document the standard library.

## Notation

The grammar is written in EBNF:

| Notation | Meaning |
|---|---|
| `rule = ... ;` | Defines `rule` |
| `"fn"` | The literal token `fn` |
| `UPPER_NAME` | A token class, defined in [Lexical elements](#lexical-elements) |
| `a b` | `a` followed by `b` |
| `a \| b` | `a` or `b` |
| `[ a ]` | `a`, optional |
| `{ a }` | `a`, zero or more times |
| `( a )` | Grouping |

`list(item)` is a comma-separated list that may be empty and may end with a
comma. `lines(item)` is items separated by line breaks:

```ebnf
list(item)  = [ item { "," item } [ "," ] ] ;
lines(item) = [ item { NEWLINE item } ] ;
```

[`grammar/truss.mly`](grammar/truss.mly) is the whole grammar written for
Menhir. A test checks that it accepts every example in the repository's
documents and every Truss file of the repository that the parser accepts, and
that it rejects inputs the parser rejects.

Some examples show a signature without a body. In a program, every function
has a body, except a method declared in a trait or a capability.

## Source files

- A source file is UTF-8. A byte order mark may appear only as the first
  character, and is ignored.
- Tab and space are whitespace. A carriage return followed by a line feed is
  one line break; a carriage return on its own is an error.
- Each language version names one Unicode version, which every rule here
  that uses a Unicode property follows.

These characters are an error anywhere in a file, including inside string
literals, because they can make code display differently from how it
compiles:

- the bidirectional controls: U+061C, U+200E, U+200F, U+202A to U+202E, and
  U+2066 to U+2069
- U+0000 to U+001F, U+007F, and U+0080 to U+009F, except tab, line feed, and
  a carriage return before a line feed
- every other character with the Unicode property
  `Default_Ignorable_Code_Point`, except U+200C, U+200D, and the variation
  selectors

An ordinary string writes such a character as an escape, such as `\u{2068}`.

## Lexical elements

```ebnf
token = UPPER_NAME | LOWER_NAME | "_" | keyword
      | INTEGER | FLOAT | STRING | TAGGED_STRING
      | punctuation | NEWLINE ;
```

Whitespace and line feeds separate tokens, and a line feed becomes a
`NEWLINE` only as [Line breaks](#line-breaks) says. Truss has no comments.

### Names

```ebnf
letter   = "a" ... "z" | "A" ... "Z" ;
raw_name = letter { letter | digit | "_" } ;
```

A `raw_name` that is a keyword is that keyword. Otherwise it is an
`UPPER_NAME` if it starts with an uppercase letter, and then contains no
`_`. It is a `LOWER_NAME` otherwise, and then contains no uppercase letter,
does not end with `_`, and does not contain `__`.

A letter outside ASCII where a name is written is an error. The lexer reads
the whole word, as Unicode's `XID_Start` and `XID_Continue` define one, and
reports it once.

Types, constructors, traits, and capabilities are `UpperCamelCase`. Values,
constants, functions, fields, modules, and files are `lower_snake_case`. In a
pattern, `Circle` is therefore a constructor and `radius` a binding.

### Keywords

Reserved everywhere:

```text
any assert break capability concurrent continue cost decreases derives echo else
ensures exists false fn for forall if impl in indirect internal invariant is law
lends let match mut opaque own parallel proof provide public requires return self
Self test theorem todo trait true type unreachable use uses var while with
```

Reserved for later use, and an error if written:

```text
as async await const defer extern loop macro static unsafe where
```

The lexer has no contextual keywords. These words are names to it,
`LOWER_NAME`s except `O`. The parser recognizes them by their spelling where
the grammar shows them, and
name resolution gives the rest their meaning:

```text
amortized time allocations allocated_bytes calls O finite potential
log power result old by bit_vector
```

| Words | Meaning |
|---|---|
| `amortized`, `time`, `allocations`, `allocated_bytes`, `calls`, `O`, `finite`, `potential` | The fixed words of a `cost` clause |
| `time(...)`, `calls(...)` | The cost functions, inside a `cost` bound |
| `log(...)`, `power(...)` | Functions on exact integers, inside a specification |
| `result` | The return value, inside `ensures` and `cost` |
| `old(e)` | The value of `e` when the function was called, inside a specification |
| `identical(a, b)` | Whether two values of one type are the same value, inside a specification |
| `visited` | In a `for` loop's clauses, the `Sequence` of the values of the iterations before |
| `final(result)` | In a lending method's `ensures`, the lent part as the caller left it |
| `by`, `bit_vector` | After an `assert`'s condition: `assert condition by bit_vector` |

A parameter cannot be named `result`, a parameter of a lending method cannot
be named `final`, and no function can be named `old` or `identical`.
Elsewhere the words are ordinary names: in
`fn wait(time: Duration) cost time O(time.seconds())`, the second `time` is
the resource and the third the parameter.

### Number literals

```ebnf
INTEGER  = whole | "0x" hex_digits | "0b" binary_digits | "0o" octal_digits ;
FLOAT    = whole "." decimal [ exponent ] | whole exponent ;
exponent = "e" [ "+" | "-" ] decimal ;

whole         = "0" | nonzero_digit { [ "_" ] digit } ;
decimal       = digit { [ "_" ] digit } ;
hex_digits    = hex_digit { [ "_" ] hex_digit } ;
binary_digits = binary_digit { [ "_" ] binary_digit } ;
octal_digits  = octal_digit { [ "_" ] octal_digit } ;

digit         = "0" ... "9" ;
nonzero_digit = "1" ... "9" ;
hex_digit     = digit | "a" ... "f" | "A" ... "F" ;
binary_digit  = "0" | "1" ;
octal_digit   = "0" ... "7" ;
```

A number literal is never directly followed by a name character, so `3u8`
is an error.

A literal takes its type from its context, as in `let small: UInt8 = 3`. A
local declared from literals alone takes its type from its first use that
decides it: after `let limit = 10`, `count < limit` with a `UInt8` count makes
`limit` a `UInt8`, and so does `let digit: UInt8 = index` in the body of
`for index in 0..10`. When nothing decides it, an integer literal is an
`Int64` and a float literal a `Float64`.

- A literal operand of an arithmetic operator, a comparison, or a range takes
  the other operand's type when it can be that type: in `count + 1` with a
  `UInt8` count, the `1` is a `UInt8`. Otherwise it has its default type, as
  the `2` in `duration * 2` does. An expression made only of literals waits
  for the same decision.
- A literal shift amount is a `USize`.
- An integer literal is never a float.
- A literal that does not fit its type is an error. A negated literal is
  checked after the negation, so `-128` fits an `Int8`.
- A literal of `USize` or `ISize` fits in 32 bits, except in the standard
  library.
- A literal whose type is a type parameter bounded by an integer trait fits
  every type that implements the trait: -128 to 127 under `SignedInteger`, 0
  to 255 under `UnsignedInteger`, and 0 to 127 under `FixedWidthInteger`.

### String literals

```ebnf
STRING        = ordinary_string | raw_string ;
TAGGED_STRING = UPPER_NAME string_start ;

ordinary_string = '"' { ordinary_char | escape | interpolation } '"' ;
ordinary_char   = ? any character except '"', '\', and a line feed ? ;
escape          = '\n' | '\t' | '\r' | '\0' | '\\' | '\"' | '\${'
                | '\u{' hex_digit [ hex_digit ] [ hex_digit ] [ hex_digit ]
                        [ hex_digit ] [ hex_digit ] '}' ;

raw_string = { "$" } quotes raw_body quotes ;
quotes     = '"""' { '"' } ;

interpolation = "${" expression "}" ;
```

The lexer returns a string literal as one token, with each interpolation
already split into the tokens of its expression. A `TAGGED_STRING` has no
whitespace between its tag and the string; a module path before the tag, as
in `database::SqlQuery"..."`, is ordinary tokens.

- `\0` is NUL, and `\${` is the text `${`. A `\u{...}` escape names a Unicode
  scalar value.
- A raw string has no escapes. Its closing delimiter has as many quotes as
  its opening one, at least three, and a longer run of quotes is an error.
- If the opening delimiter is followed by a line feed, the raw string is
  multi-line. Spaces and tabs between the delimiter and the line feed are
  ignored. The closing delimiter is on a line of its own, and the whitespace
  before it is the indentation, which every other line starts with and
  which is removed. A line of only whitespace that does not start with the
  indentation is an empty line. The line feeds after the opening delimiter
  and before the closing one are not part of the string.
- Otherwise the raw string is on one line, and its text cannot start or end
  with `"`.
- A line break in a raw string is `\n`, whatever line endings the file uses.
- In an ordinary string and a raw string opened with no `$`, an
  interpolation starts at `${`. In a raw string opened with *n* `$`s, it
  starts at *n* `$`s followed by `{`. Every other `$`, `{`, and `}` is text.
- The lexer counts braces inside an interpolation and lexes strings inside
  it recursively, so `"Players: ${names.join(", ")}"` is one string. An
  interpolation contains no line break and is not empty.

```truss
let query = SqlQuery"""
  select name, email
  from users
  where id = ${user_id}
    and active = true
  """

let script = Shell$$"""
  echo "${HOME}/$${folder}"
  """
```

`query` starts with `select`, and its `and` line keeps two spaces. In
`script`, `${HOME}` is text and `folder` is interpolated.

### Punctuation

```text
(  )  [  ]  {  }  ,  :  ::  .  ..  ..=  ->  =>  ?  |
=  +=  -=  *=  /=  %=  &=  |=  ^=  <<=  >>=
+  -  *  /  %  ==  !=  <  <=  >  >=  &&  ||  ==>  !  &  ^  ~  <<  >>
```

The lexer takes the longest match.

### Rejected sequences

These sequences are errors:

```text
//  /*  #  ;  '  `  @  ++  --  ===  !==
```

`--` is rejected even where it could be two negations, and `//` is never two
divisions.

### Line breaks

A line feed becomes a `NEWLINE` token exactly when the token before it can
end a statement and the token after it can begin one, outside `(` and `[`.
The lexer keeps a stack of open brackets, `(`, `[`, and `{`:

1. While the innermost open bracket is `(` or `[`, line feeds are skipped.
2. Otherwise, a line feed becomes a `NEWLINE` token when both of these hold:
   - the last token before it **can end a statement**: a name, `_`, a number
     or string literal, `)`, `]`, `}`, `?`, `true`, `false`, `self`, `Self`,
     `todo`, `unreachable`, `break`, `continue`, `return`;
   - the first token after it **can begin a statement**: a name, `_`, a
     number or string literal, `(`, `[`, `{`, `-`, `!`, `~`, a reserved word,
     or one of the keywords `any`, `assert`, `break`, `capability`,
     `concurrent`, `continue`, `echo`, `exists`, `false`, `fn`, `for`,
     `forall`, `if`, `impl`, `internal`, `law`, `let`, `match`, `mut`, `own`,
     `parallel`, `proof`, `provide`, `public`, `return`, `self`, `Self`,
     `test`, `theorem`, `todo`, `trait`, `true`, `type`, `unreachable`,
     `use`, `var`, `while`.
3. Several line feeds in a row produce at most one `NEWLINE`.
4. At the end of the file, a `NEWLINE` follows the last token if it can end a
   statement.

So no `NEWLINE` comes before a closing `}`, and statements, arms, and members
are separated by `NEWLINE`s. The parser skips a `NEWLINE` before a `{` that
must open a body. A line that starts with `.`, `else`, a clause keyword, or a
binary operator other than `-` continues the line before:

```truss
let active_names = users
  .filter(fn(user) { user.is_active })
  .map(fn(user) { user.name.copy() })
```

## Files and definitions

```ebnf
file        = { use NEWLINE } { definition NEWLINE } ;
use         = "use" module_path ;
module_path = LOWER_NAME { "::" LOWER_NAME } ;

definition = [ visibility ] ( function | type_definition | trait
                            | capability | constant | theorem )
           | impl | test | law_proof ;
visibility = "public" [ "opaque" ] | "internal" ;
```

Each directory of a package is a module, and its files share one namespace
(see [Module paths](#module-paths)). Nothing about a definition depends on
its file or its position in the file.

### Scope

- A name in a body is looked up in its scope, then among the definitions of
  its module, then in the prelude.
- A local, a parameter, or a generic parameter cannot hide another of an
  enclosing scope, or a prelude name. `let name = name.trim()` is an error.
- A local or a parameter may hide a function, a constant, or a theorem of
  its module, so adding a definition to one file breaks no local in another.
- A generic parameter cannot hide a type, a trait, or a capability of its
  module. An `impl`'s head declares the names in its brackets, so
  `impl Shown for Box[Marker]` would otherwise mean every `Box` where the
  type `Marker` was meant.
- Module names are a namespace of their own, written only before `::`. A
  variable can be named `url` in a file that imports the `url` module.
- `::` reaches into a module, and `.` into a type or a value.

## Types

### Built-in types

| Type | Values |
|---|---|
| `Int8`, `Int16`, `Int32`, `Int64` | Signed integers |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | Unsigned integers |
| `USize`, `ISize` | Unsigned and signed integers of 32 or 64 bits |
| `Float32`, `Float64` | IEEE 754 binary floating point |
| `Bool` | `true` and `false` |
| `String` | UTF-8 text |
| `Character` | A Unicode scalar value |
| `Array[Element, count]` | Exactly `count` elements, stored in place |
| `Unit` | One value, also written `Unit`: the result of a function that returns nothing |
| `Never` | No values: the result of a function that never returns |

A package is verified for both widths of `USize` and `ISize` unless its
manifest says `usize_bits = 64` (see [PACKAGES.md](PACKAGES.md#package-manifest)).
Integer types never convert implicitly.

### Type definitions

```ebnf
type_definition = "type" UPPER_NAME [ generics ]
                  ( fields | "=" variants | "=" "todo" )
                  { type_clause } ;
fields          = "(" list(field) ")" ;
field           = LOWER_NAME ":" type [ "=" expression ] ;
variants        = [ "|" ] variant { "|" variant } ;
variant         = [ "indirect" ] UPPER_NAME [ fields ] ;
type_clause     = "invariant" expression
                | "derives" path_type { "," path_type }
                | "cost" "potential" expression ;
```

```truss
type Point(x: Float64, y: Float64)

type Shape =
  | Circle(center: Point, radius: Float64)
  | Rectangle(corner: Point, opposite_corner: Point)
  | Empty

type Option[Value] =
  | Some(value: Value)
  | None

type DiscardLog()
```

```truss
let origin = Point(x: 0.0, y: 0.0)
let unit_circle = Shape.Circle(center: origin, radius: 1.0)
let answer = Some(3)
```

- A record has named fields; a sum type has variants, each with fields or
  none. Truss has no tuples and no type aliases.
- A value is built the way a function is called (see
  [Calls and arguments](#calls-and-arguments)), and a field can have a
  default, as a parameter can.
- In an expression, a variant is written under its type, as in
  `Shape.Circle`, and from another module under the module too, as in
  `geometry::Shape.Circle`. The prelude's `Some`, `None`, `Ok`, and `Err`
  are written bare.
- A `type_clause` after the last variant belongs to the whole type.
- The order of a record's fields has no meaning, except to a derived
  `Ordered`.
- A record with one field has the representation of its field, and none of
  its methods or operators: `type UserId(number: UInt64)` is a type of its
  own.

### Recursive types

```truss
type Expression =
  | Number(value: Int64)
  | indirect Sum(left: Expression, right: Expression)
  | Call(function: String, arguments: List[Expression])
```

- An `indirect` variant keeps its fields on the heap, in one allocation.
  Building one costs one allocation, which `cost` clauses count; changing or
  moving its fields allocates nothing.
- Every cycle of types that contain each other passes through an `indirect`
  variant or a collection. A record cannot contain itself.
- A variant that is not recursive may be `indirect` too.
- In its own fields, at any depth, a type does not occur in the input of a
  function type with a `time` clause:
  `type Knot(run: (fn(Knot) -> Bool cost time finite))` is an error. A
  function stored in a `Knot` could call itself through it, so its `time`
  clause would be proven for a function that does not terminate.

### Type expressions

```ebnf
type           = path_type
               | "Self" [ "." UPPER_NAME ]
               | UPPER_NAME "." UPPER_NAME
               | "any" path_type
               | function_type
               | "(" function_type { function_type_clause } ")" ;

path_type      = [ module_path "::" ] UPPER_NAME [ type_arguments ] ;
type_arguments = "[" type_argument { "," type_argument } [ "," ] "]" ;
type_argument  = type | INTEGER | LOWER_NAME | UPPER_NAME "=" type ;
```

- `Items.Element` names an associated type of a type parameter.
- An `INTEGER` or `LOWER_NAME` argument is the value of a `USize` generic
  parameter, as in `Array[UInt8, 32]`.
- `UPPER_NAME "=" type` constrains an associated type, as in
  `Iterable[Element = Int64]`.

### Generic parameters

```ebnf
generics          = "[" generic_parameter { "," generic_parameter } [ "," ] "]" ;
generic_parameter = UPPER_NAME [ ":" bound ]
                  | LOWER_NAME ":" type
                  | "capability" UPPER_NAME ;
bound             = path_type { "+" path_type } ;
```

- A `LOWER_NAME` parameter has type `USize`, and its value is known when the
  code is compiled.
- A `capability` parameter stands for a set of capabilities (see
  [Capability parameters](#capability-parameters)). Only a function, a
  method, or a theorem takes one.
- Generic code is compiled once for each set of type arguments. So a generic
  function cannot call itself, or a function in a cycle with it, with a type
  argument built from its own type parameters, and a generic type cannot
  contain itself with other arguments.

### Invariants

```truss
public type DateRange(start: Date, end: Date)
  invariant start <= end

public type Interval =
  | Closed(low: Int64, high: Int64)
  | Unbounded
  invariant match self {
    Closed(low, high) => low <= high
    Unbounded => true
  }
```

- `self` names the value, and a record's fields can be named directly.
- Repeated invariants all hold, and each may rely on the ones before it.
- A function called in an invariant is pure and has a `time` clause.
- Invariants are proven, never checked when the program runs. An invariant
  holds wherever other code can see the value: when it is built, directly
  or with `with`, passed to a call, or returned, and when the function that
  holds it ends. A `with` is checked after all of its updates.
- A private method that takes `mut self` is a step of an update: the
  invariant of its `self` is neither assumed when it is called nor required
  when it returns. It states its precondition and postcondition with
  `requires` and `ensures`:

  ```truss
  fn SortedList[Element: Ordered].sift_into_place(mut self, index: USize)
    requires index < self.items.length()
    requires is_sorted(self.items[..index])
    ensures is_sorted(self.items)
  {
    todo
  }
  ```

## Values and ownership

Every variable holds its own value, and no two names refer to one value
that either can change. There are no stored references and no lifetimes.

- **A place** is a variable, `self`, or a constant, followed by any number of
  field accesses and indexes: `config.servers`, `scores[0]`. A constant is a
  read-only place.
- **A temporary** is any other value. It is handed over as owned.
- **An owned value is needed** by a `var`, an `own` parameter, a record field,
  a collection element, and a return value. A place there is marked `own`,
  which moves it, or copied with `copy()`.
- **There is no mutable global state.** A top-level `let` is a constant, and
  `var` is allowed only inside functions.

### Copying

- **`Plain` types copy implicitly.** A type made only of fixed-size data with
  nothing on the heap, such as the integers, floats, `Bool`, `Character`,
  and records, sum types, and `Array`s built only from those, is `Plain`.
- **`Copyable` types have `copy()`.** An implicit copy never allocates.
- **Handles are not `Copyable`,** nor is a type that holds one.
- `Copyable` and `Plain` are prelude traits that the compiler implements and
  no `impl` can, and `Plain` requires `Copyable`. The compiler derives them
  from a type's fields, except for an opaque type, which has them only when
  it declares them with `derives`. The compiler checks the declaration, and
  other packages rely only on it.
- A generic type has them under the conditions its fields give, and
  `any Trait` is `Copyable` only when `Trait` requires it. Generic code
  copies only where a bound allows it.

### Views

A read-only parameter, a `let` bound to a place, the variable of a
`for x in items` loop, and a slice refer to the original value instead of a
copy:

```truss
let middle = items[1..4]
let total = middle.sum()
mut items.push(9)
```

While a view is in use, its original cannot be changed or moved. Here `push`
is allowed because `middle` is not used after it. The compiler checks this
within each function.

- **Being a view is a property of a type.** `Slice`, `StringSlice`, and a
  lambda that reads local variables are views, and so is any type that holds
  one anywhere, such as a cursor over a slice. An `any Trait` is a view
  unless `Trait` requires `Storable`.
- **`Storable`** is the prelude trait of every type that is not a view,
  which the compiler derives and no type declares.
- **A view never outlives the function that made it.** It can be bound, held
  in local records and collections, and passed as an argument, but it cannot
  go where a `Storable` value is needed, and putting it in a record or a
  list makes that a view.
- **A function returns a view only of the places its parameters view, or of
  the parameters themselves.** The caller treats the result as viewing
  everything that its read-only and view arguments view. Arguments that are
  `Plain` lend nothing.
- **A function keeps only the views it is given:** to keep a view of an
  argument in a `mut` parameter or `mut self`, it takes the argument as a
  `Slice`, a `StringSlice`, or a function. A value cannot keep a view of its
  own part.
- A `var` can hold a view that never leaves the function.
- **`mut` access is never stored.** It has a name only as a `mut` parameter,
  a `mut` loop's variable, or a lambda's `mut` parameter, and lasts for that
  call, iteration, or `provide mut` block. Disjoint parts of one `List`,
  `Slice`, or `Array` can be passed `mut` side by side, as in
  `sort(mut items[..middle])` and `sort(mut items[middle..])`, when the
  prover shows that they do not overlap.
- **A temporary is dropped at the end of its statement,** except where a
  `let` keeps it until the end of the block that holds the `let`. A `let`
  keeps the base of a slice that it binds, directly or through fields. It
  also keeps such a base in a field of a record or variant that its value
  constructs, in a field that a `with` replaces, and in an element of an
  array literal. So `let middle = make_list()[1..4]` keeps the list for as
  long as `middle` can be used. A `let` keeps no other temporary, such as the
  receiver in `let part = make_list().slice()`. A view cannot be used after
  the temporary or the local that it views is dropped.
- **The one implicit conversion** is a `List` passed to a `Slice` parameter,
  or a `String` to a `StringSlice` parameter, which becomes a view of it.

## Constants

```ebnf
constant      = "let" constant_name ":" type "=" expression ;
constant_name = LOWER_NAME | type_head "." LOWER_NAME ;
```

```truss
public let pi: Float64 = 3.141592653589793
public let UInt8.maximum: UInt8 = 255
public let seconds_per_day: Int64 = 24 * 60 * 60
```

- The value is a *constant expression*: literals, arithmetic on numbers,
  other constants, and records, variants, lists, maps, arrays, sets, and
  strings built from those. It calls no function. The compiler evaluates it,
  building a `Map` or `Set` with the standard library's compiled code and no
  random hash key.
- A constant lives in static memory. Reading it or taking a view of it costs
  nothing, an owned value from it is made with `copy()`, and it is never
  marked `own` or `mut`.

## Functions

```ebnf
function      = "fn" function_name [ generics ] parameters [ result ]
                { clause } body ;
function_name = LOWER_NAME | type_head "." LOWER_NAME ;
type_head     = [ module_path "::" ] UPPER_NAME [ generics ] ;

parameters    = "(" list(parameter) ")" ;
parameter     = [ mode ] "self"
              | LOWER_NAME ":" [ mode ] type [ "=" expression ] ;
mode          = "mut" | "own" ;

result        = "->" type | "lends" [ mode ] type ;
body          = block ;
```

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

- A function without a result type returns `Unit`.
- Inside a body, types are inferred one statement at a time: a variable's
  type comes from its own `let` or `var` and never changes. Where the
  statement alone cannot decide it, as in `var names = []`, the `let` has a
  type. The exception is a variable declared from literals alone (see
  [Number literals](#number-literals)).
- `self` is only the first parameter of a method (see [Methods](#methods)).

### Calls and arguments

```ebnf
argument = [ LOWER_NAME ":" ] expression ;
```

```truss
fn copy(source: Path, destination: Path)
  uses FileRead, FileWrite
fn connect(host: HostName, port: UInt16 = 443, secure: Bool = true) -> Result[Connection, NetworkError]
  uses NetworkClient

copy(original, destination: backup)
copy(source, destination)
let connection = connect(host, port: 8080)?
```

1. `label: value` passes `value` to the parameter named `label`.
2. A bare name that matches a parameter's name passes that variable to that
   parameter, wherever it appears, optionally after a mode keyword.
3. Any other first argument goes to the first parameter. Any other later
   argument is an error.
4. Arguments come in the order of the parameters.

- A default is a constant expression that refers to no other parameter. An
  argument for a parameter with a default can be left out, and the function
  fills it in. An owned default is copied, which costs one counted
  allocation for a non-empty `List`, `Map`, or `Set`.
- Building a record or a variant follows the same rules, except that fields
  may come in any order, evaluated in the order written, and only a record
  or variant with exactly one field takes a bare value, as in `Some(3)`.
- A call through a function value passes its arguments by position.
- An `UpperCamelCase` name before `(` is always a type or a variant being
  built.

### Explicit type arguments

```truss
let value = parse[Int64](text)?
let builder = List[String].with_capacity(64)
```

Type arguments that cannot be inferred are written in brackets after the
function's name. Name resolution decides whether `name[...]` is type
arguments or an index (see
[Constructs resolved after parsing](#constructs-resolved-after-parsing)), and
a diagnostic about `f[X]` says which reading applied.

### Clauses

```ebnf
clause               = "uses" capability_list
                     | "requires" expression
                     | "ensures" expression
                     | "decreases" expression { "," expression }
                     | "cost" cost ;
capability_list      = capability_reference { "," capability_reference } ;
capability_reference = path_type
                     | "Self" "." UPPER_NAME
                     | UPPER_NAME "." UPPER_NAME ;
```

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

| Clause | Meaning | Count |
|---|---|---|
| `uses` | The capabilities the function may use. Without it, the function is pure. | At most one |
| `requires` | A precondition, proven at every call | Any |
| `ensures` | A postcondition, proven for the body | Any |
| `decreases` | A measure that proves recursion ends | At most one |
| `cost` | A proven bound on a resource | Any |

- Repeated clauses all hold. Each `requires` may rely on the `requires`
  before it, and each `ensures` on every `requires` and the `ensures`
  before it.
- No clause is evaluated when the program runs.
- `Self.Uses` and `Source.Uses` name an associated capability set (see
  [Associated capability sets](#associated-capability-sets)).

### Termination

- A function with a `time` clause terminates; `cost time finite` promises
  termination without a bound. A function without one may not terminate.
- A recursive call on a part of a parameter needs nothing written. A part is
  a field taken out by a pattern, or an element of a collection that is
  itself a part:

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

- Other recursion in a function with a `time` clause states `decreases`: an
  integer measure over the parameters that stays at or above zero and that
  every recursive call makes smaller. A list of measures is compared in
  order. Functions in a cycle of calls each state one. The compiler never
  guesses a measure.
- A function also reaches itself by naming a function as a value, and by
  using an `impl` where a bound needs one. Inside an `impl`'s methods, using
  that same `impl` is a recursive call to every method of the `impl`, and
  cannot be shown to decrease.

### Cost clauses

```ebnf
cost        = [ "amortized" ] resource bound ;
resource    = "time" | "allocations" | "allocated_bytes"
            | "calls" "(" call_target ")" ;
call_target = LOWER_NAME | path_type [ "." LOWER_NAME ] ;
bound       = "O" "(" expression ")" | "finite"
            | ( "<=" | "==" ) expression ;
```

```truss
public fn load_configs(paths: List[Path]) -> Result[List[Config], ConfigError]
  uses FileRead
  cost calls(FileRead.read) == paths.length()
  cost time O(paths.length())
```

- `finite` is a bound only of `time`.
- The target of `calls` is a function parameter, a capability method, or a
  whole capability, never an associated capability set.
- `O(f)` means that the cost is at most `c * f + d` for every input, for
  constants `c` and `d` that the prover finds.
- `time` counts abstract steps: each primitive operation and each call is one.
- A caller's cost is proven from its callees' cost clauses.

A bound is an expression on exact integers. It can use the parameters,
`self`, their fields, pure methods with a `time` clause, `result`, `+`, `*`,
and `/` and `-` where the result stays at or above zero, and:

| Term | Value |
|---|---|
| `log(n)` | The smallest integer at least log₂(n + 1) |
| `power(base, exponent)` | `base` to the `exponent` |
| `time(visit)` | A bound on any one call of the function parameter `visit` |
| `time(Element.equal)` | A bound on any one call of a method of a trait that bounds a type parameter, or `Self` in a trait |

- `time(visit)` cannot depend on `visit`'s arguments. It is a constant for a
  parameter of type `(fn(Item) cost time O(1))`, and a fixed bound that is
  not known for one with `cost time finite`.
- An operator counts as the method it calls: `==` spends
  `time(Element.equal)`, and `<` spends `time(Element.compare)`. If a name has
  several versions, the term means the read-only one.
- At a call, the term has the value the type argument gives it: a constant
  for `Int64`, whose `impl Equal` promises `cost time O(1)`.
- An `impl` that writes a method its trait provides keeps the provided
  method's bound.
- `log` and `power` have the same meaning in every specification. The prover
  knows `log` of a number exactly, and that `log` of a value of an integer
  type is at most the type's width. Outside a `cost` bound, a local or a
  definition of the file with either name takes precedence. Neither can be
  called in code that runs.

```truss
fn Slice[Element: Equal].contains(self, item: Element) -> Bool
  cost time O(self.length() * time(Element.equal))
```

#### Amortized costs

```truss
public opaque type List[Element](buffer: Buffer[Element], length: USize, capacity: USize)
  invariant length <= capacity
  cost potential growth_credit(length, capacity)

fn List[Element].push(mut self, item: own Element)
  cost amortized time O(1)
```

- A `cost potential` is an integer expression over a type's fields that never
  goes below zero. A value's potential is its type's potential plus its
  parts' potentials, and belongs to that value alone; `copy()` pays for the
  new one.
- `cost amortized time O(f)` promises that the actual cost, plus the change
  in the potential of the values the function changes or returns, is within
  `O(f)`. `amortized` works with every resource that takes an `O(...)` bound.
- A function may state a plain and an amortized bound on one resource. A
  caller with an amortized bound counts the amortized one, and any other
  caller the plain one.

### Function types

```ebnf
function_type        = "fn" "(" list([ LOWER_NAME ":" ] [ mode ] type) ")" [ "->" type ] ;
function_type_clause = "uses" capability_list | "cost" cost | "requires" expression ;
```

```truss
fn sort_by(items: mut List[Item], compare: fn(Item, Item) -> Ordering)
fn serve(handle: (fn(Request) -> Response uses Database, Log cost time finite))
```

- A function type without `uses` is pure, and one without a `time` clause may
  not terminate. Its `uses` and `cost` clauses cannot mention its inputs.
- Clauses after a definition's result type belong to the definition.
- A function type names its inputs exactly when it has a `requires`, which
  only the type of a definition's parameter, at its top, may have. The
  `requires` can mention the inputs and the parameters before it. The
  function meets it at every call through the parameter, a lambda passed for
  the parameter may rely on it, and a named function passed for it accepts
  every argument it allows:

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

- A function-typed parameter can be called but not kept. One declared `own`
  can be kept, and accepts only functions that read no local variables.

### Capability parameters

```truss
public fn for_each[Item, capability Granted](
  items: List[Item],
  visit: (fn(Item) uses Granted cost time finite),
)
  uses Granted
  cost calls(visit) == items.length()
  cost time O(items.length() * time(visit))
```

A capability parameter passes on whatever capabilities a callback uses. A
type that holds a function writes the capabilities in the field's type.

### Parameter modes

A parameter is read-only by default. `mut` lets the function change the
caller's value, and `own` gives the function ownership of it. A place
passed to a `mut` or `own` parameter repeats the keyword; a temporary is
never marked:

| Call | Meaning |
|---|---|
| `sort(mut scores)` | `scores` may change. |
| `push(mut names, item: own name)` | `name` is moved. |
| `push(mut names, item: name.copy())` | `push` gets a copy. |

A keyword before a longer expression marks the longest place the expression
starts with. The first method call after that place takes it as its
receiver, and the rest of the expression works on that call's result:

| Expression | Marked place |
|---|---|
| `mut config.servers.sort()` | `config.servers` |
| `mut config.load_servers().sort()` | `config`, for `load_servers` |
| `sort(mut items[..middle])` | `items[..middle]` |

An expression that does not start with a place cannot be marked.

`own` can move one field out of a record. The record's other fields stay
usable, and the whole record is usable again once the field is assigned. A
place lent `mut` can be moved out of in the same way:

```truss
fn Option[Value].take(mut self) -> Option[Value] {
  let previous = own self
  self = None
  previous
}
```

- The place is a `mut` parameter, `mut self`, the variable of a `mut` loop, a
  `mut` binding of a `match`, or a lambda's `mut` parameter, or a field of
  one.
- It is assigned again on every path before the function returns or the
  iteration or arm ends. Until then it is not read.

## Methods

```truss
fn List[Element].with_capacity(capacity: USize) -> List[Element]

fn List[Element].push(mut self, item: own Element)

fn List[Element: Ordered].sort(mut self)
  cost time O(self.length() * log(self.length()))

fn List[Element].map[Output](self, transform: fn(Element) -> Output) -> List[Output]
```

- A method is a function declared as `fn Type.name`. One whose first
  parameter is `self` can be called with a dot, and every method can be
  called through its type's name: `List.length(names)` is `names.length()`.
- `self` has the type named before the dot, and is written `self`,
  `mut self`, or `own self`.
- The type's generic parameters go before the dot, with any bounds the
  method needs, and the method exists only where those bounds hold. The
  method's own go after its name.
- A method is defined in its type's package, in a file where the type is
  visible. From another module, the type is named with its module:
  `fn hourly::Forecast.summary(self) -> String`.

### Versions by receiver mode

```truss
fn List[Element: Copyable].filter(self, keep: fn(Element) -> Bool) -> List[Element]
fn List[Element].filter(own self, keep: fn(Element) -> Bool) -> List[Element]
```

A method can have up to three versions that differ only in the mode of
`self`. The keyword at the call picks the version, no keyword picks the
read-only one, and a temporary receiver uses the `own` version if there is
one. A version may come from a trait that the type implements in its own
package (see [Method lookup](#method-lookup)). Truss has no other
overloading.

### Lending methods

A *lending* method, with `lends` in place of a result type, lends its caller
one part of `self` for the rest of the caller's statement.

```truss
fn Grid.cell(mut self, position: Position) lends mut Cell {
  mut self.cells[position.row * self.width + position.column]
}

mut grid.cell(position).visit()
```

- `lends Cell` lends read-only access, and `lends mut Cell` lends `mut`
  access, marked on the place: `mut part`.
- **The method lends the value of its body, or of a `return`.** No code of
  the method runs after it lends. The values it still owns are dropped when
  the lend ends.
- **The part is lent for the rest of the caller's statement,** even if the
  statement leaves early.
- **In the condition of an `if` or a `while`, the part is lent for the
  condition alone** when each name the condition binds is a copy: a `Plain`
  name that is not a view and is not bound `mut`. The guarded block can then
  change the receiver, as in
  `if counts.get(word) is Some(count) { counts[word] = count + 1 }`. A name
  that is not a copy aliases the part, which stays lent until the then-block
  or the body ends. It is never lent into the `else` block.
- **For that long, the receiver is lent whole:** the statement makes no other
  use of a receiver lent `mut`, and does not change one lent read-only. Two
  indexes or slices of one `List`, `Slice`, or `Array` can be lent together
  when the prover shows that they do not overlap.
- The `mut` on the receiver chooses the version that lends `mut`, and the
  part is then changed with no mark of its own.
- **A lent part is not the caller's to keep.** It is not moved, returned,
  stored, or bound with `let`, except by copying it.
- The part need not be stored in `self`: the method may lend a value it
  made, which is dropped when the lend ends.
- **A method lends a part of its first parameter, or a whole value that it
  made.** A caller keeps only the first argument lent, so it could change or
  drop another argument while a part of it is lent, a use after free. The
  method does not lend a part inside a value it owns either, such as an
  element of a list it built: the method drops the value where it returns,
  and the part would dangle. A part whose type is `Plain` is lent as a copy,
  so it can come from anywhere. A part that is a view may view any
  parameter, as a returned view may.

The lent value may be a constructor applied to places:

```truss
fn Slice[Element].get(self, index: USize) lends Option[Element] {
  if index < self.length() {
    Some(self[index])
  } else {
    None
  }
}
```

- An argument of the lent constructor that is a place is lent, with no copy.
  Constructors nest.
- Every other field is a place, a nested constructor, or a `Plain` value.
- A `mut` lend marks each place it lends `mut`, and the caller's changes to
  a marked field reach the place when the lend ends. Two places lent `mut`
  by one method are different places.
- **A place lent `mut` is never inside a variant,** at any depth: the caller
  could replace the variant, and the place would have no value, a use after
  free.
- The built value owns nothing it was lent.

#### Contracts of lending methods

```truss
fn List[Element].element(mut self, position: USize) lends mut Element
  requires position < self.count()
  ensures identical(result, old(self.model())[position])
  ensures identical(self.model(), old(self.model()).update(position, value: final(result)))
{
  mut self[position]
}
```

- **A clause that mentions `result` holds where the method lends,** where
  `result` is the lent part, and the caller may rely on it.
- **Every other clause holds when the lend ends.**
- **`final(result)` is the part as the caller left it,** as `old(value)` is
  a value when the method was called.

### Cursors

A *cursor* gives values one at a time. It is a value of a type that
implements the prelude trait `Cursor`:

```truss
trait Cursor {
  type Element
  capability Uses
  fn next(mut self) -> Option[Self.Element]
    uses Self.Uses
}
```

```truss
type Countdown(left: USize)

impl Cursor for Countdown {
  type Element = USize

  fn next(mut self) -> Option[USize] {
    if self.left == 0 {
      return None
    }
    self.left -= 1
    Some(self.left)
  }
}
```

- `next()` returns `Some` of the next value, which the caller owns, or
  `None` when the cursor has no more.
- A cursor holds its own state. One that holds a view, such as a cursor over
  a `Slice`, is a view. One that owns a collection gives its elements away.
- `Uses` is the set of capabilities that `next` uses. Each `next` uses the
  implementations provided where it is called.
- `Cursor` gives a cursor the methods `to_list`, `count`, `last`, `fold`,
  and `find`, and the adapters of `standard::cursors`, such as `skip`,
  `take`, and `zip`.

## Statements and blocks

```ebnf
block     = "{" lines(statement) "}" ;

statement = "let" pattern [ ":" type ] "=" expression [ "else" block ]
          | "var" pattern [ ":" type ] "=" expression [ "else" block ]
          | expression [ assignment_operator expression ]
          | "for" pattern [ ":" type ] "in" expression { loop_clause } block
          | "while" expression { loop_clause } block
          | "parallel" block
          | "parallel" "for" pattern [ ":" type ] "in" expression { loop_clause } block
          | "concurrent" block
          | "concurrent" "for" pattern [ ":" type ] "in" expression { loop_clause } block
          | "proof" block
          | "assert" expression [ "by" "bit_vector" ] ;

assignment_operator = "=" | "+=" | "-=" | "*=" | "/=" | "%="
                    | "&=" | "|=" | "^=" | "<<=" | ">>=" ;
loop_clause = "invariant" expression | "decreases" expression { "," expression }
            | "cost" cost ;
```

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

- `let` binds immutable names and `var` mutable ones.
- A block's value is its last expression. Blocks, `if`, and `match` are
  expressions.
- The left side of an assignment is a place.
- **Every value is used.** A statement whose value is not `Unit` is an error;
  `let _ = expression` discards a value.
- **Every variable is used.** A binding that nothing reads is an error.
  Parameters are exempt.
- **Unreachable code is an error:** a statement after an expression of type
  `Never`. The check uses types alone, so `if false { ... }` is not
  reported. Code after a `todo` is exempt.
- `return`, `break`, `continue`, and `unreachable` have type `Never`. `break`
  and `continue` appear only in loops.
- `assert` appears only in tests, theorems, and proofs. In a proof it is
  proven, and in a test it is checked when the test runs.
- `assert condition by bit_vector` is proven alone, for every value of the
  integers and booleans it names, with its bitwise operations exact, and then
  holds where it is written. It names only integers and booleans. A fact it
  needs from the proof around it is a hypothesis it states:
  `assert used < 64 ==> (word >> used) == 0 by bit_vector`.

### Patterns

```ebnf
pattern         = pattern_primary { "|" pattern_primary } ;
pattern_primary = "_"
                | LOWER_NAME
                | range_end [ ( ".." | "..=" ) range_end ]
                | [ module_path "::" ] UPPER_NAME [ pattern_fields ]
                | pattern_fields ;
range_end       = literal_pattern | constant ;
literal_pattern = [ "-" ] INTEGER | "true" | "false" | plain_string
                | [ module_path "::" ] TAGGED_STRING ;
constant        = module_path "::" LOWER_NAME
                | [ module_path "::" ] UPPER_NAME "." LOWER_NAME ;
pattern_fields  = "(" list(pattern_field) ")" ;
pattern_field   = LOWER_NAME ":" pattern | pattern | ".." ;
```

```truss
match shape {
  Circle(radius, ..) => todo
  Rectangle(corner, opposite_corner) => todo
  Empty => todo
}

match status_code {
  http::ok => todo
  301 | 302 | 307 => todo
  500..=599 => todo
  code if code >= 400 => todo
  _ => todo
}
```

- A variant pattern names the variant without its type or its module, and
  the variant is looked up in the type of the scrutinee. A record pattern
  has no type name.
- A bare name that matches a field binds that field to a variable of the
  same name. `field: pattern` matches one field. In a record or variant with
  exactly one field, a bare pattern matches that field.
- Fields can be written in any order, and `..`, the remaining fields, comes
  last.
- A bare name binds, in every pattern. A constant is written with its module
  or its type, `http::ok` or `Status.teapot`, so adding a constant never
  changes what a pattern matches. A constant in a pattern has a type with
  structural equality (see [Equality](#equality)).
- Range patterns match integers and characters.
- Every alternative of an or-pattern binds the same names, with the same
  types.
- A pattern in `let`, `var`, `for`, or a lambda's parameters matches every
  value of its type.

### `match`

```ebnf
match = "match" expression { "," expression } "{" lines(arm) "}" ;
arm   = pattern { "," pattern } [ "if" expression ] "=>" statement ;
```

- An arm's body is a statement. When the `match` is used as a value, an arm
  whose body is not an expression has type `Unit`.
- A guard takes the arm only when the patterns match and the guard is true.
- **A `match` covers every case.** An arm with a guard never counts toward
  covering its patterns.
- **Every arm is reachable.**
- A `match` on several values has one pattern per value in each arm. No
  tuple is made, and coverage and reachability are checked across all the
  values.

### `is`

```truss
if response is Ok(body) && body.length() > 0 {
  render(body)
}

while queue.pop() is Some(task) {
  run(task)
}
```

`value is pattern` is `true` when the value matches. The names the pattern
binds can be used only where the test is known to be true: in the rest of an
`&&` chain, in the block of the `if` or `while`, and in an arm whose guard
contains the test.

### `let ... else`

```truss
let Some(user) = find_user(id) else {
  return Err(LoginError.UnknownUser(id))
}
greet(user)
```

- The names the pattern binds are in scope in the rest of the enclosing
  block.
- The `else` block has type `Never`.
- The expression before `else` does not end with `}`.

### Updating records

```ebnf
update = LOWER_NAME { "." LOWER_NAME } ":" expression | LOWER_NAME ;
```

```truss
let moved = origin with (x: 1.0)
let production = own config with (server.port: 443, log_level: LogLevel.Warning)
```

- `base with (updates)` means copying the base into a new variable,
  assigning its fields, and returning it.
- The base is handed over as an `own` argument is. An owned base is reused
  in place, so the update costs one write per field.
- `with` works on records, and updates only fields visible at that point.

### Lambdas

```ebnf
lambda = "fn" "(" list(pattern) ")" block ;
```

```truss
let passing = scores.filter(fn(score) { score >= threshold })
mut scores.update_each(fn(score) { score = score / 2 })
```

- A lambda's parameter types, modes, and result type come from the function
  type it is passed as. Types are inferred from the outside in, never from
  the lambda's body. Where nothing gives a lambda a function type, the `let`
  has a type or the call has type arguments.
- A lambda reads local variables through views and cannot change them. A
  lambda that reads local variables is a view; one that reads none can be
  returned, stored, and moved.
- A lambda's capabilities are inferred from its body.
- `return` and `?` leave the lambda. `break` and `continue` do not reach a
  loop outside it.
- A lambda is always passed inside the call's parentheses.

### Errors

```truss
fn load_config(file: Path) -> Result[Config, ConfigError]
  uses FileRead
{
  let text = FileRead.read_text(file).map_error(ConfigError.Unreadable)?
  let config = toml::parse(text).map_error(ConfigError.Malformed)?
  Ok(own config)
}
```

- `?` after a `Result` returns its error from the enclosing function
  unchanged, so the error type is the function's. `?` after an `Option` works
  in a function that returns an `Option`. `?` never converts.
- A variant with exactly one field can be used as a function.

### Loops

| Loop | Meaning |
|---|---|
| `for score in scores { ... }` | Read each element. |
| `for score in mut scores { ... }` | Change elements in place. |
| `for item in own items { ... }` | Move each element out. |
| `while low < high { ... }` | Loop while a condition holds. |

- **A `for` loop over a collection visits its elements by position.**
  `for item in items` evaluates `items.count()` once, and each iteration is
  lent `items.element(position)`, for each position from zero up to the
  count. A type supports `for` by defining `count(self) -> USize` and
  `element(self, position: USize)`, a lending method, as its own methods or
  by implementing `Iterable`.
- `for item in mut items` is lent each element by the version of `element`
  that takes `mut self`. A `mut` loop changes elements but does not add or
  remove them: each iteration leaves the collection's `count` as it was.
- `for item in own items` moves each element out: it pulls the cursor that
  `items.cursor()` returns, where `cursor` takes `own self`.
- **A `for` loop over a cursor pulls it until it has no more values.** Each
  iteration owns the value that `next` returned. A cursor in a variable is
  advanced in place, so it can be pulled again after a `break`.
- A `for` loop's type annotation is its element type, as a `let`'s is the
  type of its value: `for index: UInt8 in 0..10` iterates over `UInt8`s, and
  `for (index, element): Indexed[UInt8] in data.enumerate()` destructures
  each `Indexed[UInt8]`. The annotation must be the element type: it never
  converts the elements.
- A `while` whose condition is the literal `true`, and that no `break`
  leaves, has type `Never`.
- `invariant` holds at the start of every iteration and when the loop ends.
- `decreases` names a measure that every iteration makes smaller and that
  never goes below zero. A `while` loop in a function with a `time` clause is
  proven to terminate, and so is a `for` loop over a cursor. A `for` loop
  over a cursor whose type has a `remaining(self) -> USize` method has that
  method's value as its measure where it states none.
- In the clauses of a loop over a range, the loop variable is the index of
  the next iteration: in `for i in start..end`, `i` is `start` on entry and
  `end` where the loop ends, and `end + 1` after `start..=end`.
- In the clauses of any other `for` loop, `visited` is the `Sequence` of the
  values of the iterations before. The clauses cannot name the element. A
  local named `visited` hides the word.
- In a loop that reads a collection, `visited[i]` is the value of the
  collection's `element` at position `i`, so it meets that method's
  `ensures`. Where the collection's `model()` is the `Sequence` of its
  elements, as a `List`'s is, `visited` is that model once the loop has
  visited every element.
- A loop's `cost` bounds the loop's cost so far, at the start of every
  iteration and when it ends. It is never `amortized` or `finite`. Its bound
  can use the variables in scope at the loop, and `visited` or a range's
  index:

  ```truss
  fn sum_all(rows: List[List[Int64]]) -> Int64
    cost time O(rows.length() + rows.model().sum(fn(cells) { cells.length() }))
  {
    var total = 0
    for row in rows
      cost time O(visited.length() + visited.sum(fn(cells) { cells.length() }))
    {
      for cell in row {
        total = total.saturating_add(cell)
      }
    }
    total
  }
  ```

  `sum` adds a measure of each element of a `Sequence`. The measure is a
  function that terminates and uses no capabilities, and two lambdas with
  the same body are the same measure.

### Ranges

- `start..end` excludes `end`, and `start..=end` includes it. A range whose
  start is at or past its end is empty.
- A range of characters holds the characters between its ends in the order
  of their code points.
- A range with no start or no end is allowed only directly in brackets, as in
  `items[2..]`.

### Collection literals

```ebnf
map_entry = expression ":" expression ;
```

| Literal | Value |
|---|---|
| `[2, 3, 5, 7]` | A `List`, or an `Array`, a `Set`, or a type of specifications where one is expected |
| `[]` | An empty one of the same |
| `["http": 80, "https": 443]` | A `Map`, or a `FiniteMap` where one is expected |
| `[:]` | An empty `Map` |

- An `Array` literal has exactly as many elements as its type says.
- A non-empty list literal in a function body counts as one allocation, and
  an empty one as none.
- A set or map literal makes an empty collection with room for every
  element, then calls `insert` for each element in order, and costs as much
  as those calls. `insert` requires a key that is not there yet, so a map
  literal's keys are proven distinct.

### Indexing

| Indexing | Meaning |
|---|---|
| `items[i]` | Element `i`, which is proven in bounds |
| `items[1..4]` | A `Slice`, whose bounds are proven |
| `ports[name]` | The value for `name`, which is proven present |
| `items[i] = value` | Replaces element `i` |
| `ports[own name] = 8080` | Inserts or replaces the value for `name` |

- A type supports `[]` by implementing the prelude trait `Index` (see
  [Associated types](#associated-types)), which lends an element read-only.
- A type whose elements change in place also implements `IndexMut`, whose
  `at(mut self, key)` lends an element `mut`. `items[i].name = text`,
  `items[i] += 1`, and `mut items[i]` need it.
- `collection[key] = value` calls `assign` when the type implements
  `IndexAssign`. The collection must accept the key, by its `accepts_key`:
  a `Map` accepts every key and inserts a missing one, and a `BitSet`
  accepts the keys it has. For any other type, the assignment replaces the
  element that `IndexMut` lends, so the key is there.
- A type that computes its elements, such as a `BitSet`, implements `Index`
  and `IndexAssign` and not `IndexMut`: it has no place to lend `mut`.
- Strings cannot be indexed.

## Expressions

```ebnf
expression = "echo" expression
           | "return" [ expression ]
           | implication
           | bitwise ;

implication = [ logical "==>" ] ( logical | quantified ) ;
quantified  = quantifier
            | comparison { "&&" comparison } "&&" quantifier
            | comparison { "||" comparison } "||" quantifier ;
quantifier  = ( "forall" | "exists" ) binder "=>" expression ;
binder      = pattern "in" expression | LOWER_NAME ":" type ;

logical     = comparison { "&&" comparison }
            | comparison "||" comparison { "||" comparison } ;

comparison  = range [ comparison_operator range ]
            | range "is" pattern ;
comparison_operator = "==" | "!=" | "<" | "<=" | ">" | ">=" ;

range          = additive [ ( ".." | "..=" ) additive ] ;
additive       = multiplicative { ( "+" | "-" ) multiplicative } ;
multiplicative = prefix { ( "*" | "/" | "%" ) prefix } ;

bitwise    = prefix "&" prefix { "&" prefix }
           | prefix "|" prefix { "|" prefix }
           | prefix "^" prefix { "^" prefix }
           | prefix ( "<<" | ">>" ) prefix { ( "<<" | ">>" ) prefix } ;

prefix     = ( "-" | "!" | "~" ) prefix
           | ( "mut" | "own" | "any" ) postfix
           | postfix ;

postfix    = primary { "." LOWER_NAME
                     | "." UPPER_NAME
                     | "[" brackets "]"
                     | "(" list(argument) ")"
                     | "?"
                     | "with" "(" list(update) ")" } ;
brackets   = expression
           | [ additive ] ( ".." | "..=" ) [ additive ]
           | type_argument { "," type_argument } [ "," ] ;

primary    = INTEGER | FLOAT | STRING | [ module_path "::" ] TAGGED_STRING
           | "true" | "false" | "todo" | "unreachable" | "break" | "continue"
           | "self" | "Self"
           | LOWER_NAME
           | [ module_path "::" ] UPPER_NAME
           | module_path "::" LOWER_NAME
           | "(" expression ")"
           | "[" list(expression) "]"
           | "[" ":" "]"
           | "[" map_entry { "," map_entry } [ "," ] "]"
           | lambda
           | if
           | match
           | provide
           | block ;

if         = "if" expression block [ "else" ( if | block ) ] ;
```

- The grammar is the precedence: precedence is a partial order. Bitwise
  operators combine only with themselves, `&&` and `||` do not mix,
  comparisons, `is`, ranges, and `==>` do not chain, and `!` cannot be the
  left operand of `is`. Each of those needs parentheses, and a missing pair
  is an error with a fix that adds them.
- `return` and `echo` take everything after them. A `{` right after
  `return`, on the same line, starts the returned value.
- The brackets after a name in an expression hold expressions, which cover
  type names and their arguments but not function types.

### Operators

`==` and `!=` call the `Equal` trait, and `<`, `<=`, `>`, and `>=` call
`Ordered`. Both sides have the same type, and functions and `any` values
cannot be compared. `!` works on `Bool`, `~` on integers, and negation on
signed integers and floats.

The arithmetic operators call traits with a type parameter for the right
side and an associated type for the result:

| Operator | Trait | Defined where |
|---|---|---|
| `a + b` | `Add[Right]` | `add_is_defined(right)` |
| `a - b` | `Subtract[Right]` | `subtract_is_defined(right)` |
| `a * b` | `Multiply[Right]` | `multiply_is_defined(right)` |
| `a / b` | `Divide[Right]` | `divide_is_defined(right)` |
| `a % b` | `Remainder[Right]` | `remainder_is_defined(right)` |
| `-a` | `Negate` | `negate_is_defined()` |

```truss
public trait Add[Right] {
  type Output

  fn add_is_defined(self, right: Right) -> Bool
    cost time finite

  fn add(self, right: Right) -> Self.Output
    requires self.add_is_defined(right)
}
```

- Each operation requires its `_is_defined` method. For a fixed-width
  integer, an operation is defined where its result fits the type and,
  for `/` and `%`, where the divisor is not 0 and the operation is not
  `minimum / -1`. A float operation is defined everywhere.
- The built-in number types implement these traits only with themselves on
  both sides. The bitwise operators and shifts work only on the built-in
  integer types.

#### Compound assignment

- `a += b` and the other compound assignments are statements whose left side
  is a place. `a += b` means `a = a + b` with the place evaluated and
  checked once.
- The old value of `a` is handed to the operator as owned, so a version of
  the trait's method that takes `own self` can update in place.

#### Evaluation order

- Operands, arguments, and fields are evaluated in the order written.
- `target = value` evaluates `value`, then the index keys of `target`, and
  then stores.
- `target += operand` evaluates `operand`, then the index keys of `target`,
  once, then takes the old value of `target` and stores the result. A `?`
  that leaves from `operand` leaves `target` unchanged.
- `&&`, `||`, and `==>` evaluate their right side only when the left does
  not decide the result.

### Integers

- **No integer operation overflows silently.** An operation that could
  overflow is proven not to, or the code calls the standard library's
  checked, wrapping, or saturating version.
- `/` rounds toward zero, and `%` has the sign of its left operand.
- `>>` on a signed integer copies the sign bit, and on an unsigned integer
  shifts in zeros. A shift amount is any unsigned integer type, proven
  smaller than the bit width of the value.
- Unsigned integers cannot be negated.
- A proof about `USize` or `ISize` holds for both widths, unless the package
  says `usize_bits = 64`.
- The traits `FixedWidthInteger`, `SignedInteger`, and `UnsignedInteger` are
  sealed: only the built-in integer types implement them.

### Floats

- Float arithmetic follows IEEE 754. NaN and infinity are values, so no
  float operation fails.
- Float results are the same on every platform. The operations IEEE 754
  defines exactly are never contracted or reordered.
- `==` treats every NaN as equal to every other NaN, and otherwise follows
  IEEE 754, so `-0.0 == 0.0`. In ordering, NaN comes after every number.

## Failure

Code stops abruptly only where its signature says it can, except by running
out of memory or overflowing the stack.

Every operation that can fail is a proof obligation: integer overflow,
division by zero, indexing or slicing out of bounds, a shift that is too
large, and `unreachable`. Where the compiler cannot prove one safe, the code
is an error, and one of these makes it compile:

1. Establish the fact locally, as with an `if`.
2. Require it with `requires`.
3. Call a version that returns an `Option` or a `Result`.
4. Declare `uses Panic`.

`unreachable` admits only the first.

`Panic` is a built-in capability. `Panic.crash(message)` prints its message
and location to standard error and ends the process with a nonzero exit
code, and no Truss code runs afterward. No code can `provide` `Panic`, so a
panic cannot be caught.

## Capabilities

```ebnf
capability = "capability" UPPER_NAME "{" lines(signature) "}" ;
provide    = "provide" expression { "," expression } block ;
```

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

- Code calls a capability's methods through its name, as in `Random.next()`,
  and never calls an implementation directly.
- An implementation is a type with an `impl`. Its methods take `self`, or
  `mut self` where they change its state.
- `provide implementation, ... { body }` runs the body with the given
  implementations, handed over as arguments are: a place is marked `mut` when
  its methods change it, and then holds the changes afterward.
- Providing a type provides every capability it implements.
- An `impl` with a `uses` clause can use those capabilities, and providing
  it requires them. Otherwise an `impl`'s methods use only the capabilities
  their trait or capability declares.
- **Inside an implementation, a call of the capability it implements goes to
  the next provider out.** So an implementation can check each call and pass
  it on, which narrows the capability.
- **A capability method always returns to its caller,** once.
- A capability's method keeps no view it is given, and returns no view of its
  implementation's state.
- A capability cannot be declared as a bundle of others.

### Standard capabilities

These capabilities are in the prelude:

| Capability | Allows |
|---|---|
| `Console` | Reading standard input, writing standard output and standard error |
| `FileRead` | Opening files to read, reading files, and listing directories |
| `FileWrite` | Creating, writing, renaming, and deleting files |
| `NetworkClient` | Opening outgoing connections and looking up names |
| `NetworkServer` | Listening for incoming connections |
| `Handles` | Using open handles: files, connections, listeners, and running programs |
| `Clock` | The current time, a monotonic clock, and sleeping |
| `Random` | Random numbers from the operating system |
| `Environment` | Environment variables, the current directory, and the platform |
| `Processes` | Running other programs |
| `Signals` | Waiting for a signal sent to the program |
| `Tasks` | Running `concurrent` code |
| `Log` | Writing to the program's log |
| `Panic` | Ending the program |

### Handles

A handle is a value that stands for something the operating system holds,
such as an open file. It is released when its owner is done with it, on
every path, and releasing it runs no Truss code and never fails. No type
defines code that runs when its value is released.

### main

A program starts at the `main` of its package's root module, the files in the
directory of its manifest:

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

`main` has this signature and any `uses` clause. The runtime provides the
real implementation of each capability in it, and nothing else. The program
ends when `main` returns or panics.

## Parallelism

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

- A `parallel` block runs each statement directly inside it, a *branch*, at
  the same time, and ends when all have ended. A `let` in a branch is in
  scope after the block.
- **Branches cannot race.** Any branch may read any place, and a place that
  one branch changes is used by no other branch.
- Branches use no capability but `Panic`, so a function that contains
  `parallel` is still pure.
- A branch cannot leave the block with `return`, `break`, `continue`, or `?`.
- A `parallel` block has the result of running its branches in order, and
  its `time` is the sum of theirs.
- `parallel for` runs a loop's iterations at the same time, by the same
  rules. Its body changes only its own element and its own variables, and
  may use `continue`.

## Concurrency

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

- A `concurrent` block runs each branch as a task, and ends when every task
  has ended. A `concurrent for` runs each iteration as a task. The enclosing
  function declares `uses Tasks`.
- Branches follow the rules of `parallel` branches, except that they may use
  the capabilities of the code around them and may leave the block.
- **A branch that leaves the block with `?`, `return`, or `break` cancels the
  other branches,** waits for them to end, and then leaves. A branch that has
  not started does not start, and the first branch to leave decides where
  control goes.
- The code after the block does not run when a branch leaves early, so a
  branch that moves a value out of a place reinitializes it before it ends.
- **In a cancelled task, a standard capability call that would wait returns
  at once:** an `Err` of `SystemError.Cancelled` where it returns a
  `Result`, `None` where it returns an `Option`, and early where it returns
  nothing. `Tasks.cancelled()` tells whether the task is cancelled. A task
  blocked on the mutex of a `mut` implementation waits until it acquires it.
- A function that waits for another task has no `time` clause.

The iterations of a `parallel for` and of a `concurrent for` run at the same
time, and a `concurrent for` iteration keeps running after the loop
advances.

- An iteration that reads its element is lent it for the whole loop, from
  any collection.
- **Only a `List`, a `Slice`, or an `Array` lends its elements `mut` to such
  a loop.** Its elements at different positions are different places.
  Another collection's `element` could lend one place to two iterations: a
  data race.
- **A `concurrent for` over a cursor pulls values that are not views.** The
  next pull could change or drop what a view from the cursor views, which
  would leave the task with a dangling view.

### Shared state

When the code inside a `provide mut` can use `Tasks`, as known from the
signatures it calls, including through a capability parameter, the
implementation's calls are mutually exclusive: each holds the
implementation's mutex from start to end. Such an implementation has no
method with a parameter that can hold a function, or an `any` value, that
uses a capability, so its mutexes cannot deadlock. An implementation
provided without `mut` has no mutex.

The standard library's `tasks` module holds channels, limits on how many
tasks run at once, and cells that tasks update (see
[`standard/tasks.md`](standard/tasks.md)).

## Strings

- A string literal is a `String` in static memory, copied to the heap the
  first time it is changed. Making one, and `copy()` of one, cost nothing.
- `StringSlice` is the view of a `String`.
- There is no concatenation operator: `+` on strings is an error, and
  adjacent literals do not join.
- A value in `${...}` has a type that implements `Display`.

### Tagged templates

```truss
let query = SqlQuery"select name from users where id = ${user_id}"
let pattern = Regex"[a-z]+@${domain}"
```

- The tag, a type name without type arguments, is the type of the result. A
  plain string is the case where the tag is `String`.
- A type is a tag by implementing the prelude trait `FromTemplate`. Its
  associated type `Part` is the type each interpolated value is converted to,
  and its method `from_template` takes a `Template[Part]`, which holds the
  literal text as `text::Literal` values, which only the compiler makes, and
  the converted values.
- A tag's `from_template` states the rules for valid literal text with `requires`.
  The literal text is known when the code is compiled, so the compiler proves
  the `requires` by running the check, as compiled code. `Regex"[a-z"` is an
  error.
- `from_template` is the one method whose `requires` may be stronger than its
  trait's, and a call of it through a bound or `any` is an error.

```truss
impl FromTemplate for Regex {
  type Part = RegexPart

  fn from_template(template: Template[RegexPart]) -> Regex
    requires is_valid_template(template.literals)
  {
    todo
  }
}
```

`Character"é"` holds exactly one Unicode scalar value and `UInt8"\n"`
exactly one ASCII character, checked when the code is compiled, with no
interpolation.

## Traits and laws

```ebnf
trait        = "trait" UPPER_NAME [ generics ] [ ":" bound ]
               "{" lines(trait_member) "}" ;
trait_member = signature [ body ]
             | "type" UPPER_NAME [ ":" bound ]
             | "capability" UPPER_NAME
             | "law" LOWER_NAME parameters { "requires" expression } block ;
signature    = "fn" LOWER_NAME [ generics ] parameters [ result ] { clause } ;

impl            = "impl" path_type "for" type_head [ "uses" capability_list ]
                  "{" lines(impl_member) "}" ;
impl_member     = function_member
                | "type" UPPER_NAME "=" type
                | "capability" UPPER_NAME "=" capability_list ;
function_member = signature body ;
```

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

- A `law` holds for every implementation and every set of values that meets
  its `requires`. It uses only methods with a `time` clause and no
  capabilities, and an `impl`'s method keeps its trait's `time` clause.
- A trait's contracts and costs bind every `impl` and are proven for each.
- **An `impl`'s method may promise more than its trait:** `ensures` and
  `cost` clauses of its own, and a `requires` that the trait's implies. A
  call known to reach that `impl` is proven against the `impl`'s contract,
  and a call through a bound or `any` against the trait's.
- **Required traits:** a type implements the traits a trait requires before
  it implements the trait, and a bound includes them. A trait cannot
  redeclare a method of a trait it requires, but can add a version in
  another mode. Traits cannot require each other in a cycle.
- **A method with a body** is provided to every implementation. An `impl` can
  replace it only with a version proven to give the same result, and only
  where the prover reads the body as a definition (see
  [Bodies and contracts in proofs](#bodies-and-contracts-in-proofs)).

### Implementations

- A type has at most one `impl` of each trait for each set of the trait's
  type arguments, whatever the type's own arguments, and every `impl` is
  written out for its type.
- An `impl` for a generic type states its conditions on the type's
  parameters, as in `impl Display for List[Element: Display]`.
- An `impl` lives in the package of the trait, of the implementing type, or
  of the outermost type of one of the trait's arguments.
- An `impl` applies wherever its trait and the types it names are visible.
- With a trait that takes type parameters, the `impl` is chosen by the types
  of the arguments, inferred first without looking at which `impl`s exist,
  and never by the expected result type.

### Associated types

```truss
trait Index {
  type Key
  type Output
  fn contains_key(self, key: Self.Key) -> Bool
    cost time finite
  fn at(self, key: Self.Key) lends Self.Output
    requires self.contains_key(key)
}
```

A trait's associated type is chosen by each `impl`, with `type Key = ...`,
which appears only in an `impl`.

### Associated capability sets

```truss
impl Cursor for Chain[First: Cursor, Second: Cursor[Element = First.Element]] {
  type Element = First.Element
  capability Uses = First.Uses, Second.Uses
  fn next(mut self) -> Option[First.Element]
    uses Self.Uses
  { todo }
}

fn count[Source: Cursor](source: own Source) -> USize
  uses Source.Uses
```

- `capability Uses` in a trait declares a set of capabilities that each
  `impl` defines, as a list of capabilities, capability parameters, and the
  sets of its type's parameters. An `impl` that leaves it out has the empty
  set, and its methods use only the set's capabilities.
- `Self.Uses` and `Source.Uses` name the set in a `uses` clause. A call needs
  the set's capabilities for its type arguments. A function generic over a
  `Cursor` that advances it declares `uses Source.Uses`.
- A bound cannot constrain a set, and `calls(...)` cannot count one.

### Equality

A type's equality is *structural* when two equal values cannot be told apart
by any function, so the prover concludes `f(a) == f(b)` from `a == b`. The
built-in integers, `Bool`, `Character`, `Unit`, `String`, and the types of
specifications have it, and so does a type that derives `Equal` when all its
fields do. A hand-written `Equal`, float equality, and an opaque type's
equality outside its package are not structural.

### Deriving

```truss
type Priority =
  | Low
  | Normal
  | Urgent(deadline: Instant)
  derives Equal, Ordered
```

| Trait | Derived implementation |
|---|---|
| `Equal` | Equal variants with equal fields |
| `Hash` | Combines the hashes of the fields |
| `Ordered` | Variants in declaration order, then fields in declaration order |
| `Default` | Each field's default, for a record |
| `Copyable`, `Plain` | Nothing: an opaque type declares that it copies (see [Copying](#copying)) |

- Every field has the trait, and a derived trait's required traits are
  derived too: `Ordered` and `Hash` need a derived `Equal`.
- A generic type has a derived trait only where its parameters do.
- A derived implementation satisfies the trait's laws; a hand-written one
  proves them.
- `serialization::Serialize` and `serialization::Deserialize` can be derived
  too (see [`standard/serialization.md`](standard/serialization.md)).
- Every type has debug output, which needs no derive.

### Method lookup

- A call with a dot finds the type's own methods, and the methods of the
  traits it implements from the standard library, the calling package, and
  the packages the calling package's manifest lists. No trait is imported.
- Two of those traits giving one name is an error at a call with a dot,
  which is then written in full: `Ordered.compare(first, second)`. A trait
  and a trait it requires are the exception.
- A type's own method and a trait method it implements are never the same
  name with the same mode. An `impl` in the type's own package may add
  another version of a name the type has, by writing the method. A method
  an `impl` leaves to its trait's body, and every method of an `impl` in
  another package, takes no name the type's methods have.

### Values of any type with a trait

```truss
type Server(handlers: List[any Handler])

mut server.handlers.push(any HealthCheck())
```

- `any value` takes ownership of the value and allocates once, which `cost`
  clauses count.
- `any` names one trait, and fixes each of its associated types, as in
  `any Cursor[Element = Int64]`, and each of its associated capability sets
  to the empty set.
- A method can be called through `any` if it takes `self` in any mode, has no
  generic parameters, and does not take or return `Self`.
- An `any` value cannot be converted back to its type.

## Tests

```ebnf
test = "test" plain_string [ "uses" capability_list ] block ;
```

```truss
test "config loads with defaults" {
  let disk = files::MemoryFiles.new().with_text(Path.new("app.toml"), contents: "")
  let config = provide disk, log::DiscardLog() {
    load_config(Path.new("app.toml"))
  }
  assert config == Ok(Config.default())
}
```

- `plain_string` is a `STRING` with no interpolation.
- A test provides every capability its code uses, except `Panic`, unless it
  declares them with `uses`. A test with `uses` is *external*: it gets the
  real implementations of exactly those capabilities, and runs every time the
  suite runs. Any other test is deterministic, and its result is kept until
  its code changes.
- A failed test is never retried.
- A failed `assert` ends the test as failed, and the rest of the test can
  rely on the asserted fact.
- A test does not wait for proofs. A test build checks every primitive
  operation that could fail when it runs, and a failed check fails the
  test. A `requires` is not run.
- A panic fails only its test. A test that reaches a `todo` is incomplete.
- A test that runs past the project's time limit fails.

## Proofs

```ebnf
theorem   = "theorem" LOWER_NAME [ generics ] parameters { clause } block ;
law_proof = "proof" path_type "." LOWER_NAME "for" type_head block ;
```

Every promise is proven before a program is built: contracts, cost clauses,
invariants, laws, loop invariants, and every operation that could fail.
There is no `assume`.

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

proof Ordered.transitive for Box[Item: Ordered] {
  box_order_is_transitive(first, second: second, third: third)
}
```

- A theorem's `requires` are its assumptions, its `ensures` its conclusions,
  and its body the proof, using calls, `let`, `match`, `if`, and `assert`. An
  empty body asks the prover to prove it alone.
- Calling a theorem makes its `ensures` available. A theorem that calls
  itself on smaller input is a proof by induction.
- A `proof { }` block in a function body holds the statements a theorem's body holds,
  and is removed from the compiled program.
- A law proof's body is checked as the law's body is: it names the law's
  read-only parameters, `Self` is its type, and the law's `requires` hold. A
  proof for a generic `impl` names the type as the `impl` does, and is
  proven once for every type.

### Bodies and contracts in proofs

- A function or a method of a type is known to its callers' proofs by its
  `requires` and `ensures`, in every package. A function whose body is its
  meaning states it in its `ensures`:
  `ensures result == (forall index in 1..items.length() => items[index - 1] <= items[index])`.
- A method of a trait or an `impl` is known by its body, where the body is
  functional: `let`, `if`, `match`, `is`, calls, fields, building values,
  `with`, operators, and quantifiers, with no `var`, assignment, or loop, and
  nothing passed `mut` or `own`. A trait's provided method is read in every
  package, and a method an `impl` writes in the `impl`'s package.
- A clause is read only where everything it reads is visible.
- A function with a `requires` is defined only where it holds.

### Writing specifications

A *specification* is a `requires`, `ensures`, `decreases`, or `cost` clause,
an invariant, a law, or a proof.

- A function called in a specification is pure, with no `uses` at all, and
  has a `time` clause.
- Every specification is well defined: each call meets its callee's
  `requires`, and each index is in bounds. `&&`, `||`, `==>`, and `if` read
  left to right, so the right side can rely on the left.
- `==` is the type's `Equal`, and `identical(a, b)` is identity, for any type.

| Form | Meaning |
|---|---|
| `forall index in 0..count => items[index] >= 0` | True for every value in a range or a collection |
| `forall value: Int64 => value + 0 == value` | True for every value of a type |
| `exists item in items => item == target` | True for at least one value |
| `a ==> b` | When `a` holds, so does `b` |
| `old(self.items)` | A value as it was when the function was called |

- A quantifier over a range or a collection is also an expression in code,
  which runs as a loop that stops when the answer is known. Its body may rely
  on the bound name being in its range, and uses no capabilities.
- A quantifier over a type and `==>` appear only in specifications and in
  functions for specifications only.
- A quantifier's body runs to the end of the expression.
- Integer arithmetic in a specification is exact. It is done on `Integer`, a
  prelude type that exists only in specifications, of which every built-in
  integer type is a subset, so comparisons can mix integer types. An
  `Integer` can stand where a built-in integer is expected, and the prover
  shows that it fits.
- A function whose signature mentions a type that exists only in
  specifications is for specifications only: it is called only from
  specifications, never compiled, and its body is a specification.
- Float arithmetic in a specification follows IEEE 754.

The prelude types `Sequence`, `FiniteSet`, `FiniteMap`, and `Multiset` exist
only in specifications and have structural equality. A type gives its value
in their terms with the prelude trait `Model`, whose `model()` can be called
only in specifications:

```truss
fn List[Element].push(mut self, item: own Element)
  ensures identical(self.model(), old(self.model()).append(item))
  cost amortized time O(1)
{
  todo
}
```

## Unfinished code

```truss
fn render(report: Report) -> String {
  let header = render_header(report.title)
  let body = todo
  "${header}\n${body}"
}

public opaque type Session = todo
```

- `todo` stands for an expression of any type, a body, or a type's
  definition. The compiler reports each one with its type and the names in
  scope.
- Code with a `todo` is type-checked and proven, and callers are checked
  against the signature of an unfinished function.
- `truss build` and `truss run --release` refuse a program whose `main` can
  reach a `todo`. In a development build, a `todo` that runs stops the
  program and reports its position.
- A type defined as `todo` can be named, but its contents cannot be used.

## Debug output

```truss
fn score(player: Player) -> Int64 {
  let base = echo player.wins * 3
  base.saturating_add(echo bonus(player))
}
```

- `echo expr` records the value's debug output with its location and text,
  and returns the value. It needs no `uses`, and proofs and cost clauses read
  it as `expr`.
- In tests, the output is attached to the test's report, grouped by branch or
  task; otherwise it goes to standard error.
- It is not allowed in proofs. `truss build` and `truss run --release`
  refuse a program whose `main` can reach an `echo`, and a package that
  contains one cannot be published.

## Modules and visibility

```truss
use standard::json

let settings = json::parse(text)?
```

- `use` imports a module, never names. Every name that is not local, not a
  definition of the module, and not from the prelude is written with its
  module.
- A `use` belongs to its file. Each file of a module imports the modules it
  names.
- There are no import aliases. A full path works without a `use`, and
  importing two modules with the same last name is an error.
- An unused `use` is an error. A `use` is used when a module path in the
  file begins with its last name. A file with a syntax error reports no
  unused `use`, since the code that did not parse may use it.

### Module paths

Each directory of a package that holds a `.truss` file is a module, whose
path is the package's name, then the directory's names. The files of
`forecast/` in the `weather` package, such as `forecast/hourly.truss` and
`forecast/daily.truss`, are the module `weather::forecast`, and the files
beside the package's manifest are its root module, `weather`.

- The files of a module share one namespace: each names the others'
  definitions without a module, private ones included. Two files of a
  module cannot define one name.
- A file's name says nothing about its definitions. Moving a definition to
  another file of its module changes no path.
- A module's subdirectory is a module of its own: `forecast/hourly/` is
  `weather::forecast::hourly`, which names `weather::forecast` with `::`
  like any other module.
- Every path starts with a package name, including inside the package.
- There are no relative paths, and a path holds no version.
- File and directory names are `lower_snake_case`.
- The modules of a package may use each other in a cycle.

### The prelude

The prelude is in scope in every file, and all its names are
`UpperCamelCase`:

- the built-in types, `Option` and `Result`, and `List`, `Slice`, `Map`, and
  `Set`
- the core traits, such as `Equal`, `Ordered`, `From`, `TryFrom`, `Default`,
  `Copyable`, `Plain`, `Storable`, `Index`, `IndexMut`, `IndexAssign`,
  `Iterable`, `Cursor`, `FromTemplate`, `Model`, and the arithmetic traits
- `Integer`, `Sequence`, `FiniteSet`, `FiniteMap`, and `Multiset`
- the standard capabilities, and `Path`, `Instant`, `Duration`, and
  `SystemError`

No definition can have a prelude name, a project cannot change the prelude,
and the prelude changes only with a language version.

### Visibility

| Keyword | Visible to |
|---|---|
| *(none)* | The same module: every file of its directory |
| `internal` | The whole package |
| `public` | Every package |

- An `impl`, a test, and a law proof take no visibility.
- `opaque` appears only before `public type`. Outside its package, an opaque
  type's fields cannot be read, built, updated, or matched on. Visibility is
  set for a type as a whole.
- A public signature cannot mention a private or `internal` type, and
  neither can a public type's fields unless the type is opaque.
- The `requires` and `cost` of a public function, of a method of a public
  trait or capability, and of a method of an `impl` that other packages can
  use call no private or `internal` function and name no such constant. An
  `ensures` may name any function the definition can, so that callers in its
  package can know its result in terms of private helpers.

## No foreign code

Truss code cannot call code written in other languages. Only the standard
library reaches the operating system, through the compiler.

## Constructs resolved after parsing

| Construct | Decided by | How |
|---|---|---|
| `name[...]` | Name resolution | Type arguments if `name` is a generic function, a type, or a trait; otherwise an index. For a method, type checking decides. |
| A bare argument after the first | Type checking | Names a parameter or field of the callee |
| Whether an expression after `mut` or `own` starts with a place | Name resolution | It starts with a variable, a parameter, `self`, or a constant |
| A variant in a pattern | Type checking | Looked up in the type of the scrutinee |
| A method call or field | Type checking | Looked up in the type of the receiver |
| An `impl` of a trait with type parameters | Type checking | Chosen by the argument types, inferred first |
| The cost words, `log`, `power`, `result`, `old` | The parser and name resolution | The parser checks their spelling where a `cost` clause expects them |
| The expected type of `[...]` | Type checking | `List` unless another collection type is expected |

## Ambiguities in the grammar

The grammar has three shift/reduce conflicts, all resolved by shifting.
Precedence declarations in `grammar/truss.mly` resolve them, and the checks of
the reference parser fail on any other conflict:

- **`else` after `let pattern = if ... { } else { }`** attaches to the `if`.
  A `let ... else` expression that ends with `}` is rejected after parsing.
- **`{` after `return`** starts the returned value.
- **A name after `return`** starts the returned value, so in
  `assert return by bit_vector`, `by` is `return`'s operand and not the
  start of `by bit_vector`.

## Layout

`truss fmt` writes every file in one layout:

- It removes a byte order mark, indents with spaces, and writes line feeds
  only.
- It puts line breaks only where they continue a statement.
- It writes a sum type that fits on one line without the first `|`, and
  otherwise each variant on its own line starting with `|`.
- It removes `-> Unit`, and writes `x = x + y` as `x += y`.
- It orders clauses by kind, `uses`, `requires`, `ensures`, `decreases`,
  `cost`, keeping the order within a kind.
- It sorts `use` lines, and puts each element of a long literal on its own
  line.
- It never breaks a string or changes the text inside one, and removes
  spaces after an opening `"""`.
