# Truss Language Specification

This document defines the Truss language: its grammar, and the rules that
decide a program's semantics and whether it compiles. [DESIGN.md](DESIGN.md)
gives the reasons for these rules, and [PACKAGES.md](PACKAGES.md) defines
packages.

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
Menhir.

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

A letter outside ASCII where a name is written is an error.

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

These words are not reserved. Each has its meaning only where this table
says, and is an ordinary name elsewhere:

| Words | Meaning |
|---|---|
| `amortized`, `time`, `allocations`, `allocated_bytes`, `calls`, `O`, `potential` | The fixed words of a `cost` clause |
| `time(...)`, `allocations(...)`, `allocated_bytes(...)`, `calls(...)` | The cost functions, inside a `cost` bound |
| `log(...)`, `power(...)` | Functions on exact integers, inside a specification |
| `result` | The return value, inside `ensures` and `cost` |
| `old(e)` | The value of `e` when the function was called, inside a specification |
| `identical(a, b)` | Whether two values of one type are the same value, inside a specification |
| `visited` | In a `for` loop's clauses, the `Sequence` of the values of the iterations before |
| `final(result)` | In a lending method's `ensures`, the lent part as the caller left it |
| `by`, `bit_vector` | After an `assert`'s condition: `assert condition by bit_vector` |
| `generic` | In a `uses` list, before the name of a capability parameter |

A parameter cannot be named `result`, a parameter of a lending method cannot
be named `final`, and no function can be named `old` or `identical`. In
`fn wait(time: Duration) cost time O(time.seconds())`, the second `time` is
the resource and the third the parameter.

Inside a `cost` bound, a call of `log`, `power`, or a cost function always
names the function of the table. In any other specification, a local or a
definition of the module named `log` or `power` takes precedence.

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
- A literal shift amount is a `UInt64`.
- An integer literal is never a float.
- A literal that does not fit its type is an error. A negated literal is
  checked after the negation, so `-128` fits an `Int8`.
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

A `TAGGED_STRING` has no whitespace between its tag and the string.

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
- An interpolation ends at the `}` that matches its `{`, and may hold
  strings, so `"Players: ${names.join(", ")}"` is one string. An
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
end a statement and the token after it can begin one, outside `(` and `[`:

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
are separated by `NEWLINE`s. A `NEWLINE` before a `{` that must open a body
is ignored. A line that starts with `.`, `else`, a clause keyword, or a
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
- A local, a parameter, or a generic parameter cannot shadow another of an
  enclosing scope, or a prelude name. `let name = name.trim()` is an error.
- A local or a parameter may shadow a function, a constant, or a theorem of
  its module, so adding a definition to one file breaks no local in another.
- A generic parameter cannot shadow a type, a trait, or a capability of its
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
| `Float32`, `Float64` | IEEE 754 binary floating point |
| `Bool` | `true` and `false` |
| `String` | UTF-8 text |
| `Character` | A Unicode scalar value |
| `Array[Element, count]` | Exactly `count` elements, stored in place |
| `Unit` | One value, also written `Unit`: the result of a function that returns nothing |
| `Never` | No values: the result of a function that never returns |

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
- A record with one field has none of its field's methods or operators:
  `type UserId(number: UInt64)` is a type of its own.

### Recursive types

```truss
type Expression =
  | Number(value: Int64)
  | indirect Sum(left: Expression, right: Expression)
  | Call(function: String, arguments: List[Expression])
```

- An `indirect` variant keeps its fields on the heap, in one allocation.
  Building one costs one allocation, which `cost` clauses count; mutating or
  moving its fields allocates nothing.
- Every cycle of types that contain each other passes through an `indirect`
  variant or a collection. A record cannot contain itself.
- A variant that is not recursive may be `indirect` too.
- In its own fields, at any depth, a type does not occur in the input of a
  function type without `RunForever`: `type Knot(run: fn(Knot) -> Bool)` is
  an error. A function stored in a `Knot` could call itself through it, so
  it would be proven to terminate without a measure.
  `type Knot(run: (fn(Knot) -> Bool uses RunForever))` is legal.

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
- An `INTEGER` or `LOWER_NAME` argument is the value of a `UInt64` generic
  parameter, as in `Array[UInt8, 32]`.
- `UPPER_NAME "=" type` constrains an associated type, as in
  `Iterable[Element = Int64]`.

### Generic parameters

```ebnf
generics          = "[" generic_parameter { "," generic_parameter } [ "," ] "]" ;
generic_parameter = UPPER_NAME [ ":" bound ]
                  | LOWER_NAME ":" type ;
bound             = path_type { "+" path_type } ;
```

- A `LOWER_NAME` parameter has type `UInt64`, and its value is known when the
  code is compiled.
- A generic function cannot call itself, or a function in a cycle with it,
  with a type argument built from its own type parameters, and a generic
  type cannot contain itself with other arguments.

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
- Invariants are proven, never checked when the program runs. An invariant
  holds wherever other code can observe the value: when it is built,
  directly or with `with`, passed to a call, or returned, and when the
  function that holds it ends. A `with` is checked after all of its updates.
- A private method that takes `mut self` is a step of an update: the
  invariant of its `self` is neither assumed when it is called nor required
  when it returns. A method written in a trait, a capability, or an `impl`
  is never one: a caller that reaches it through the trait assumes that
  `self` meets its invariant when the call returns, and would otherwise
  observe a broken value. A step states its precondition and postcondition
  with `requires` and `ensures`:

  ```truss
  fn SortedList[Element: Ordered].sift_into_place(mut self, index: UInt64)
    requires index < self.items.length()
    requires is_sorted(self.items[..index])
    ensures is_sorted(self.items)
  {
    todo
  }
  ```

## Values and ownership

Every variable holds its own value, and no two names alias a value that
either can mutate. There are no stored references and no lifetimes.

- **A place** is a variable, `self`, or a constant, followed by any number of
  field accesses and indexes: `config.servers`, `scores[0]`. A constant is a
  read-only place.
- **A temporary** is any other value. It is passed as owned.
- **An owned value is needed** by a `var`, an `own` parameter, a record field,
  a collection element, and a return value. A place there is written with
  `own`, which moves it, or is copied with `copy()`. A view, a constant, an
  element, or a part of one cannot be moved, so it is copied.
- **There is no mutable global state.** A top-level `let` is a constant, and
  `var` is allowed only inside functions.

### Parameter modes

A parameter is read-only by default. `mut` lets the function mutate the
caller's value, and `own` gives the function ownership of it. The call site
repeats the keyword on a place that it passes to a `mut` or `own`
parameter. A temporary takes no keyword:

| Call | Meaning |
|---|---|
| `sort(mut scores)` | `scores` may be mutated. |
| `push(mut names, item: own name)` | `name` is moved. |
| `push(mut names, item: name.copy())` | `push` gets a copy. |

A mode keyword applies to the longest place expression at the start of its
operand. The first method call or `with` after that place takes it, a
method call as its receiver and `with` as its base, and the rest of the
expression works on the result:

| Expression | Place the keyword applies to |
|---|---|
| `mut config.servers.sort()` | `config.servers` |
| `mut config.load_servers().sort()` | `config`, for `load_servers` |
| `own config with (port: 443)` | `config`, for `with` |
| `sort(mut items[..middle])` | `items[..middle]` |

An expression that does not start with a place takes no mode keyword.

`own` can move one field out of a record. The record's other fields stay
usable, and the whole record is usable once the field is reinitialized. A
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
- It is reinitialized on every path before the function returns or the
  iteration or arm ends. Until then it is not read.

### Copying

- **`Plain` types copy implicitly.** A type made only of fixed-size data with
  nothing on the heap, such as the integers, floats, `Bool`, `Character`,
  and records, sum types, and `Array`s built only from those, is `Plain`.
- **A name bound to a `Plain` value is a copy.** A `let`, or a pattern of a
  `match` or an `is`, that binds a `Plain` value without `mut` copies it, so
  the place it was bound from can be assigned while the name is live. A
  compound assignment's `Plain` operand is a copy too, so an index key of
  the target can assign the operand's place. The variable of a `for` loop is
  not copied: the loop lends its collection for the body.
- **`Copyable` types have `copy()`,** whose result is identical to the
  original. An implicit copy never allocates.
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

A read-only parameter, a `let` bound to a place or to a string literal, the
variable of a `for x in items` loop, and a slice refer to the original value
instead of a copy:

```truss
let middle = items[1..4]
let total = middle.sum()
mut items.push(9)
```

While a view is live, that is, until its last use, its original cannot be
mutated or moved. Here `push` is allowed because `middle` is not used after
it.

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
  everything that its read-only and view arguments view. An argument that
  is `Plain` lends nothing, unless it holds an `Array`: an array is stored
  in place, so a `Slice` of it views the argument.
- **A function stores only the views it is given.** To store a view of an
  argument in a `mut` parameter or in `mut self`, the function takes that
  argument as a `Slice`, a `StringSlice`, or a function. A value cannot
  hold a view of a part of itself.
- A `var` can hold a view that never escapes the function.
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
- **The implicit conversions are between a `List`, an `Array`, or a
  `String` and its view.** One makes a view of a `List` or an `Array` where
  a `Slice` is expected, and of a `String` where a `StringSlice` is. It
  applies to an argument of such a parameter, and to an operand of a
  comparison whose other operand is such a view, so `items == part[1..]`
  compares two slices and allocates nothing. `self` is such a parameter,
  so `StringSlice.trim(name)` takes a `String`.
- **The other passes a view as its owning type to generic code.** A
  read-only parameter whose declared type is a type parameter or an
  associated type takes a `Slice` where the call instantiates that type to
  a `List`, and a `StringSlice` where it instantiates it to `String`. So
  `counts.get(word)` and `counts[word]` look up a `Map[String, Int64]` with
  a `StringSlice`. The call allocates nothing, and a view that the call
  returns views what the argument views. `self` is no such
  parameter, and neither is a parameter declared as `List` or `String`,
  which takes no view. The receiver and the other arguments instantiate the
  type parameter first, in whatever order the arguments are written.

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
  other constants, and records, variants, collection literals, and strings
  built from those. It calls no function except the `from_elements` or
  `from_entries` of a collection literal, and is evaluated when the program
  is compiled.
- A constant's value does not depend on itself, through another constant or
  through the default of a field that a record or variant in it leaves out.
- Reading a constant or taking a view of it allocates nothing.

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
  fills it in.
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
function's name.

- `name[...]` holds type arguments when `name` is a generic function, a
  type, or a trait, and is an index otherwise. After a `.`, it holds type
  arguments when the name is a method of the receiver.
- The written arguments give the generic parameters in brackets, in order.
- A capability parameter takes no type argument, since it is written at its
  uses and not in brackets: `for_each[String](names, visit: greet)` gives
  `Item` alone.

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
                     | UPPER_NAME "." UPPER_NAME
                     | "generic" UPPER_NAME ;
```

```truss
public fn binary_search[Element: Ordered](sorted: Slice[Element], target: Element) -> Option[UInt64]
  requires is_sorted(sorted)
  ensures match result {
    Some(index) => sorted[index] == target
    None => !contains(sorted, target)
  }
  cost time O(log(sorted.length()) * time(Element.compare))
  cost allocations == 0
{
  todo
}
```

| Clause | Meaning | Count |
|---|---|---|
| `uses` | The capabilities the function may use. Without it, the function uses none. | At most one |
| `requires` | A precondition, proven at every call | Any |
| `ensures` | A postcondition, proven for the body | Any |
| `decreases` | A measure that proves recursion ends | At most one |
| `cost` | A proven bound on a resource | Any |

- Repeated clauses all hold. Each `requires` may rely on the `requires`
  before it, and each `ensures` on every `requires` and the `ensures`
  before it.
- A function's *contract* is its `requires`, `ensures`, `decreases`, and
  `cost` clauses.
- No clause is evaluated when the program runs.
- `Self.Uses` and `Source.Uses` name an associated capability set (see
  [Associated capability sets](#associated-capability-sets)).

### Termination

```truss
fn serve(listener: mut Listener)
  uses NetworkServer, Handles, RunForever
{
  while true {
    respond(mut listener.accept())
  }
}
```

- **A function terminates unless its `uses` names `RunForever`.** A loop
  without a measure uses `RunForever` (see [Loops](#loops)), and so does a
  call of a function that uses it. `RunForever` is otherwise a capability
  like any other: a function type without it takes only functions that
  terminate, and a capability parameter holds it where a function passed for
  the parameter may run forever (see
  [Capability parameters](#capability-parameters)).
- `RunForever` has no methods, and nothing implements it, since a `provide`
  of it would let a function that does not declare it run forever. A
  `parallel` branch or a quantifier may run forever where its function may.
- A function that uses `RunForever` has no `time` clause.
- A call of a capability's method terminates unless the method's `uses`
  names `RunForever`. A method that waits for the world, such as
  `Console.read_line`, returns once the world answers, so waiting is not
  running forever. An implementation whose method may run forever declares
  `uses RunForever` on its `impl`, and providing it requires `RunForever`.
- A trait's method runs forever only where its `uses` names `RunForever`, or
  names an associated capability set that an `impl` puts `RunForever` in
  (see [Associated capability sets](#associated-capability-sets)). `any`
  fixes those sets to the empty set, so a method called through `any`
  terminates unless its trait's method names `RunForever`.
- A recursive call on a part of a parameter needs nothing written. A part is
  a field taken out by a pattern, or an element of a collection that is
  itself a part:

  ```truss
  fn depth(tree: Tree) -> UInt64
    cost time O(tree.size())
  {
    match tree {
      Leaf => 0
      Node(left, right, ..) => 1 + depth(left).max(depth(right))
    }
  }
  ```

- Other recursion in a function without `RunForever` states `decreases`: an
  integer measure over the parameters that stays at or above zero and that
  every recursive call makes smaller. A list of measures is compared in
  order. Functions in a cycle of calls each state one.
- A function that uses `RunForever` may state `decreases` as well. Each of
  its recursive calls to a function that states one then makes the measure
  smaller.
- **A recursion is followed through each call to the code that the call
  runs.** The callee decides which code that is:

  | The callee | The code that the call runs |
  |---|---|
  | A function, or a method of a type | That function or method |
  | A trait's method, on a type whose `impl` is known | That `impl`'s method: the method written in the `impl`, the method that the `impl` derives, or the provided method that the `impl` inherits |
  | A trait's method, through `any Trait` | The method of every `impl` of the trait |
  | A trait's method, through a bound on a type parameter | Code that a caller of the enclosing function supplies, as the next rule says |
  | A function value | Code that a caller of the enclosing function supplies, as the next rule says |

  A provided method that an `impl` inherits runs the trait's body for that
  `impl`, so a call on `Self` in the body runs the same `impl`'s method. The
  body is also checked once, for every `impl`. In that check a call on `Self`
  is followed to the method of every `impl` of the trait.
- **Code that supplies other code to a callee is followed to all of the
  supplied code.** The callee is checked for every type argument and every
  function value, so it cannot name the code that it is given:

  | The supplier | The supplied code |
  |---|---|
  | A call that gives a type argument to a type parameter with a bound. The parameter is one of a generic function, of a generic `impl`, of a generic type with a derived `impl`, or of a trait's generic method | Every method of the type argument's `impl` of the bound |
  | A function named as a value | The function, and the code that its type arguments supply |
  | A conversion to `any Trait` | Every method of the value's `impl` of the trait |
  | A `provide` | Every method of the provided `impl` |

- **A recursion that leads back to a function without `RunForever` is proven
  to terminate, or is rejected.** The way back decides:

  | The way back to the function | The requirement |
  |---|---|
  | A call of a function, of a method written in an `impl`, or of a trait's method through `any Trait` or on `Self` | The call is on a part of a parameter, or each function in the cycle states `decreases` |
  | A call of a method that its `impl` derives or inherits | Rejected. The `impl` states no measure for that code, so nothing proves that the recursion through it terminates |
  | Supplied code | Rejected. A use of supplied code passes no arguments to compare with a measure |

  A function that uses `RunForever` is not rejected for any of these. Its
  recursive call is compared only where it and its callee both state
  `decreases`.

  With `type Tree(children: List[Tree])`, an `equal` of `Tree` written as
  `self.children == other.children` supplies the `impl` of `Equal` for `Tree`
  to the list's `equal`, which calls it back, and is rejected. A loop over
  the children that calls `equal` on each child recurses on a part.

### Cost clauses

```ebnf
cost        = [ "amortized" ] resource bound ;
resource    = "time" | "allocations" | "allocated_bytes"
            | "calls" "(" call_target ")" ;
call_target = LOWER_NAME | path_type [ "." LOWER_NAME ] ;
bound       = "O" "(" expression ")" | ( "<=" | "==" ) expression ;
```

```truss
public fn load_configs(paths: List[Path]) -> Result[List[Config], ConfigError]
  uses FileRead
  cost calls(FileRead.read) == paths.length()
  cost time O(paths.length())
```

- The target of `calls` is a function parameter, a capability method, or a
  whole capability, never an associated capability set.
- `O(f)` means that the cost is at most `c * f + d` for every input, for
  some constants `c` and `d`.
- `time` counts abstract steps: each primitive operation and each call is one.
- A caller's cost is proven from its callees' cost clauses.

A bound is an expression on exact integers. It can use the parameters,
`self`, their fields, pure methods, `result`, `+`, `*`, and `/` and `-`
where the result stays at or above zero, and:

| Term | Value |
|---|---|
| `log(n)` | The smallest integer at least log₂(n + 1) |
| `power(base, exponent)` | `base` to the `exponent` |
| `time(visit)`, `allocations(visit)`, `allocated_bytes(visit)` | A bound on that resource of any one call of the function parameter `visit` |
| `time(Element.equal)`, `allocations(Element.equal)`, `allocated_bytes(Element.equal)` | A bound on that resource of any one call of a method of a trait that bounds a type parameter, `Self` in a trait, or an associated type of either, as in `time(Source.Element.equal)` |

The terms of the last two rows are the costs of a callee. A cost of a callee
is one number for the function: it cannot depend on the arguments of a call.

| A cost of a callee is written | Rule |
|---|---|
| In an `O(...)` or a `<=` bound of a clause on its own resource | Allowed |
| In an `==` bound | Rejected. The term is an upper bound and a call may spend less, so an exact amount that names it would be false for that call. |
| In a clause on another resource | Rejected. `time(visit)` bounds only `time`, `allocations(visit)` only `allocations`, and `allocated_bytes(visit)` only `allocated_bytes`. |
| With an operand that is neither a function parameter nor a method of a bound | Rejected |

- `time(visit)` is a constant for a parameter of type
  `(fn(Item) cost time O(1))`, and a fixed bound that is not known for any
  other function that terminates. It has no value for a function that may
  run forever, and a bound that names it is then unbounded. So a bound
  names `time(visit)` only where the type of `visit` does not name
  `RunForever`.
- `allocations(visit)` is `n` for a parameter whose type states
  `cost allocations <= n` or `== n`, and a fixed bound that is not known for
  any other function whose allocations are bounded. It has no value for a
  function whose allocations have no bound, and a bound that names it is
  then unbounded. `allocated_bytes(visit)` is the same for
  `cost allocated_bytes`. A bound names either term for any function
  parameter.
- An operator counts as the method it calls: `==` spends
  `time(Element.equal)` and `allocations(Element.equal)`, and `<` spends
  `time(Element.compare)`. If a name has several overloads, the term means
  the read-only one.
- At a call, the cost of a callback has the value that the function passed
  gives it:

  | The function passed | The value of the term |
  |---|---|
  | A lambda | A bound on its body for every argument |
  | A named function | For `time`, a constant where its clause is `O(n)` for a literal `n`. For `allocations` and `allocated_bytes`, `n` where its clause is `<= n` or `== n` for a literal `n`. |
  | A parameter of the caller | The caller's own term for that parameter |

  A function that states no bound on the resource has no value for the
  term, and neither has one whose bound is `amortized`, which bounds a call
  together with the potential it changes. A bound that names the term is
  then unbounded, so the caller proves no bound on that resource through the
  call.
- At a call, the cost of a bound's method has the value the type argument
  gives it: `time(Element.equal)` is a constant for `Int64`, whose
  `impl Equal` promises `cost time O(1)`, and `allocations(Element.equal)`
  is 0, since that `impl` promises `cost allocations == 0`. `time(...)` has
  no value for a type argument whose `impl` of the method may run forever
  (see [Termination](#termination)), and `allocations(...)` and
  `allocated_bytes(...)` have none where the `impl` states no bound on that
  resource. A bound that names the term is then unbounded.
- A function with an `==` bound on a resource calls a callback only where
  the cost of the call is exact: the callback's type states an `==` bound on
  that resource, or the callback's bound is zero. The cost of any other call
  is only bounded above.

```truss
fn Slice[Element: Equal].contains(self, item: Element) -> Bool
  cost time O(self.length() * time(Element.equal))
  cost allocations <= self.length() * allocations(Element.equal)

fn Option[Value].map[Output](
  own self,
  transform: (fn(own Value) -> Output uses generic Granted),
) -> Option[Output]
  uses generic Granted
  cost time O(time(transform))
  cost allocations <= allocations(transform)

fn halved(value: Option[Int64]) -> Option[Int64]
  cost allocations <= 0
{
  value.map(fn(inner) { inner / 2 })
}
```

#### Amortized costs

```truss
public opaque type List[Element](buffer: Buffer[Element], length: UInt64, capacity: UInt64)
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
  in the potential of the values the function mutates or returns, is within
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
fn serve(handle: (fn(Request) -> Response uses Database, Log))
```

- A function type without `uses` uses no capability. Its `uses` and `cost`
  clauses cannot mention its inputs.
- **A function type takes only functions whose capabilities its `uses`
  names,** so one without `RunForever` takes only functions that terminate
  (see [Termination](#termination)).
- Clauses after a definition's result type belong to the definition.
- A function type names its inputs exactly when it has a `requires`. Only
  the type of a definition's parameter may have one, at the top level of
  that type. The `requires` can mention the inputs and the parameters before
  that parameter. The definition proves the `requires` at every call through
  the parameter. A lambda passed for the parameter may rely on the
  `requires`, and a named function passed for the parameter accepts every
  argument that the `requires` allows:

  ```truss
  fn List[Element].generate(
    count: UInt64,
    make: (fn(index: UInt64) -> Element requires index < count),
  ) -> List[Element]
    ensures result.length() == count

  let reversed = List.generate(values.length(), make: fn(index) { values[values.length() - 1 - index] })
  ```

- A function-typed parameter can be called but not stored. One declared
  `own` can be stored, and accepts only functions that capture no local
  variables.

### Capability parameters

```truss
public fn for_each[Item](
  items: List[Item],
  visit: (fn(Item) uses generic Granted),
)
  uses generic Granted
  cost calls(visit) == items.length()
  cost time O(items.length() * time(visit))
```

A capability parameter passes on the capabilities a callback uses,
`RunForever` among them.

- `generic Granted` names a capability parameter of the enclosing function,
  method, or theorem, and is written at each use. Every `generic Granted` in
  one signature names the same parameter, including one inside the type of
  a parameter's parameter. Nothing else declares it.
- A capability parameter is named only in `uses`, in the signature of a
  function, a method, or a theorem, and in its body. A body names only the
  capability parameters of its signature, and a type, a constant, an `impl`,
  and a test name none.
- A capability parameter named in the function's own `uses` is also named in
  the type of a parameter or the result. Otherwise no argument gives it
  capabilities, and the name is a misspelling.
- A call infers `Granted` from the functions it passes, and writes no type
  argument for it (see [Explicit type arguments](#explicit-type-arguments)).
  Where the function passed may run forever, `Granted` holds `RunForever`,
  and so does the call.
- A function declares `uses generic Granted` only where it calls a function
  that uses it. One that returns or stores such a function does not, and its
  caller needs the capabilities only where it calls the result:

  ```truss
  fn later(run: (fn() uses generic Granted)) -> (fn() uses generic Granted) {
    run
  }
  ```

- `for_each` terminates where the functions passed for `generic Granted` do.
  In its body, a lambda that calls `visit` and also runs forever has the type
  `(fn() uses generic Granted, RunForever)`, and only a function that uses
  `RunForever` itself calls it.
- An `impl`'s method names its capability parameters as its trait's method
  does. Capability parameters have no order to rename them by.
- `O(items.length() * time(visit))` is unbounded where `visit` may run
  forever, so the bound holds for every `Granted`. A bound that does not name
  `time(visit)` is proven only where the type of `visit` bounds its time.
- A type that holds a function writes the capabilities in the field's type.

## Methods

```truss
fn List[Element].with_capacity(capacity: UInt64) -> List[Element]

fn List[Element].push(mut self, item: own Element)

fn Slice[Element: Ordered].sort(mut self)
  cost time O(self.length() * log(self.length()) * time(Element.compare))

fn Slice[Element].zip[Other](self, other: Slice[Other]) -> Zipped[Element, Other]
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

### Overloads by receiver mode

```truss
fn Slice[Element: Copyable].filter(self, keep: fn(Element) -> Bool) -> List[Element]
fn List[Element].filter(own self, keep: fn(Element) -> Bool) -> List[Element]
```

A method can have up to three overloads that differ only in the mode of
`self`. The mode keyword at the call site selects the overload, no keyword
selects the read-only one, and a temporary receiver takes the `own` overload
if there is one. An overload may come from a trait that the type implements
in its own package, or from the type's view (see
[Method lookup](#method-lookup)): a `List` has both overloads of `filter`
above. Truss has no other overloading.

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
  access, written on the place: `mut part`.
- **The method lends the value of its body, or of a `return`.** No code of
  the method runs after it lends. The values it still owns are dropped where
  it lends, before the caller uses the part.
- **The part is lent for the rest of the caller's statement,** even if the
  statement exits early.
- **In the condition of an `if` or a `while`, the part is lent for the
  condition alone** when each name the condition binds is a copy: a `Plain`
  name that is not a view and is not bound `mut`. The guarded block can then
  mutate the receiver, as in
  `if counts.get(word) is Some(count) { counts[word] = count + 1 }`. A name
  that is not a copy aliases the part, which stays lent until the then-block
  or the body ends. It is never lent into the `else` block.
- **For that long, the receiver is lent whole:** the statement makes no other
  use of a receiver lent `mut`, and does not mutate one lent read-only. A
  receiver that is a view lends its original too, so `names[..].first()`
  lends `names`. Two indexes or slices of one `List`, `Slice`, or `Array` can
  be lent together when the prover shows that they do not overlap.
- The `mut` on the receiver selects the overload that lends `mut`, and the
  part is then mutated with no keyword of its own.
- **A lent part is not the caller's to keep.** It is not moved, returned,
  stored, or bound with `let`, except by copying it.
- **A lending method is not a value.** A function type has a result and
  never lends, so its caller could keep the part past the statement, a
  dangling view.
- The part need not be stored in `self`: the method may lend a value it
  made, which is dropped when the lend ends.
- **A method lends a part of its first parameter, or a whole value that it
  made.** A caller keeps only the first argument lent, so it could mutate or
  drop another argument while a part of it is lent, a use after free. The
  method does not lend a part inside a value it owns either, such as an
  element of a list it built: the method drops the value where it returns,
  and the part would dangle. A part whose type is `Plain` is lent as a copy,
  so it can come from anywhere. A part that is a view may view any
  parameter, as a returned view may.

The lent value may be a constructor applied to places:

```truss
fn Slice[Element].get(self, index: UInt64) lends Option[Element] {
  if index < self.length() {
    Some(self[index])
  } else {
    None
  }
}
```

- An argument of the lent constructor that is a place is lent, with no copy.
  Constructors nest.
- Any other argument is a value that the method made. The lent value owns
  it, and it is dropped when the lend ends.
- A `mut` lend writes `mut` on each place that it lends `mut`, and the
  caller's mutations of such a field reach the place when the lend ends.
  Two places lent `mut` by one method are different places.
- **A place lent `mut` is never inside a variant,** at any depth: the caller
  could replace the variant, and the place would have no value, a use after
  free.
- The built value owns the values that the method made, and nothing that it
  was lent.

#### Contracts of lending methods

```truss
fn List[Element].element(mut self, position: UInt64) lends mut Element
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
type Countdown(left: UInt64)

impl Cursor for Countdown {
  type Element = UInt64

  fn next(mut self) -> Option[UInt64] {
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
- `Uses` is the set of capabilities that `next` uses. Each `next` uses the
  implementations provided where it is called.

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
- **A comparison of a place with itself is an error,** as in `x != x` or
  `items[i] < items[i]`, since the laws of `Equal` and `Ordered` decide its
  result. A specification is exempt.
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
                | UPPER_NAME [ pattern_fields ]
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
  changes the semantics of a pattern. A constant in a pattern has a type with
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
- A `match` on several values has one pattern per value in each arm.
  Coverage and reachability are checked across all the values.

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
- The base is passed as an `own` argument is: a base that is a place takes
  `own`, unless it copies implicitly.
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
- A lambda captures local variables by view and cannot mutate them. A
  lambda that captures a variable is a view; one that captures none can be
  returned, stored, and moved.
- A lambda's capabilities are inferred from its body, `RunForever` among
  them: a lambda uses it when its body holds a loop without a measure or
  calls a function that uses it.
- `return` and `?` exit the lambda. `break` and `continue` do not reach a
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
| `for score in mut scores { ... }` | Mutate elements in place. |
| `for item in own items { ... }` | Move each element out. |
| `while low < high { ... }` | Loop while a condition holds. |

- **A `for` loop over a collection visits its elements by position.**
  `for item in items` evaluates `items.count()` once, and each iteration is
  lent `items.element(position)`, for each position from zero up to the
  count. A type supports `for` by defining `count(self) -> UInt64` and
  `element(self, position: UInt64)`, a lending method, as its own methods or
  by implementing `Iterable`.
- `for item in mut items` is lent each element by the overload of `element`
  that takes `mut self`. A `mut` loop mutates elements but does not add or
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
  exits, has type `Never`.
- `invariant` holds at the start of every iteration and when the loop ends.
- `decreases` names a measure that every iteration makes smaller and that
  never goes below zero. It holds in every function, including one that
  uses `RunForever`.
- Where a `for` loop over a cursor states no measure, and the cursor's type
  has a `remaining(self) -> UInt64` method, that method's value is the
  loop's measure, and it holds as a written one does.
- In a function without `RunForever`, a `while` loop that states no measure,
  and whose condition compares two sides that mutate nothing with `<`, `<=`,
  `>`, or `>=`, has the distance between them as its measure.
- **A loop without a measure uses `RunForever`** (see
  [Termination](#termination)). A `for` loop over a range or over a
  collection's elements always terminates.
- In the clauses of a loop over a range, the loop variable is the index of
  the next iteration: in `for i in start..end`, `i` is `start` on entry and
  `end` where the loop ends, and `end + 1` after `start..=end`.
- In the clauses of any other `for` loop, `visited` is the `Sequence` of the
  values of the iterations before. The clauses cannot name the element. A
  local named `visited` shadows the word.
- In a loop that reads a collection, `visited[i]` is the value of the
  collection's `element` at position `i`, so it meets that method's
  `ensures`.
- Where a cursor's `model()` is a `Sequence` of the cursor's `Element`, as a
  `ListCursor`'s is, the model is the values that the cursor has yet to
  give, in order. In a loop that pulls such a cursor, `visited` followed by
  the cursor's model is the cursor's model on entry to the loop, so
  `visited` is that model once the cursor has no more values. A loop that
  moves the elements out of a `List` or an `Array` therefore visits the
  elements of the collection's model in order. A loop whose clauses name
  `visited` proves, of such a cursor, that `next` returns the first value of
  the model and leaves the rest as the model, and that it returns `None`
  only when the model is empty.
- A loop's `cost` bounds the loop's cost so far at the start of every
  iteration and where the loop ends, each time before a `while` loop
  evaluates its condition or a `for` loop over a cursor calls `next`. It
  also holds where a `break` leaves the loop, with the iteration that the
  `break` leaves counted as visited: a range's index is the index after it,
  and `visited` holds its value. The clause is never `amortized`. Its bound
  can use the variables in scope at the loop, and
  `visited` or a range's index:

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

- **A loop's `cost` does not count the evaluation that ends the loop.** That
  evaluation comes after the last point where the clause holds, and its cost
  is added to the clause's bound to give the cost after the loop:

  | Loop | Evaluated once more than the body runs |
  |---|---|
  | `while` | The condition, as far as `&&` and `\|\|` evaluate it |
  | `for` over a cursor | `next`, which returns `None` |
  | `for` over a range or over a collection's elements | Nothing: `count` is called once, before the loop |

  ```truss
  fn count_heads(limit: UInt32) -> UInt32
    uses Random
    cost calls(Random.next) == result + 1
  {
    var heads: UInt32 = 0
    while Random.next() % 2 == 0 && heads < limit
      invariant heads <= limit
      decreases limit - heads
      cost calls(Random.next) == heads
    {
      heads = heads + 1
    }
    heads
  }
  ```

### Ranges

- `start..end` excludes `end`, and `start..=end` includes it. `start..end` is
  empty when `start` is at or past `end`, and `start..=end` when `start` is
  past `end`.
- Two ranges of a `Countable` type, such as an integer type, `Character`, or
  `Date`, are equal when they hold the same values: `0..3 == 0..=2`, and
  every empty range equals every other.
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
| `[2, 3, 5, 7]` | A `List`, or where one is expected an `Array`, a `Sequence`, a `FiniteSet`, or a type that implements `FromElements` |
| `[]` | An empty one of the same |
| `["http": 80, "https": 443]` | A `Map`, or where one is expected a `FiniteMap` or a type that implements `FromEntries` |
| `[:]` | An empty one of the same |

```truss
impl FromElements for Stack[Element] {
  type Element = Element

  fn from_elements(elements: own List[Element]) -> Stack[Element] {
    Stack(items: own elements)
  }
}

let pending: Stack[Int64] = [1, 2, 3]
```

- An `Array` literal has exactly as many elements as its type says.
- A non-empty list literal in a function body counts as one allocation, and
  an empty one as none.
- A type takes a list literal by implementing the prelude trait
  `FromElements`, and a map literal by implementing the prelude trait
  `FromEntries`. The literal's elements have the type's `Element`, and a map
  literal's keys and values its `Key` and its `Value`.
- Such a literal is a call of `from_elements` with the `List` of its
  elements, or of `from_entries` with a `List` of one `map::Entry` for each
  key and value, in the order written. It costs that list and that call.
- `from_entries` requires keys that are pairwise distinct by `==`, so a map
  literal's keys are proven distinct.
- A list literal may repeat an element, and `from_elements` decides which of
  two equal elements a collection keeps.

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
- A type whose elements are mutated in place also implements `IndexMut`, whose
  `at(mut self, key)` lends an element `mut`. `items[i].name = text`,
  `items[i] += 1`, and `mut items[i]` need it.
- `collection[key] = value` calls `assign` when the type implements
  `IndexAssign`. The collection must accept the key, by its `accepts_key`:
  a `Map` accepts every key and inserts a missing one. For any other type,
  the assignment replaces the element that `IndexMut` lends, so the key is
  there.
- Each method of the three traits terminates: none uses `RunForever`.
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
brackets   = bracket_item { "," bracket_item } [ "," ]
           | [ additive ] ".." [ additive ]
           | [ additive ] "..=" additive ;
bracket_item = expression | UPPER_NAME "=" type ;

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
  left operand of `is`. Each of those needs parentheses.
- `return` and `echo` take everything after them. A `{` right after
  `return`, on the same line, starts the returned value.
- The brackets after a name in an expression hold expressions, which cover
  type names and their arguments but not function types.

### Operators

`==` and `!=` call the `Equal` trait, and `<`, `<=`, `>`, and `>=` call
`Ordered`. Both sides have the same type, or one side is a view that the
other converts to (see [Views](#views)). Functions and `any` values cannot
be compared. `!` works on `Bool`, `~` on integers, and negation on
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

  fn add(self, right: Right) -> Self.Output
    requires self.add_is_defined(right)
}
```

- Each operation terminates, and requires its `_is_defined` method. For a
  fixed-width integer, an operation is defined where its result fits the
  type and, for `/` and `%`, where the divisor is not 0 and the operation is
  not `minimum / -1`. A float operation is defined everywhere.
- The built-in number types implement these traits only with themselves on
  both sides. The bitwise operators and shifts work only on the built-in
  integer types.

#### Compound assignment

- `a += b` and the other compound assignments are statements whose left side
  is a place. `a += b` means `a = a + b` with the place evaluated and
  checked once.
- The old value of `a` is passed to the operator as owned, so an overload
  of the trait's method that takes `own self` can update in place.

#### Evaluation order

- Operands, arguments, and fields are evaluated in the order written.
- `target = value` evaluates `value`, then the index keys of `target`, and
  then stores.
- `target += operand` evaluates `operand`, then the index keys of `target`,
  once, then takes the old value of `target` and stores the result. A `?`
  that returns from `operand` leaves `target` unchanged.
- `&&`, `||`, and `==>` evaluate their right side only when the left does
  not decide the result.

### Integers

- **No integer operation overflows silently.** An operation that could
  overflow is proven not to, or the code calls the standard library's
  checked, wrapping, or saturating method.
- `/` rounds toward zero, and `%` has the sign of its left operand.
- `>>` on a signed integer copies the sign bit, and on an unsigned integer
  shifts in zeros. A shift amount is any unsigned integer type, proven
  smaller than the bit width of the value.
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

Code panics only where it calls `Panic.crash`, directly or through a
callee such as `expect`, so only code that has `Panic` panics. Running out
of memory and overflowing the stack are the exceptions.

Every operation that can fail is a proof obligation, in every function and
every test: integer overflow, division by zero, indexing or slicing out of
bounds, a shift that is too large, and `unreachable`. Where the compiler
cannot prove one safe, the code is an error, and one of these makes it
compile:

1. Establish the fact locally, as with an `if`.
2. Require it with `requires`.
3. Call a method that returns an `Option` or a `Result`, such as
   `checked_add` or `get`.

`unreachable` admits only the first. Code that crashes when the operation
would fail calls the third kind of method and `expect` on its result, as in
`left.checked_add(right).expect("the total fits Int64")`, and declares
`uses Panic`.

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
  `mut self` where they mutate its state, and then the capability's
  parameters without their defaults: the capability's method fills a
  default in before the call reaches an implementation.
- `provide implementation, ... { body }` runs the body with the given
  implementations, passed as arguments are: a place is written with `mut`
  when its methods mutate it, and it holds the mutations afterward.
- Providing a type provides every capability it implements.
- An `impl` with a `uses` clause can use those capabilities, and providing
  it requires them. Otherwise an `impl`'s methods use only the capabilities
  their trait or capability declares.
- **Inside an implementation, a call of the capability it implements goes to
  the next provider out.** So an implementation can check each call and pass
  it on, which narrows the capability.
- **A capability method returns to its caller once,** unless its result
  type is `Never`, as for `Panic.crash`.
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
| `RunForever` | Running a loop or a recursion that no measure bounds (see [Termination](#termination)) |

The runtime holds a *real implementation* of every standard capability.
Those of `Panic` and `RunForever` are built in, and no `impl` implements
either. A capability that a package declares has no real implementation.

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

`main` has this signature. Its `uses` clause names only capabilities with
a real implementation, and the runtime provides those real implementations
and nothing else. The program ends when `main` returns or panics.

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
  one branch mutates is used by no other branch.
- A branch uses no capability except `Panic` and `RunForever`, and uses
  each only where the enclosing function has it, so a function that
  contains `parallel` is still pure.
- A branch cannot exit the block with `return`, `break`, `continue`, or `?`.
- A `parallel` block has the result of running its branches in order, and
  its `time` is the sum of theirs.
- `parallel for` runs a loop's iterations at the same time, by the same
  rules. Its body mutates only its own element and its own variables, and
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
  the capabilities of the code around them and may exit the block.
- **A branch that exits the block with `?`, `return`, or `break` cancels the
  other branches,** waits for them to end, and then exits. A branch that has
  not started does not start, and the first branch to exit decides where
  control goes.
- The code after the block does not run when a branch exits early, so a
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
  next pull could mutate or drop the value that a view from the cursor
  views, which would leave the task with a dangling view.

### Shared state

When the code inside a `provide mut` can use `Tasks`, as known from the
signatures it calls, including through a capability parameter, the
implementation's calls are mutually exclusive: each holds the
implementation's mutex from start to end. Such an implementation has no
method with a parameter that can hold a function, or an `any` value, that
uses a capability other than `Panic` and `RunForever`, so its mutexes
cannot deadlock. An implementation provided without `mut` has no mutex.

## Strings

- A string literal is a `String` constant without a name. Reading it, taking
  a view of it, and binding it with `let` cost nothing. Where an owned
  `String` is needed, as in a `var`, an `own` argument, or a returned value,
  the literal is copied, and a copy of a non-empty literal counts as one
  allocation.
- A string literal without `${...}` where a `StringSlice` is expected is a
  `StringSlice` of the constant's bytes.
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
- A tag's `from_template` states the rules for valid literal text with
  `requires`. The literal text is known when the code is compiled, so the
  `requires` is evaluated then. `Regex"[a-z"` is an error, and so is a check
  that panics or reaches `todo`.
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
  its `requires`.
- A trait's contracts bind every `impl` and are proven for each.
- **An `impl`'s method has its trait's signature.** It restates that
  signature: the generic parameters with their bounds; the parameters with
  their names, modes, and types, and a default exactly where the trait's
  parameter has one; and the result. `Self`, the trait's arguments, and the
  associated types are as the `impl` gives them, and a function type has the
  trait's `uses` and `cost` clauses. The method's generic parameters may
  have other names, its capability parameters have the trait's names (see
  [Capability parameters](#capability-parameters)), and a type parameter's
  bounds and a function type's `cost` clauses may come in another order.
  The body of the method and every call of it are checked against this one
  signature. The method states of its own only its `uses`, which stays
  within the trait's, the values of its defaults, and the contract clauses
  that the next two rules allow.
- **An `impl`'s method may promise more than its trait.** Its contract is
  the trait method's, with the method's own `ensures` and `cost` clauses
  added, and its own `requires`, if it has any, in place of the trait's.
  The trait's `requires` must imply the method's. A call known to reach
  that `impl` is proven against the `impl`'s contract, and a call through a
  bound or `any` against the trait's.
- An `impl`'s method without a `time` clause has its trait's.
- **Required traits:** a type implements the traits a trait requires before
  it implements the trait, and a bound includes them. A trait cannot
  redeclare a method of a trait it requires, but can add an overload in
  another mode. Traits cannot require each other in a cycle.
- **A method with a body** is provided to every implementation. An `impl` can
  override it with a method that keeps the trait's contract for it, as it
  keeps the contract of every other method.

### Implementations

- A type has at most one `impl` of each trait for each set of the trait's
  type arguments, whatever the type's own arguments, and every `impl` is
  written out for its type.
- An `impl` for a generic type states its conditions on the type's
  parameters, as in `impl Display for List[Element: Display]`.
- An `impl` lives in the package of the trait, of the implementing type, or
  of the outermost type of one of the trait's arguments.
- The trait's arguments in an `impl` or a law proof hold no function type
  and no associated type, such as `Items.Element` or `Self.Output`. An
  associated type may stand for any type, so an `impl` with one would overlap
  every other `impl` of the trait for its type.
- The trait of an `impl` or a law proof takes no constraint, such as
  `Element = Int64`. An `impl` chooses its associated types in its body, so a
  constraint on its trait could only repeat or contradict that choice.
- An `impl` applies wherever its trait and the types it names are visible.
- With a trait that takes type parameters, the `impl` is chosen by the types
  of the arguments, inferred first without looking at which `impl`s exist,
  and never by the expected result type.
- A call's arguments give the trait's arguments, and so does a type
  parameter's one bound of the trait, which its signature states. The
  `impl`s of a type never do: where `Pair` implements only `Bag[Int64]`,
  `pair.count()` is an error, and is written `Bag[Int64].count(pair)`. A loop
  over a `Pair` whose elements come from the methods of `Bag` is an error for
  the same reason.

### Associated types

```truss
trait Index {
  type Key
  type Output
  fn contains_key(self, key: Self.Key) -> Bool
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

fn count[Source: Cursor](source: own Source) -> UInt64
  uses Source.Uses
```

- `capability Uses` in a trait declares a set of capabilities that each
  `impl` defines, as a list of capabilities and the sets of its type's
  parameters. An `impl` that leaves it out has the empty set, and its
  methods use only the set's capabilities.
- `Self.Uses` and `Source.Uses` name the set in a `uses` clause. A call needs
  the set's capabilities for its type arguments. A function generic over a
  `Cursor` that advances it declares `uses Source.Uses`.
- A bound cannot constrain a set, and `calls(...)` cannot count one.

### Equality

A type's equality is *structural* when two equal values cannot be distinguished
by any function, so `a == b` implies `f(a) == f(b)`. The
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
| `Default` | For a record, each field's written default, or its type's `default()` for a field without one. The value must meet the type's invariant |
| `serialization::Serialize` | A record as its fields by name, in declaration order. A variant with no fields as its name, and a variant with fields as a record of them under its name |
| `serialization::Deserialize` | The same form, read back. A missing field takes its default if it has one, and a missing field of type `Option` is `None`. A value that breaks an `invariant` clause of its type is an error |
| `Copyable`, `Plain` | Nothing: an opaque type declares that it copies (see [Copying](#copying)) |

- Every field has the trait, and a derived trait's required traits are
  derived too: `Ordered` and `Hash` need a derived `Equal`.
- A generic type has a derived trait only where its parameters do.
- A derived implementation satisfies the trait's laws; a hand-written one
  proves them.
- `serialization::Deserialize` is derived only for a type whose `invariant`
  clauses can be evaluated at run time: none quantifies over a type, names
  `identical`, holds a value of a type that exists only in specifications,
  or calls a function for specifications only. Data then cannot make a value
  that breaks its type's invariant, which every proof assumes.
- Every type has debug output, which needs no derive.

### Method lookup

- A call with a dot finds the type's own methods, and the methods of the
  traits it implements from the standard library, the calling package, and
  the packages the calling package's manifest lists. No trait is imported.
- A call finds only the methods and traits that its module can see
  ([Visibility](#visibility)). A method it cannot see is not a candidate, so
  a trait's method or the view's method of that name and mode is found
  instead.
- A `String` has the methods of `StringSlice` too, and a `List` and an
  `Array` those of `Slice`, in each mode of `self` that its own methods and
  its traits' methods do not take. The receiver becomes a view of itself, so
  `name.trim()` and `String.trim(name)` are `StringSlice.trim(name)`. A
  method as a value is named through the view: `StringSlice.trim`. In the
  rules below, the methods a type has from its view count as its own.
- Two of those traits giving one name is an error at a call with a dot,
  which is then written in full: `Ordered.compare(first, second)`. A trait
  and a trait it requires are the exception.
- No module can see both a type's own method and a trait method it
  implements with the same name and mode. An `impl` in the type's own
  package may add another overload of a name the type has, by writing the
  method. A provided method that an `impl` does not override, and every
  method of an `impl` in another package, takes no name that the type's
  methods have. These rules count the methods that the `impl`'s package can
  see: every method of the type for an `impl` in its own package, and the
  public ones for an `impl` in another package.

### Dynamic dispatch

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
  generic or capability parameters, and does not take or return `Self`.
- An `any` value cannot be converted back to its type.

## Tests

```ebnf
test = "test" plain_string [ "uses" capability_list ] block ;
```

```truss
test "config loads with defaults" uses RunForever {
  let disk = files::MemoryFiles.new().with_text(Path.new("app.toml"), contents: "")
  let config = provide disk, log::DiscardLog() {
    load_config(Path.new("app.toml"))
  }
  assert config == Ok(Config.default())
}
```

- `plain_string` is a `STRING` with no interpolation.
- A test declares the capabilities its code uses with `uses`, as a
  function does, or provides them. A test whose `uses` names a capability
  other than `Panic` or `RunForever` is *external*: it gets the real
  implementations of exactly those capabilities. Any other test is
  deterministic.
- A test's `uses` names only capabilities with a [real
  implementation](#standard-capabilities).
- A test's standard input is empty.
- A failed `assert` ends the test as failed, and the rest of the test can
  rely on the asserted fact.
- A test build checks every primitive operation that could fail when it
  runs, and a failed check fails the test. A `requires` is not run.
- A panic fails only its test. A test that reaches a `todo` is incomplete.
- A test that runs past the project's time limit fails.

## Proofs

```ebnf
theorem   = "theorem" LOWER_NAME [ generics ] parameters { clause } block ;
law_proof = "proof" path_type "." LOWER_NAME "for" type_head block ;
```

Every promise is proven before a program is built: contracts, invariants,
laws, loop invariants, and every operation that could fail.
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
- **A theorem is called only in specifications and proofs, and is not a
  value.** Its body is a proof and never runs.
- A `proof { }` block in a function body holds the statements that a
  theorem's body holds, and does not run.
- A law proof's body is checked as the law's body is: it names the law's
  read-only parameters, `Self` is its type, and the law's `requires` hold. A
  proof for a generic `impl` names the type as the `impl` does, and is
  proven once for every type.
- A law proof's generic parameters have only the bounds that its `impl`
  declares. A further bound would let the law be taken as proven for
  instantiations that the proof does not cover.

### Bodies and contracts in proofs

- Every callee is known to its callers' proofs by its contract, in every
  package: a function, a method of a type, a trait's method, and an
  `impl`'s method alike.
- An `impl`'s laws are proven from the contracts of its methods.
- A derived `Ordered` states its comparison in its `ensures`.
- A clause applies only where every name that it mentions is visible.
- A function with a `requires` is defined only where it holds.

### Writing specifications

A *specification* is a `requires`, `ensures`, `decreases`, or `cost` clause,
an invariant, a law, or a proof.

- A call in a specification uses no capability, so it terminates. A
  capability parameter in the callee's `uses` stands for nothing at that
  call: `values.map(fn(value) { value + 1 })` is
  such a call, although `map` passes a capability parameter on.
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
- A quantifier over a collection ranges over the values that the
  collection's `element` lends at the positions below its `count()`, in code
  and in specifications alike. A pattern that does not match a value leaves
  that value out.
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
  specifications, never compiled, and its body and defaults are
  specifications.
- A constant whose type mentions a type that exists only in specifications
  is for specifications only.
- **Code that is compiled holds no value of a type that exists only in
  specifications,** nor of a type that holds one, such as `List[Integer]`:
  the type has no representation when the code runs.
- A field never has a type that exists only in specifications, because a
  value that code holds stores its fields.
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
  definition.
- Code with a `todo` is type-checked and proven, and callers are checked
  against the signature of an unfinished function.
- A release build refuses a program whose `main` can reach a `todo`. In a
  development build, a `todo` that runs stops the program and reports its
  position.
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
- Outside a test, the output goes to standard error.
- It is not allowed in proofs. A release build refuses a program whose
  `main` can reach an `echo`, and a package that contains one cannot be
  published.

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
  file begins with its last name.

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
- The modules of a package may use each other in a cycle.

### The prelude

The prelude is in scope in every file, and all its names are
`UpperCamelCase`:

- the built-in types, `Option` and `Result`, and `List`, `Slice`, `Map`, and
  `Set`
- the core traits, such as `Equal`, `Ordered`, `From`, `TryFrom`, `Default`,
  `Copyable`, `Plain`, `Storable`, `Index`, `IndexMut`, `IndexAssign`,
  `Iterable`, `Cursor`, `FromTemplate`, `FromElements`, `FromEntries`,
  `Model`, and the arithmetic traits
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

- An `impl`, a test, and a law proof take no visibility. An `impl` is as
  visible as the least visible of its trait and the types it names, since
  it applies only where all of them are visible. A law proof is as visible
  as the `impl` whose law it proves.
- A method or constant written in a trait, a capability, or an `impl` takes
  no visibility, and is as visible as the definition it is written in.
- A method or member constant defined on its own, such as `fn Shape.area`,
  has its own visibility. A use that reaches a member through its type
  finds it only where it is visible: `Shape.unit`, `shape.area()`, a
  constant in a pattern, and the `count`, `element`, and `cursor` of a `for`
  loop or a quantifier. A member that the use cannot see is skipped, as if
  it did not exist. A use that finds no member except one it cannot see is
  an error that names that member.
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
- A private or `internal` function, method, or constant that no definition
  of its package uses is an error. A method or constant written in a trait,
  a capability, or an impl is not checked. A use counts when the user is
  public, is a test, an `impl`, or another definition the rule does not
  check, or is itself used, so definitions that use only each other are an
  error together. The `main` of a package's root module is exempt, and so
  is a definition the compiler calls, such as the static `new` of a
  `system` module's type, which builds the implementation of a capability.

## No foreign code

Truss code cannot call code written in other languages. Only the standard
library reaches the operating system.
