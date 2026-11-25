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

These characters are an error anywhere in a file, including inside string
literals:

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
`NEWLINE` only as [Line breaks](#line-breaks) says.

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
assert break capability concurrent continue cost decreases derives echo else
ensures exists false fn for forall if impl in indirect internal invariant is law
lends let match modifies mut opaque own parallel proof provide public requires
return self Self test theorem todo trait true type unless unreachable use uses
var view when while with
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
| `by`, `bit_vector`, `evaluation` | After an `assert`'s condition: `assert condition by bit_vector`, `assert condition by evaluation` |
| `generic` | In a `uses` list, before the name of a capability parameter |
| `tuple` | Before `type`: a tuple type (see [Tuple types](#tuple-types)) |

A parameter cannot be named `result`, a parameter of a lending method cannot
be named `final`, and no function can be named `old` or `identical`. The
reserved word `ensures` also follows a `.`, where `visit.ensures(...)` names
the postcondition of a function passed (see
[Callback contracts](#callback-contracts)). In
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

Literal's types are inferred, as in `let small: UInt8 = 3`. A local declared
from literals alone takes its type from its first use that decides it: after
`let limit = 10`, `count < limit` with a `UInt8` count makes `limit` a `UInt8`,
and so does `let digit: UInt8 = index` in the body of `for index in 0..10`. The
use may follow a method call on the local, which then computes for the decided
type: after `let mask = 255`, `mask.count_zeros()` is 0 when a later `let small:
UInt8 = mask` makes `mask` a `UInt8`, and 56 without it. When nothing decides
it, a literal has the first of `Int64`, `UInt64`, and `Float64` that its value
fits and its uses allow, so `9223372036854775808` is a `UInt64`.

- A literal operand of an arithmetic operator, a comparison, or a range takes
  the other operand's type when its value fits that type: in `count + 1` with
  a `UInt8` count, the `1` is a `UInt8`. Otherwise it has its default type, as
  the `2` in `duration * 2` does. Two literal operands have one type, so an
  integer literal and a float literal are an error. An expression made only
  of literals waits for the same decision. In a specification, a literal that
  fits neither operand's type is an `Integer`, and `Integer` is its default,
  so `span * 2` there needs a literal with a type.
- A shift amount is an unsigned integer, and a literal one is a `UInt64` by
  default.
- A literal that does not fit its type is an error. A negated literal is
  checked after the negation, so `-128` fits an `Int8`.
- A literal whose type is a type parameter bounded by an integer trait fits
  every type that implements the trait: -128 to 127 under `SignedInteger`, 0
  to 255 under `UnsignedInteger`, and 0 to 127 under `FixedWidthInteger`.
- A literal meets a bound of a sealed number trait that every type it may
  have implements. A sealed bound that only some of those types implement
  narrows the literal to them: `kept(3)` with `Value: UnsignedInteger` makes
  the `3` a `UInt64`. A literal meets any other bound once its type is
  decided. Until then, a lookup proceeds as if the bound is met: after
  `let range = 0..3`, `for index in range` finds `Range`'s `Iterable`, and
  the loop's body may still decide the type, which must then meet
  `Countable`.
- A method call on an undecided literal looks up the method in the sealed
  number traits that some of the literal's types implement, and in the traits
  those require. A method found there narrows the literal to the implementors
  of the sealed trait that provides it: `count.integer_square_root()` makes
  `count` an unsigned integer, `level.negate()` makes `level` a signed
  integer, and `count.saturating_add(1)` leaves `count` undecided. Any other
  method gives the literal its default type at the call, and so does a method
  that two unrelated traits declare: `first.absolute_difference(4)` makes
  `first` an `Int64`, since both `SignedInteger` and `UnsignedInteger` declare
  `absolute_difference`.
- A statement whose type depends on an undecided literal through an
  operator's or a trait's result gives the literal its default type at the
  statement's end, and so does reading a member, an index, or a method of
  such a result: after `let count = 2`, `let scaled = span * count` and
  `(span * count).ticks` make `count` an `Int64` when `Span` implements
  `Multiply[Int64]`.

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
(  )  [  ]  {  }  ,  :  .  ..  ..=  ->  =>  ?  |
=  +=  -=  *=  /=  %=  &=  |=  ^=  <<=  >>=
+  -  *  /  %  ==  !=  <  <=  >  >=  &&  ||  ==>  !  &  ^  ~  <<  >>
```

The lexer takes the longest match.

### Rejected sequences

These sequences are errors:

```text
//  /*  #  ;  '  `  @  ++  --  ===  !==  ::
```

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
     or one of the keywords `assert`, `break`, `capability`, `concurrent`,
     `continue`, `echo`, `exists`, `false`, `fn`, `for`, `forall`, `if`,
     `impl`, `internal`, `law`, `let`, `match`, `mut`, `own`, `parallel`,
     `proof`, `provide`, `public`, `return`, `self`, `Self`, `test`,
     `theorem`, `todo`, `trait`, `true`, `type`, `unreachable`, `use`, `var`,
     `while`.
3. Several line feeds in a row produce at most one `NEWLINE`.
4. At the end of the file, a `NEWLINE` follows the last token if it can end a
   statement.

So no `NEWLINE` comes before a closing `}`, and statements, arms, and members
are separated by `NEWLINE`s. A `NEWLINE` before a `{` that must open a body
is ignored. A line that starts with `.`, `else`, a clause keyword, `when`,
`unless`, or a binary operator other than `-` continues the line before:

```truss
let active_names = users
  .filter(fn(user) { user.is_active })
  .map(fn(user) { user.name.copy() })
```

## Files and definitions

```ebnf
file        = { use NEWLINE } { definition NEWLINE } ;
use         = "use" module_path ;
module_path = LOWER_NAME { "." LOWER_NAME } ;

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
  its module, and a module.
- A generic parameter cannot shadow a type, a trait, or a capability of its
  module, so `impl Shown for Box[Marker]` is an error where `Marker` is a
  type of the module.
- In an expression, a name before `.` is a local, a module that the file's
  `use` lines import, a definition of the file's module, or a package that
  module can use. A local shadows the other three: in
  `for network in subnets { network.contains(address) }`, `network` is the
  local even in a file that imports the `network` module.
- A module's names never repeat: a definition cannot have the name of a
  submodule of its module, and a file cannot import a module whose last name
  is a definition of its module.
- A package is named in the manifest, not in the module, so a definition may
  have the first name of a package's path. A path that starts with that name
  is an error, since it could name either.
- After a module, a path names the longest module it can, then a definition
  of that module: in `standard.json.parse`, `standard.json` is the module and
  `parse` is its function.

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
type_definition = [ "tuple" ] "type" UPPER_NAME [ generics ]
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
  none.
- A value is built the way a function is called (see
  [Calls and arguments](#calls-and-arguments)), and a field can have a
  default, as a parameter can.
- In an expression, a variant is written under its type, as in
  `Shape.Circle`, and from another module under the module too, as in
  `geometry.Shape.Circle`. The prelude's `Some`, `None`, `Ok`, and `Err`
  are written bare.
- A `type_clause` after the last variant belongs to the whole type.
- The order of a record's fields has no meaning, except in a tuple type and
  to a derived `Ordered` or `serialization.Serialize`, which follow the
  order the fields are declared in. The compiler chooses a record's layout in
  memory.
- A record with one field has none of its field's methods or operators:
  `type UserId(number: UInt64)` is a type of its own.

### Tuple types

```truss
public tuple type Span(start: UInt64, end: UInt64)

fn length(span: Span) -> UInt64
  requires span.start <= span.end
{
  let start, end = span
  end - start
}
```

- A tuple type is a record whose fields are in the order they are declared,
  and a tuple pattern matches them by position (see [Patterns](#patterns)).
- A tuple type has two or more fields. It is built as a function is called
  (see [Calls and arguments](#calls-and-arguments)): positional arguments in
  the order of the fields, then labeled ones in any order. A positional
  argument that is a variable named like another field is an error. It is
  read, updated with `with`, and matched in parentheses by name, as any
  record is.
- `map.Entry`, `core.Indexed`, and `core.Pair` are tuple types, so
  `for name, port in ports` binds each entry's key and value.

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
  variant or a collection.
- A variant that is not recursive may be `indirect` too.
- In its own fields, at any depth, a type does not occur in the input of a
  function type without `RunForever`: `type Knot(run: fn(Knot) -> Bool)` is
  an error, and `type Knot(run: (fn(Knot) -> Bool uses RunForever))` is
  legal.

### Type expressions

```ebnf
type           = path_type
               | "view" type
               | "Self" [ "." UPPER_NAME ]
               | UPPER_NAME "." UPPER_NAME
               | function_type
               | "(" function_type { function_type_clause } ")" ;

path_type      = [ module_path "." ] UPPER_NAME [ type_arguments ] ;
type_arguments = "[" type_argument { "," type_argument } [ "," ] "]" ;
type_argument  = type | INTEGER | LOWER_NAME | UPPER_NAME "=" type ;
```

- `view T` is the type of a view of a `List` or a `String`
  ([Views](#views)). `view` before any other type is an error.
- `Items.Element` names an associated type of a type parameter. It names
  no associated type of an associated type: `Source.Cursor.Element` is
  written through a parameter, as in
  `[Items: Cursor, Source: IntoCursor[Cursor = Items]]` and `Items.Element`.
- An `INTEGER` or `LOWER_NAME` argument is the value of a `UInt64` generic
  parameter, as in `Array[UInt8, 32]`.
- `UPPER_NAME "=" type` constrains an associated type, as in
  `Iterable[Element = Int64]`, including one that a required trait
  declares, as in `IterableMut[Element = Int64]`.

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
- An invariant cannot call a function whose proof depends on the
  invariant's type (see [Circular proofs](#circular-proofs)). A function that
  uses a value of the type assumes the invariant, so the invariant would be
  proven from itself. `invariant self.value() <= 10` is such an error, and
  so is `invariant through(count) >= 0` where `through` builds a value of
  the type. An invariant states its condition over the fields of `self`, and
  may call a function of a field's type, as `invariant used <= span.width()`
  does. The same rule holds for a `potential`.
- Invariants are proven, never checked when the program runs. An invariant
  holds wherever other code can observe the value: when it is built,
  directly or with `with`, passed to a call, or returned, and when its
  holder ends: a `var` at the end of its scope, and a `mut` parameter or
  `mut self` when the function returns. A `with` is checked after all of
  its updates. An element of a `List` or an `Array` meets it
  when a write to a part of the element ends, as in `spans[0].low = 1` or
  `bump(mut spans[0].low)`, since the next read of the element assumes it.
- An invariant clause that calls a definition private to its type's
  module is known only in that module. Another module assumes the clause of
  every value of the type and proves it only of a value it was given or a
  call returned, so it cannot build a value of the type from its fields when
  the clause must hold.
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
either can mutate.

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
  and records, sum types, and `Array`s built only from those, is `Plain`. A
  type that declares a `cost potential` is not (see
  [Amortized costs](#amortized-costs)).
- **A name bound to a `Plain` value is a copy.** A `let`, or a pattern of a
  `match` or an `is`, that binds a `Plain` value without `mut` copies it, so
  the place it was bound from can be assigned while the name is live. A
  compound assignment's `Plain` operand is a copy too, so an index key of
  the target can assign the operand's place. The variable of a `for` loop is
  not copied: the loop lends its collection for the body.
- **`Copyable` types have `copy()`,** whose result is identical to the
  original. A copy of a `List`, a `String`, or an `Array` costs one unit of
  time and at most one allocation, plus the cost of copying each element:
  `text.copy()` is within `cost time O(text.length())`. A copy of any other
  type costs `time(T.copy)`.
- **Handles are not `Copyable`,** nor is a type that holds one.
- `Copyable` and `Plain` are prelude traits that the compiler implements and
  no `impl` can, and `Plain` requires `Copyable`. The compiler derives them
  from a type's fields, except for an opaque type, which has them only when
  it declares them with `derives`. The compiler checks the declaration, and
  other packages rely only on it.
- A generic type has them under the conditions its fields give. Generic
  code copies only where a bound allows it.

### Views

A view refers to the elements of a `List` or the bytes of a `String` that
another value owns. A read-only parameter, a `let` bound to a place or to a
string literal, the variable of a `for x in items` loop, and a range are
views:

```truss
let middle = items[1..4]
let total = middle.sum()
mut items.push(9)
```

`items[1..4]` is a place of type `List[Int64]`. Binding it allocates nothing
and copies no element. While a view is live, that is, until its last use, the
place that it views cannot be mutated or moved. Here `push` is allowed
because `middle` is not used after it.

A view that is stored or returned is declared with `view`:

```truss
type Token(text: view String, line: UInt64)

fn first_word(text: String) -> view String

var longest: view String = words[0]
```

- **`view T` is the type of a view of a `T`,** where `T` is a `List` or
  `String`. It has the layout and the methods of `T`, is read-only, and is
  `Plain`: a copy of it views the same elements, and dropping it frees
  nothing.
- **A place of type `T` converts to a `view T`** where one is expected: in
  an argument, a field of a constructed value, an element of a literal, an
  annotated binding, an assignment, and a returned value. An `Array` converts
  to the `List` of its elements where a read-only or `mut` `List` or a
  view of one is expected.
- **A place given where a type parameter is undecided is viewed.** In
  `let found = Some(names[0])`, nothing but the argument decides the type
  parameter of `Option`. The argument is a place of a `String`, written
  without `own`, so the type argument is `view String` and `found` is an
  `Option[view String]`.
  - The rule covers an `own` parameter of a generic function, a field of a
    constructed value, an element of a list literal, and a key or a value of
    a map literal.
  - The place is of a `List` or a `String`. It may be a constant or a part
    that a method lends read-only.
  - `Some(own name)` moves `name`, and `Some(names[0].copy())` copies the
    element. Each is an `Option[String]`.
  - A place is viewed only where a view meets every bound of the type
    parameter. Given to a `Value: Storable`, the place is an owned value
    that cannot be moved.
  - Arguments decide a type parameter in the order written. After
    `pick("fig".copy(), second: names[0])` has decided `String`, the element
    is an owned value that cannot be moved. A declared type, as in
    `let found: Option[String] = Some(names[0])`, decides before any
    argument.
- **A view converts to no owned value.** `copy()` makes a `List` or a
  `String` that owns copies of the viewed elements, and a view where an
  owned value is needed is an error with that fix.
- **A read-only parameter takes a view whatever its declared type says.**
  A parameter declared `List[String]` takes a `List[view String]`, and one
  declared `Map[String, Int64]` is looked up with a `view String`: in a
  read-only argument, types are compared without `view`.
- **A parameter declared `view T` may be stored.** A parameter declared `T`
  is lent for the call. One declared `view T` views the caller's place for
  as long as the callee's `mut` parameter, `mut self`, or result may hold
  it, so the function can store it there. Storing a view of a parameter
  declared `T` is an error with a fix that declares it `view`: the caller's
  place would be mutated while the stored view is live.
- **Nothing is written through a view.** It is passed `mut` to nothing, its
  elements are not assigned, and a `mut` loop does not go over it. A `var`
  declared `view T` can be assigned: it then views other elements.
- **A `let` binds a place read-only, and a `var` binds an owned value.**
  `let rest = items[1..]` views the range. `var rest = items[1..]` is an
  error, since the elements cannot be moved out of `items`: it is written
  `var rest = items[1..].copy()` or `var rest: view List[Int64] = items[1..]`.
  A `let` whose value is an `if`, a `match`, or a block is a view when every
  branch gives a place of a `List` or a `String`.
- **Being a view is a property of a type.** `view T` and a lambda that reads
  local variables are views, and so is any type that holds one anywhere,
  such as a record with a `view String` field or a `List[view String]`.
- **`Storable`** is the prelude trait of every type that is not a view,
  which the compiler derives and no type declares.
- **A view never outlives the place that it views.** It can be bound, held
  in local records and collections, and passed as an argument, but it cannot
  go where a `Storable` value is needed.
- **A function returns a view only of the places its parameters view, or of
  the parameters themselves.** The caller treats the result as viewing
  everything that its read-only and view arguments view. An argument that
  is `Plain` lends nothing, unless it holds an `Array`: an array is stored
  in place, so a view of its elements views the argument. A value cannot
  hold a view of a part of itself.
- **A view implements a trait through the `impl` of its viewed type.**
  `view T` implements `Trait` when this `impl` would be accepted: each
  method that the `impl` of `Trait` for `T` writes is forwarded, as
  `T.method(self, other)`, and each method that it inherits from the trait
  is inherited again, with the view as `Self`. Every rule for an `impl`
  applies to it. The view implements each trait that `Trait` requires, and
  a forwarded call passes its arguments as any call does: a view passes to a
  read-only parameter of its viewed type, and to no `own` or `mut` one. So a
  `view String` is `Equal`, `Hash`, `Display`, and `Ordered`: a
  `List[view String]` is sorted in place, and a `Map[view String, Int64]` is
  keyed by views. A view implements no trait whose `impl` writes a method
  that takes `self` by `mut` or `own`, or that returns `Self`.
- **`mut` access is never stored.** It has a name only as a `mut` parameter,
  a `mut` loop's variable, or a lambda's `mut` parameter, and lasts for that
  call, iteration, or `provide mut` block. Disjoint ranges of one `List` or
  `Array` can be passed `mut` side by side, as in
  `sort(mut items[..middle])` and `sort(mut items[middle..])`, when the
  prover shows that they do not overlap.
- **A range is passed `mut` only to a parameter whose elements alone
  change.** The callee declares `modifies items[..]`
  ([Changed parts](#changed-parts)), so it assigns and mutates elements but
  cannot change the length: a `push` through a range would write past the
  range into the elements that follow it.
- **A temporary is dropped at the end of its statement,** except where a
  `let` keeps it until the end of the block that holds the `let`. A `let`
  keeps the base of a range or an element that it binds, directly or through
  fields, and a temporary that its value converts to a view. It also keeps
  such a temporary in a field of a record or variant that its value
  constructs, in a field that a `with` replaces, and in an element of an
  array literal. So `let middle = make_list()[1..4]` keeps the list for as
  long as `middle` can be used. A `let` keeps no other temporary, such as
  the argument in `let first = first_word(make_text())`. A view cannot be
  used after the temporary or the local that it views is dropped.
- **A default's temporaries are dropped at the end of the statement that
  makes the call,** as the temporaries of a written argument are. So a
  read-only parameter can have an owned default: in
  `names: List[String] = ["ab", "cde"]` the list lasts for the call.

## Constants

```ebnf
constant      = "let" constant_name ":" type "=" expression ;
constant_name = LOWER_NAME | type_head "." LOWER_NAME ;
```

```truss
public let pi: Float64 = 3.141592653589793
public let UInt8.maximum: UInt8 = 255
public let seconds_per_day: Int64 = 24 * 60 * 60
public let greeting_length: UInt64 = "hello".length()
public let word: Regex = Regex"[a-z]+"
```

- A *constant expression* is made of literals, arithmetic on numbers, other
  constants, and the records, variants, collection literals, and strings
  built from those. It calls no function except the `from_elements` or
  `from_entries` of a collection literal.
- The value of a constant is a constant expression whose parts may also be
  calls: a call of a function or a method, an operator or an index of any
  type, a tagged template, an interpolated string, and a quantifier over a
  range or a collection. Other code, such as an `if`, a `match`, or a
  lambda, goes in a function that the value calls.
- The value uses no capability, so each call in it terminates and cannot
  panic. Each call meets its callee's `requires`.
- The value is evaluated when the code is checked, and the program holds
  the result as data. An evaluation that uses more than 10 seconds of CPU
  time is an error.
- A proof that reads a constant knows its value. Where the value calls a
  function, the proof knows the result of the evaluation as far as it sees
  the type: a number, a `Bool`, a `Character`, and each field of a record or
  a variant whose fields are visible to it. It knows a collection, and a type
  whose fields it does not see, by the contracts of the calls.
- A constant's type is not a function type, and holds no function value,
  no handle, and no state that tasks share.
- A constant's value does not depend on itself: through another constant,
  through the default of a field that a record or variant in it leaves out,
  or through the code that it calls.
- A constant that a type names, as in `Array[UInt8, digest_size]`, has a
  constant expression as its value.
- Reading a constant or taking a view of it allocates nothing.

## Functions

```ebnf
function      = "fn" function_name [ generics ] parameters [ result ]
                { clause } body ;
function_name = LOWER_NAME | type_head "." LOWER_NAME ;
type_head     = [ module_path "." ] UPPER_NAME [ generics ] ;

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
    Circle(radius, ..) => math.pi * radius * radius
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

copy(original, backup)
copy(destination: backup, source: original)
let connection = connect(host, secure: false)?
```

1. A positional argument, one without a label, passes its value to the
   parameter at its position.
2. `label: value` passes `value` to the parameter named `label`.
3. Labeled arguments follow the positional ones, in any order. A positional
   argument after a labeled one is an error, and so is a parameter given
   twice.
4. Arguments are evaluated in the order written.

- A default is a constant expression that refers to no other parameter. An
  argument for a parameter with a default can be left out, and the call then
  passes the default's value. A function, a method of a type, a capability's
  method, and a trait's method that has a body can declare a default (see
  [Traits and laws](#traits-and-laws)).
- Building a record or a variant takes labeled arguments in any order,
  evaluated in the order written. A bare name that matches a field's name
  passes that variable to that field, optionally after a mode keyword. Only
  a record or variant with exactly one field takes a positional argument, as
  in `Some(3)`, except a tuple type (see [Tuple types](#tuple-types)).
- A call through a function value passes its arguments by position, without
  labels.

### Explicit type arguments

```truss
let value = parse[Int64](text)?
let builder = List[String].with_capacity(64)
let words = List[view String].with_capacity(64)
```

Type arguments that cannot be inferred are written in brackets after the
function's name.

- `name[...]` holds type arguments when `name` is a generic function, a
  type, or a trait, and is an index otherwise. After a `.`, it holds type
  arguments when the name is a method of the receiver.
- The written arguments give the generic parameters in brackets, in order.
- A type argument that is a view is written `view T`, as in a declared type.
- A capability parameter takes no type argument, since it is written at its
  uses and not in brackets: `for_each[String](names, visit: greet)` gives
  `Item` alone.

### Clauses

```ebnf
clause               = "uses" capability_use { "," capability_use }
                     | "requires" expression [ "when" condition ]
                     | "ensures" expression [ "when" condition ]
                     | "decreases" expression { "," expression } [ "when" condition ]
                     | "modifies" field_path { "," field_path }
                     | "cost" cost [ "when" condition ] ;
field_path           = ( LOWER_NAME | "self" ) "." LOWER_NAME { "." LOWER_NAME } ;
capability_use       = capability_reference [ "unless" unless_condition ] ;
capability_list      = capability_reference { "," capability_reference } ;
capability_reference = path_type
                     | "Self" "." UPPER_NAME
                     | UPPER_NAME "." UPPER_NAME
                     | "generic" UPPER_NAME ;
```

```truss
public fn binary_search[Element: Ordered](sorted: List[Element], target: Element) -> Option[UInt64]
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
| `modifies` | The parts of `mut` parameters that the function changes. Without it, every part of a `mut` parameter may change. | At most one |
| `cost` | A proven bound on a resource | Any |

- Repeated clauses all hold. Each `requires` may rely on the `requires`
  before it, and each `ensures` on every `requires` and the `ensures`
  before it. A clause with a condition relies only on the clauses whose
  conditions its own implies.
- A function's *contract* is its `requires`, `ensures`, `decreases`, and
  `cost` clauses.
- No clause is evaluated when the program runs.
- `Self.Uses` and `Source.Uses` name an associated capability set (see
  [Associated capability sets](#associated-capability-sets)).
- Every clause but `uses` and `modifies` can end with `when` and a
  condition, and each capability in `uses` with `unless` and a condition
  (see [Conditions](#conditions)).

### Conditions

```ebnf
condition        = bound_condition { "&&" bound_condition } ;
unless_condition = unless_atom { "&&" unless_atom } ;
unless_atom      = bound_condition | comparison ;
bound_condition  = ( UPPER_NAME | "Self" ) ":" bound ;
```

```truss
public fn List[Element].collect[Source: Cursor[Element = Element]](source: own Source) -> List[Element]
  uses Source.Uses, RunForever unless Source: FiniteCursor
  ensures result.length() <= old(source.remaining()) when Source: FiniteCursor
```

A *condition* states that type arguments implement traits. A clause with a
condition holds for the instantiations that meet it.

- `T: Trait` holds where the type argument for `T` implements `Trait`, and
  `T: First + Second` where it implements both. `&&` joins conditions that
  all hold.
- A condition names a type parameter of its definition or of the
  definition's type or `impl`, or `Self` in a trait or an `impl`, as a bound
  does. An associated type is named through a type parameter bound to it:
  `[Element, Items: Cursor[Element = Element]]`, and then
  `when Element: Display`.
- A clause holds where its `when` condition holds, and a capability in
  `uses` is used only where its `unless` condition does not hold. Every
  clause of a function and of a loop takes a condition: `requires`,
  `ensures`, `decreases`, `cost`, and `invariant`.
- **A clause is checked with its condition's bounds,** so it can call the
  methods of the condition's traits: the `ensures` above calls
  `source.remaining()`, a method of `FiniteCursor`. The body is checked
  without them, because it runs for every instantiation.
- **A clause with a condition is proven where the condition holds.** An
  `ensures`, a `cost`, an `invariant`, and a measure are proven for the body
  with the condition's bounds: a call through them has their traits'
  contracts, and a callee's clause holds where the bounds imply its
  condition.
- **A call has each clause of its callee whose condition holds for the
  call's type arguments.** A condition holds where an `impl` gives it, as a
  bound does, or where the caller's bounds or the condition of the caller's
  own clause imply it. `List.collect(word.characters())` uses no
  `RunForever`, since `Characters` implements `FiniteCursor`.
  `List.collect(channel.messages())` uses `RunForever`. In a function generic
  over `Items: Cursor`, `List.collect(own items)` uses
  `RunForever unless Items: FiniteCursor`.
- A call whose type arguments leave the condition of a `requires` undecided
  proves the `requires` with the condition's bounds.
- A condition on a type built from type parameters holds where an `impl`
  gives it: `Skip[Source]: FiniteCursor` holds where `Source: FiniteCursor`
  does, by `impl FiniteCursor for Skip[Source: FiniteCursor]`.
- A capability that code uses `unless` a condition is available where the
  function's `uses` names it with no condition, or `unless` a condition that
  implies the code's. A trait implies the traits it requires, so
  `RunForever unless Items: Short`, where `Short: FiniteCursor`, covers
  `RunForever unless Items: FiniteCursor`.
- A written function type takes no condition. The type of a function named
  as a value keeps each condition that its type arguments do not decide.
- A condition that names neither a type parameter nor `Self` is an error,
  since it is decided where it is written, and so is a clause whose
  condition no instantiation meets.

#### Conditions on values

```truss
public fn Option[Value].expect(own self, message: String) -> Value
  uses Panic unless self is Some(_)
  ensures self is Some(held) && identical(result, held)
```

- **`Panic` can be `unless` a condition on the arguments.** The condition
  is a `&&` of `Bool` expressions over the parameters, read at entry, as a
  `requires` is. No other capability takes one, and it is not joined with a
  bound.
- **A caller without `Panic` proves the condition, as it proves a
  `requires`.** A caller that has `Panic` proves nothing. A caller that uses
  `Panic unless C` proves the condition where `C` holds.
- **The body is proven twice.** It is proven once with `Panic`. It is
  proven again assuming the condition, without `Panic`: every operation that
  could fail is proven not to, and every call that uses `Panic` is proven
  unreachable.
- **A specification that calls such a function proves its condition,** as
  it proves a callee's `requires`, since a specification never panics. A
  function whose only capability is `Panic unless P` can be called in a
  specification: `forall i in 0..text.length() => text.byte(i) < 128`.
- **A trait's method can take one.** An `impl`'s method of it states its
  own `uses Panic unless` a condition, which the trait's must imply, or uses
  no `Panic`. A call known to reach an `impl` proves that `impl`'s
  condition, and a call through a bound proves the trait's.
- A function named as a value uses `Panic`, since the code that a call of
  the value reaches is chosen when the program runs. A capability's method,
  a written function type, and a `when` condition take no condition on
  values.

### Changed parts

```truss
type Reader(text: String, position: UInt64, lines: UInt64)
  invariant position <= text.length()

fn Reader.skip_spaces(mut self)
  modifies self.position
  ensures old(self.position) <= self.position
{
  while self.position < self.text.length() && self.text.byte(self.position) == 32
    invariant old(self.position) <= self.position
  {
    self.position += 1
  }
}

fn Reader.start_word(mut self) -> UInt64
  modifies self.position
  ensures self.lines == old(self.lines)
{
  mut self.skip_spaces()
  self.position
}
```

- **`modifies` names the parts of `mut` parameters that a function
  changes.** A part is a `mut` parameter or `self` followed by one or more
  field names, such as `self.position` or `cursor.region.stop`. The fields
  are those of record types: one element of a collection and a field of a
  variant are not fixed parts, so the clause names the field that holds
  them.
- **A part followed by `[..]` is the elements of a `List` or a `String`,**
  as in `modifies items[..]` or `modifies self.rows[..]`. The function
  assigns and mutates elements and keeps the length, so a caller's proof
  keeps `items.length()`, and the caller can pass a range, as in
  `sort(mut items[..middle])` ([Views](#views)). A function that changes the
  length names the part without `[..]`.
- **Every other part of a parameter that the clause names keeps its
  value.** `start_word` ensures that `lines` is unchanged although
  `skip_spaces` states nothing of it: a caller's proof keeps what it knew of
  every part that the callee does not name.
- **A `mut` parameter that the clause does not name may change in every
  part,** as every `mut` parameter of a function without `modifies` may.
- **The body changes only the parts named.** An assignment changes its
  target. A `mut` argument, a `mut` binding, a `mut` loop variable, and a
  part lent `mut` change their place, and a call of a function with
  `modifies` changes the parts that it names of its arguments. A change
  outside the clause is an error, since the proofs of the callers take
  every other part to keep its value.
- **A part that the clause names and the body never changes is a
  warning,** since the proofs of the callers do not learn that the part
  keeps its value. Where no part of a parameter that the clause names
  changes, the parameter need not be `mut`. A trait's method is not
  checked, since its clause bounds what every implementation changes, and
  neither is a body with a `todo`.
- A caller that cannot see the fields of a parameter's type, because the
  type is opaque in another package, takes every part of the argument as
  changed.
- **An `impl`'s method changes only the parts that its trait's method names
  for each parameter.** Its own `modifies` can name fewer, and without one
  it has the trait's.
- A function type has no `modifies`, so a call through a function value
  changes every part of its `mut` arguments.

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

- **A function terminates unless its `uses` names `RunForever`.** One whose
  `uses` names `RunForever unless C` terminates where `C` holds (see
  [Conditions](#conditions)). A loop without a measure uses `RunForever`
  (see [Loops](#loops)), and so does a call of a function that uses it.
  `RunForever` is otherwise a capability like any other: a function type
  without it takes only functions that terminate, and a capability
  parameter holds it where a function passed for the parameter may run
  forever (see [Capability parameters](#capability-parameters)).
- `RunForever` has no methods, and nothing implements it. A `parallel`
  branch or a quantifier may run forever where its function may.
- A function that uses `RunForever` has no `time` clause. One that uses
  `RunForever unless C` states its `time` clause `when` a condition that
  implies `C`.
- A `RunForever` that a function declares and does not use is a warning. The
  function uses it where a call or a loop in it uses `RunForever`, where one
  of its `while` loops takes its measure from its condition, or where a
  recursion reaches the function. A method written in a trait or an `impl`
  is not checked.
- A call of a capability's method terminates unless the method's `uses`
  names `RunForever`. A method that waits for the world, such as
  `Console.read_line`, returns once the world answers, so waiting is not
  running forever. An implementation whose method may run forever declares
  `uses RunForever` on its `impl`, and providing it requires `RunForever`.
- A trait's method runs forever only where its `uses` names `RunForever` and
  no `unless` condition of it holds, or names an associated capability set
  that an `impl` puts `RunForever` in
  (see [Associated capability sets](#associated-capability-sets)).
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

- The parameters whose types are declared with `type` are compared in the
  order they are declared, as a list of measures is. The first of them that
  a recursive call does not pass unchanged must be passed a part of itself,
  and the parameters after it may be any value. The recursive call below
  needs nothing written because `chain` is declared before `reversed`. Declared in the
  other order, the function would have to state `decreases`:

  ```truss
  fn reverse_onto(chain: Chain, reversed: own Chain) -> Chain {
    match chain {
      End => reversed
      Link(value, rest) => reverse_onto(rest, reversed: Chain.Link(value, rest: own reversed))
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
- A function whose `decreases` has a condition `C` uses
  `RunForever unless C`, and its recursion is proven to end where `C` holds,
  as with `decreases source.remaining() when Source: FiniteCursor`.
- **A recursion is followed through each call to the code that the call
  runs.** The callee decides which code that is:

  | The callee | The code that the call runs |
  |---|---|
  | A function, or a method of a type | That function or method |
  | A trait's method, on a type whose `impl` is known | That `impl`'s method: the method written in the `impl`, the method that the `impl` derives, or the provided method that the `impl` inherits |
  | A trait's method, through a bound on a type parameter | Code that a caller of the enclosing function supplies, as the next rule says |
  | A function value | Code that a caller of the enclosing function supplies, as the next rule says |

  A provided method that an `impl` inherits runs the trait's body for that
  `impl`, so a call on `Self` in the body runs the same `impl`'s method. The
  body is also checked once, for every `impl`. In that check a call on `Self`
  is followed to the trait's method, so provided methods that call each
  other are a recursion.
- **Code that supplies other code to a callee is followed to all of the
  supplied code:**

  | The supplier | The supplied code |
  |---|---|
  | A call that gives a type argument to a type parameter with a bound. The parameter is one of a generic function, of a generic `impl`, of a generic type with a derived `impl`, or of a trait's generic method | Every method of the type argument's `impl` of the bound |
  | A function named as a value | The function, and the code that its type arguments supply |
  | A `provide` | Every method of the provided `impl` |

- **A recursion that leads back to a function without `RunForever` is proven
  to terminate, or is rejected.** The way back decides:

  | The way back to the function | The requirement |
  |---|---|
  | A call of a function, of a method written in an `impl`, or of a trait's method on `Self` | The call is on a part of a parameter, or each function in the cycle states `decreases` |
  | A call of a method that its `impl` derives or inherits | Rejected |
  | Supplied code | Rejected |

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
- **`calls` of a capability counts the calls that reach the caller's
  provider.** A call inside a `provide` goes to the provided
  implementation, which calls the next provider out only if its `impl`
  uses that capability. No clause bounds those calls, so a call to an
  implementation that uses the counted capability has no known count, and
  a call to one that does not counts as none. A capability method whose
  declaration uses another capability may call that one any number of
  times.
- `O(f)` means that the cost is at most `c * f + d` for every input, for
  some constants `c` and `d`.
- `time` counts abstract steps: each primitive operation and each call is one.
- A default that a call or a construction fills in is evaluated there, and
  its cost counts toward the enclosing function's.

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
  gives it (see [Callback contracts](#callback-contracts)).
- At a call, the cost of a bound's method has the value of the bound that
  the type argument's `impl` states for the method, where that bound reads
  no parameter, `result`, or `old`. `time(Element.equal)` is a constant for
  `Int64`, whose `impl Equal` promises `cost time O(1)`, and
  `allocations(Element.equal)` is 0, since that `impl` promises
  `cost allocations == 0`. `time(Element.compare)` is
  `4 * time(Int64.compare)` for `Array[Int64, 4]`, whose `impl Ordered`
  promises `cost time O(count * time(Element.compare))`.
- A bound that reads a parameter gives the term no value: `List`'s
  `O(self.length() * time(Element.compare))` depends on the list.
- A method with generic or capability parameters of its own takes a value
  only from a bound that is an integer. Its other bounds can name those
  parameters, and a term such as `time(Item.serialize)` supplies no
  argument for them.
- `time(...)` has no value for a method that returns a value with
  potential or takes one as `mut`, since a plain bound does not count the
  potential that the call makes. A derived `Default` is the exception: the
  cost of its body includes the potential of its value.
- `time(...)` has no value for a type argument whose `impl` of the method
  may run forever (see [Termination](#termination)), and `allocations(...)`
  and `allocated_bytes(...)` have none where the `impl` states no bound on
  that resource. A bound that names the term is then unbounded.
- A function with an `==` bound on a resource calls a callback only where
  the cost of the call is exact: the callback's type states an `==` bound on
  that resource, or the callback's bound is zero. The cost of any other call
  is only bounded above.

```truss
fn List[Element: Equal].contains(self, item: Element) -> Bool
  cost time O(self.length() * time(Element.equal))
  cost allocations <= self.length() * allocations(Element.equal)
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
  new one. A view holds no potential: the potential of the elements that it
  views belongs to their owner, so a `List[view String]` holds only its own.
- **Potential is owned like the value that holds it.** `own` transfers it.
  `mut` lends it, and the borrower's bound covers the change. Read-only
  access, a view's included, changes none.
- A type that declares a `cost potential`, or holds a value that does, is not
  `Plain`, since an implicit copy would duplicate its potential. A type
  parameter bounded by `Plain` holds no potential.
- `cost amortized time O(f)` promises that the actual cost, plus the change
  in the potential of the values the function mutates or returns, is within
  `O(f)`. `amortized` takes only an `O(...)` bound, on `time`, `allocations`,
  or `allocated_bytes`. Potential pays for no calls, and an exact count with
  `<=` or `==` cannot borrow from it.
- A function may state a plain and an amortized bound on one resource. A
  caller counts each call by the bound of its own kind.
- A caller with an amortized bound counts a callee's amortized bound as
  stated, and never reads the potential that the callee changes. It counts
  a callee that states only a plain bound at that bound plus the change in
  the potential of the values the call mutates, consumes, or returns.
- A caller with an amortized bound also counts the potential that its own
  code makes. A value it builds counts its type's potential. A write counts
  the change in the potential of the values that contain the written place.
- A caller with a plain bound counts a callee's plain bound. Where the
  callee states only an amortized bound, the caller counts that bound less
  the change in potential. A function that pushes only onto a list it
  creates empty therefore has a plain bound, since the list starts with no
  potential to spend.
- **Potential that a call saves pays for no step.** Under a plain bound it
  only offsets a later call that spends it. So an `O(...)` bound must also
  hold when every call counts at its callee's bound and no operation counts
  a change in potential. For an amortized bound, that count may spend the
  potential that the `mut` and `own` parameters hold on entry, since the
  caller pays for it. This prevents a false bound: potential that callees
  save in a value that is dropped, kept under a plain bound, or spent by the
  function's own code would otherwise pay for the steps of the calls that
  saved it, and `count` calls of an `O(1)` amortized function would prove
  `O(1)`.
- **A capability method's `O(...)` bound counts the change in the potential
  of its provider,** whether or not it is `amortized`. An `impl` of the
  capability is checked so, and a caller counts the bound as stated. A plain
  bound of a function that uses a capability is therefore relative to the
  potential its provider holds, and the function with the `provide` block
  counts, in its plain bounds, the potential that the provider held when the
  block began.

### Function types

```ebnf
function_type        = "fn" "(" list([ LOWER_NAME ":" ] [ mode ] type) ")" [ "->" type ] ;
function_type_clause = "uses" capability_list | "cost" cost
                     | "requires" expression | "ensures" expression ;
```

```truss
fn sort_by(items: mut List[Item], compare: fn(Item, Item) -> Ordering)
fn serve(handle: (fn(Request) -> Response uses Database, Log))
```

- A function type without `uses` uses no capability. Its `uses` clause
  cannot mention its inputs.
- An `O(...)`, `<=`, or `==` bound in a function type is an integer
  literal, as in `(fn(Item) cost time O(1) cost allocations <= 2)`. A bound
  that depends on a value, such as a parameter of the enclosing function,
  goes in that function's own `cost` clause, which names the callback's cost
  as `time(visit)`.
- **A function type takes only functions whose capabilities its `uses`
  names,** so one without `RunForever` takes only functions that terminate
  (see [Termination](#termination)).
- A function type's bound is met only by a bound of the same kind: a plain
  bound does not stand for an amortized one, nor an amortized bound for a
  plain one.
- Clauses after a definition's result type belong to the definition.
- A function type's `requires` and `ensures` are a callback's contract (see
  [Callback contracts](#callback-contracts)).
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
  and so does the call. Where it is a lambda that takes `Panic` (see
  [Failure](#failure)), `Granted` holds `Panic`.
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

### Callback contracts

```truss
type Card(rank: UInt8, suit: UInt8)

fn pick[Item: Copyable](
  items: List[Item],
  choose: (fn(count: UInt64) -> UInt64 uses generic Granted requires count > 0 ensures result < count),
) -> Item
  uses generic Granted
  requires items.length() > 0
{
  items[choose(items.length())].copy()
}

fn deal(deck: List[Card]) -> Card
  uses Random
  requires deck.length() > 0
{
  pick(deck, choose: fn(count) { Random.next() % count })
}

fn Option[Value].map[Output](
  own self,
  transform: (fn(own Value) -> Output uses generic Granted),
) -> Option[Output]
  uses generic Granted
  ensures match self {
    Some(value) => result is Some(output) && transform.ensures(value, output)
    None => result is None
  }
  cost time O(time(transform))
  cost allocations <= allocations(transform)

fn halved(value: Option[Int64]) -> Option[Int64]
  ensures match value {
    Some(inner) => result is Some(half) && half == inner / 2
    None => result is None
  }
  cost allocations <= 0
{
  value.map(fn(inner) { inner / 2 })
}
```

A *callback contract* is what a function knows of the function passed for
one of its parameters: the `requires` and `ensures` of the parameter's
type, and the terms `time(visit)`, `allocations(visit)`,
`allocated_bytes(visit)`, and `visit.ensures(...)`.

- **A `requires` or an `ensures` in a function type appears only on the type
  of a definition's parameter,** at the top level of that type, and the type
  then names its inputs. Each can mention the inputs and the parameters
  before that parameter. In the `ensures`, `result` is the callback's result,
  and `old(input)` is a `mut` input's value when the callback was called.
- **The definition proves the `requires` at every call through the
  parameter, and each such call meets the `ensures`.**
- **At a call of the definition, the function passed is proven against both
  clauses.** A lambda's body may rely on the `requires`, and proves the
  `ensures`, as `deal`'s lambda relies on `count > 0` and proves
  `result < count`. A named function accepts every argument that the
  `requires` allows, and its own `ensures` implies the type's there. A
  parameter of the caller is accepted where its type's clauses imply the
  callee's. Any other function value promises nothing of its results.
- **An `impl`'s method states the callback contracts of its trait's method,**
  clause for clause, since a call through the trait proves and assumes those.
- **`visit.ensures(...)` holds where the function passed for `visit` may
  return the given result for the given arguments.** Its operand is a
  function parameter of the enclosing definition. Its arguments are the
  callback's inputs in order, a `mut` input giving its value at entry and
  then at exit, followed by the callback's result if it has one, as in
  `transform.ensures(value, output)`. It appears only in specifications.
- **`visit.ensures` is a relation, not a call.** A callback may return
  different results for one argument, as one that reads `Random` does. Each
  call through the parameter makes `visit.ensures` hold of that call's
  arguments and result, and the definition knows nothing else of it. A
  function that uses no capability and has no `mut` input returns one
  result, so for it `visit.ensures(value, output)` holds exactly where
  `output` is that result.
- **At a call, each term of a callback contract takes its value from the
  function passed:**

  | The function passed | `time(visit)`, `allocations(visit)`, `allocated_bytes(visit)` | `visit.ensures(...)` |
  |---|---|---|
  | A lambda | A bound on its body for every argument | Where its body may return that result for those arguments |
  | A named function | For `time`, a constant where its clause is `O(n)` for a literal `n`. For `allocations` and `allocated_bytes`, `n` where its clause is `<= n` or `== n` for a literal `n`. | Where its `ensures` holds |
  | A parameter of the caller | The caller's own term | The caller's own `visit.ensures` |

  A function that states no bound on a resource has no value for that term,
  and neither has one whose bound is `amortized`, which bounds a call
  together with the potential it changes. A bound that names the term is
  then unbounded, so the caller proves no bound on that resource through the
  call.
- **A law over a callback's answers is stated over `visit.ensures`.** A
  contract that needs the law makes it the premise of an implication, so the
  conclusion holds for every callback that keeps the law, and a callback
  that breaks it loses only the conclusion:

  ```truss
  fn List[Element].max_by(
    self,
    compare: (fn(Element, Element) -> Ordering uses generic Granted),
  ) lends Option[Element]
    uses generic Granted
    ensures (result is Some(_)) == (self.length() > 0)
    ensures self.model().is_totally_ordered_by(compare) ==> match result {
      Some(largest) => forall i in 0..self.length() => !compare.ensures(self[i], largest, Ordering.Greater)
      None => true
    }
  ```

## Methods

```truss
fn List[Element].with_capacity(capacity: UInt64) -> List[Element]

fn List[Element].push(mut self, item: own Element)

fn List[Element: Ordered].sort(mut self)
  modifies self[..]
  cost time O(self.length() * log(self.length()) * time(Element.compare))

fn List[Element].zip[Other](self, other: List[Other]) -> Zipped[Element, Other]
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
  `fn hourly.Forecast.summary(self) -> String`.

### Overloads by receiver mode

```truss
fn List[Element: Copyable].filter(self, keep: fn(Element) -> Bool) -> List[Element]
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
- **A `match` arm lends as an `if` does,** with the scrutinees, the arm's
  patterns, and its guard as the condition, and the arm's body as the
  then-block. Each arm decides for itself, so an arm whose names are copies
  can mutate the receiver. A part that a scrutinee lends stays lent while the
  arms are tested. A guard that fails ends its lends before the next arm is
  tested.

  ```truss
  fn tally(counts: mut Map[String, UInt64], word: String) {
    match counts.get(word) {
      Some(count) => counts[word.copy()] = count.saturating_add(1)
      None => counts[word.copy()] = 1
    }
  }
  ```

- **For that long, the receiver is lent whole:** the statement makes no other
  use of a receiver lent `mut`, and does not mutate one lent read-only. A
  receiver that is a view lends its original too, so `names[..].first()`
  lends `names`. Two elements or ranges of one `List` or `Array` can be lent
  together when the prover shows that they do not overlap.
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
fn List[Element].get(self, index: UInt64) lends Option[Element] {
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
impl IterableMut for List[Element] {
  fn element(mut self, position: UInt64) lends mut Element
    requires position < self.count()
    ensures identical(result, old(self.model())[position])
    ensures identical(self.model(), old(self.model()).update(position, value: final(result)))
  {
    mut self[position]
  }
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
```

- `next()` returns `Some` of the next value, which the caller owns, or
  `None` when the cursor has no more.
- `Uses` is the set of capabilities that `next` uses. Each `next` uses the
  implementations provided where it is called.

A cursor whose values run out implements the prelude trait `FiniteCursor`:

```truss
trait FiniteCursor: Cursor {
  fn remaining(self) -> UInt64

  fn next(mut self) -> Option[Self.Element]
    uses Self.Uses
    ensures (result is Some(_)) ==> self.remaining() < old(self.remaining())
}

impl FiniteCursor for Countdown {
  fn remaining(self) -> UInt64
    ensures result == self.left
  {
    self.left
  }
}
```

- `FiniteCursor` restates `next` to promise that each `next` that returns
  `Some` makes `remaining()` smaller (see
  [Traits and laws](#traits-and-laws)). `impl FiniteCursor for Countdown`
  proves it from the `ensures` of `Countdown`'s `next` and `remaining`.
- A loop over a `FiniteCursor` therefore terminates with no measure written
  (see [Loops](#loops)). A cursor that may give values forever, such as a
  channel's `Messages`, implements only `Cursor`.

## Statements and blocks

```ebnf
block     = "{" lines(statement) "}" ;

statement = "let" binding_pattern "=" expression [ "else" block ]
          | "var" binding_pattern "=" expression [ "else" block ]
          | expression [ assignment_operator expression ]
          | "for" binding_pattern "in" expression { loop_clause } block
          | "while" expression { loop_clause } block
          | "parallel" block
          | "parallel" "for" binding_pattern "in" expression { loop_clause } block
          | "concurrent" block
          | "concurrent" "for" binding_pattern "in" expression { loop_clause } block
          | "proof" block
          | "assert" expression [ "by" ( "bit_vector" | "evaluation" ) ] ;

binding_pattern = pattern [ ":" type ] | tuple_pattern ;
assignment_operator = "=" | "+=" | "-=" | "*=" | "/=" | "%="
                    | "&=" | "|=" | "^=" | "<<=" | ">>=" ;
loop_clause = ( "invariant" expression | "decreases" expression { "," expression }
              | "cost" cost ) [ "when" condition ] ;
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
  Parameters are exempt. Assigning a variable as a whole does not read it,
  and a compound assignment such as `+=` does.
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
- `assert condition by evaluation` is proven by evaluating its condition
  when the code is checked, and then holds where it is written. The
  condition is an expression that the value of a constant can be (see
  [Constants](#constants)), so it names no variable and no parameter, and it
  mentions no type parameter of the code around it. It is code, in a theorem
  too: it uses no capability, and each call in it meets its callee's
  `requires`. It is not evaluated when the program or a test runs. An
  evaluation that gives `false`, that reaches a `todo`, or that uses more
  than 10 seconds of CPU time is an error.

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
                | [ module_path "." ] TAGGED_STRING ;
constant        = module_path "." LOWER_NAME
                | [ module_path "." ] UPPER_NAME "." LOWER_NAME ;
pattern_fields  = "(" list(pattern_field) ")" ;
pattern_field   = LOWER_NAME ":" pattern | pattern | ".." ;
tuple_pattern   = pattern "," pattern { "," pattern } ;
```

```truss
match shape {
  Circle(radius, ..) => todo
  Rectangle(corner, opposite_corner) => todo
  Empty => todo
}

match status_code {
  http.ok => todo
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
  or its type, `http.ok` or `Status.teapot`. A constant in a pattern has a
  type with structural equality (see [Equality](#equality)).
- Range patterns match integers and characters.
- A tuple pattern matches a tuple type, one pattern for each field, in the
  order of the fields. It is written without parentheses, and only as the
  whole pattern of a `let`, a `var`, or a `for`.
- In a tuple pattern, a bare name that names another field of the type is
  an error. Matched by position, `for value, key in ports` would bind each
  key under the name `value`.
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

while mut queue.pop() is Some(task) {
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
update = [ LOWER_NAME { "." LOWER_NAME } ":" ] expression ;
```

```truss
type Point(x: Float64, y: Float64)

type LogLevel =
  | Information
  | Warning

type Server(host: String, port: Int64)

type Config(server: Server, log_level: LogLevel)

fn moved(origin: Point) -> Point {
  origin with (x: 1.0)
}

fn production(config: own Config) -> Config {
  own config with (server.port: 443, log_level: LogLevel.Warning)
}
```

- `base with (updates)` means copying the base into a new variable,
  assigning its fields, and returning it.
- The base is passed as an `own` argument is: a base that is a place takes
  `own`, unless it copies implicitly.
- The updates follow the rules of a construction's arguments, with a path
  of fields for a label: each names a field of the record once, a bare name
  goes to the field it names, as in `with (own name)`, and each value is
  passed to its field as an `own` argument is.
- `a.b: value` builds `a` anew with `b` updated, so it names `a`, and no
  other update names `a` itself.
- `with` works on records, and updates only fields visible at that point.

### Lambdas

```ebnf
lambda           = "fn" "(" list(lambda_parameter) ")" block ;
lambda_parameter = pattern [ ":" [ mode ] type ] ;
```

```truss
let passing = scores.filter(fn(score) { score >= threshold })
mut scores.update_each(fn(score) { score = score / 2 })
let halve = fn(score: UInt8) { score / 2 }
```

- A lambda's parameter modes and types come from the function type it is
  passed as. An annotation states them as a function's parameter does, so
  `score: UInt8` is read-only and `score: mut UInt8` is `mut`. An
  annotation must state the mode and the type that the function type gives:
  it never converts the argument.
- A lambda that nothing passes as a function type takes its parameter modes
  and types from its annotations: `halve` has the type
  `fn(UInt8) -> UInt8`.
- Types are inferred from the outside in, never from the lambda's body.
  Each parameter's type is decided before the body is checked, by the
  function type or by the annotation, and a parameter whose type neither
  decides is an error.
- A lambda declares no result type. Its result type is the type of its
  body's value, converted to the function type's result.
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
  let config = toml.parse(text).map_error(ConfigError.Malformed)?
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

- **A `for` loop calls the methods of a prelude trait,** as an operator
  does, and never a method found by its name:

  | Loop | The iterable implements | Each iteration |
  |---|---|---|
  | `for item in items` | `Iterable` | Is lent `items.element(position)` |
  | `for item in mut items` | `IterableMut` | Is lent `mut items.element(position)` |
  | `for item in own items` | `IntoCursor` | Owns a value of the cursor that `items.cursor()` returns |
  | `for item in cursor` | `Cursor` | Owns the value that `cursor.next()` returns |

  An iterable that does not implement its loop's trait is pulled as a
  `Cursor`, and one that implements neither is an error.
- **A `for` loop over a collection visits its elements by position.**
  `for item in items` evaluates `items.count()` once, and each iteration is
  lent `items.element(position)`, for each position from zero up to the
  count. An iteration over a `List` or an `Array` is lent the element place
  `items[position]` instead, and calls no `element`.
- `List` and `Array` implement `Iterable` and `IterableMut` for generic
  code. A `mut` loop over a range, as in `for item in mut items[1..]`, is
  lent the range's element places. A view is read-only, so no `mut` loop
  goes over one ([Views](#views)).
- A `mut` loop mutates elements but does not add or remove them: each
  iteration leaves the collection's `count` as it was, as
  `IterableMut.element` promises.
- The methods of `Iterable` and `IterableMut` use no capability, as those of
  `Index` do not, so a loop by position uses none and terminates. A
  collection whose elements need a capability to reach, such as lines read
  from a file, is a `Cursor`, whose `Uses` names the capabilities.
- `for item in own items` moves each element out: it pulls the cursor that
  `items.cursor()` returns.
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
- **A loop's proof keeps every part that its body does not change.** The
  body changes the places that it assigns, passes `mut`, and lends `mut`,
  and the parts that its callees' `modifies` clauses name. At the start of
  an iteration, the proof knows of a changed part only what the invariants
  state: a loop that assigns `reader.position` keeps what the proof knew of
  `reader.lines`.
- `decreases` names an integer measure that every iteration makes smaller
  and that never goes below zero. It holds in every function, including
  one that uses `RunForever`. A `while` compares its measure before each
  evaluation of its condition, so a change that the condition makes counts
  toward the iteration.
- A loop whose measure has a condition `C` uses `RunForever unless C`.
- Where a `for` loop over a `cursor` of type `T` states no measure, it has
  `decreases cursor.remaining() when T: FiniteCursor`, which holds as a
  written measure does. A loop over a `ListCursor` therefore terminates, and
  a loop over a cursor of type `Items: Cursor` uses
  `RunForever unless Items: FiniteCursor`.
- In a function without `RunForever`, a `while` loop that states no measure,
  and whose condition compares two sides that mutate nothing with `<`, `<=`,
  `>`, or `>=`, has the distance between them as its measure. So does one
  whose condition is a chain of `&&` that begins with such a comparison, as
  in `while at < text.length() && text.byte(at) == 32`.
- **A loop without a measure uses `RunForever`** (see
  [Termination](#termination)). A `for` loop over a range or over a
  collection's elements always terminates.
- In the clauses of a loop over a range, the loop variable is the index of
  the next iteration: in `for i in start..end`, `i` is `start` on entry and
  `end` where the loop ends, and `end + 1` after `start..=end`.
- In the clauses of any other `for` loop, `visited` is the `Sequence` of the
  values of the iterations before. The clauses cannot name the element. A
  local named `visited` shadows the word.
- In a loop that reads a collection, `visited[i]` is the collection's
  element at position `i`: `items[i]` of a `List` or an `Array`, and
  otherwise the value of the collection's `element` at
  position `i`, which meets that method's `ensures`.
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
  elements, or of `from_entries` with a `List` of one `map.Entry` for each
  key and value, in the order written. It costs that list and that call.
- `from_entries` requires keys that are pairwise distinct by `==`, so a map
  literal's keys are proven distinct.
- A list literal may repeat an element, and `from_elements` decides which of
  two equal elements a collection keeps.

### Indexing

| Indexing | Meaning |
|---|---|
| `items[i]` | Element `i`, which is proven in bounds |
| `items[1..4]` | The range of elements 1 to 3, a `List`, whose bounds are proven |
| `items.model()[1..4]` | In a specification, the `Sequence` of positions 1 to 3 of a `Sequence`, whose bounds are proven |
| `ports[name]` | The value for `name`, which is proven present |
| `items[i] = value` | Replaces element `i` |
| `ports[own name] = 8080` | Inserts or replaces the value for `name` |

- **An element of a `List` or an `Array` is a place,** as a field of a
  record is. `items[i]` names the element at position `i`, and
  `items[1..4]` names the range of positions 1 to 3, a place whose type is a
  `List` of the element type. A range of a `String` is not written: `part`
  and `substring` give one. Neither an element nor a range calls a method.
  So `let first = names[0]` binds a view of the element,
  `names[0].count += 1` mutates it in place, and `mut names[1..]` passes the
  range `mut` ([Views](#views)).
- A range of a `Sequence` is a value, not a place. Its bounds are `Integer`s,
  and its elements are the `Sequence`'s from the first bound up to the second.
- An index and the bounds of a range are evaluated before the element or
  the range is reached, so `items[grow(mut items)]` is checked against the
  length that `grow` leaves. Evaluating an element or a range checks its
  bounds even where nothing reads it, as in `let _ = items[2]`.
- Any other type supports `[]` by implementing the prelude trait `Index`
  (see [Associated types](#associated-types)), which lends an element
  read-only. `List` and `Array` implement it for generic code.
- Such a type whose elements are mutated in place also implements
  `IndexMut`, whose `at(mut self, key)` lends an element `mut`.
  `entries[key].name = text`, `entries[key] += 1`, and `mut entries[key]`
  need it. `List` and `Array` implement it for generic code.
- `collection[key] = value` calls `assign` when the type implements
  `IndexAssign`. The collection must accept the key, by its `accepts_key`:
  a `Map` accepts every key and inserts a missing one. For a type that
  implements `IndexMut` and not `IndexAssign`, the assignment replaces the
  element that `IndexMut` lends, so the key is there.
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
           | ( "mut" | "own" ) postfix
           | postfix ;

postfix    = primary { "." LOWER_NAME
                     | "." UPPER_NAME
                     | "." TAGGED_STRING
                     | "[" brackets "]"
                     | "(" list(argument) ")"
                     | "?"
                     | "with" "(" list(update) ")" } ;
brackets   = bracket_item { "," bracket_item } [ "," ]
           | [ additive ] ".." [ additive ]
           | [ additive ] "..=" additive ;
bracket_item = expression | UPPER_NAME "=" type | "view" type ;

primary    = INTEGER | FLOAT | STRING | TAGGED_STRING
           | "true" | "false" | "todo" | "unreachable" | "break" | "continue"
           | "self" | "Self"
           | LOWER_NAME
           | UPPER_NAME
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
other converts to (see [Views](#views)). Functions cannot be compared. `!`
works on `Bool`, `~` on integers, and negation on signed integers and
floats.

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
    uses Panic unless self.add_is_defined(right)
}
```

- Each operation terminates, and uses `Panic unless` its `_is_defined`
  method holds: code without `Panic` proves it, and code with `Panic` panics
  where it fails, as with a built-in integer. For a fixed-width integer, an
  operation is defined where its result fits the type and, for `/` and `%`,
  where the divisor is not 0 and the operation is not `minimum / -1`. A
  float operation is defined everywhere.
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
  overflow is proven not to, panics in code that has `Panic` (see
  [Failure](#failure)), or is the standard library's checked, wrapping, or
  saturating method.
- `/` rounds toward zero, and `%` has the sign of its left operand.
- `>>` on a signed integer copies the sign bit, and on an unsigned integer
  shifts in zeros. A shift amount is any unsigned integer type, proven
  smaller than the bit width of the value.
- The traits `FixedWidthInteger`, `SignedInteger`, and `UnsignedInteger` are
  sealed: only the built-in integer types implement them. A method that every
  integer type has is declared in one of them.

### Floats

- The trait `FloatingPoint` is sealed: only `Float32` and `Float64`
  implement it. A method that both float types have is declared in it.
- Float arithmetic follows IEEE 754. NaN and infinity are values, so no
  float operation fails.
- Float results are the same on every platform. The operations IEEE 754
  defines exactly are never contracted or reordered.
- `==` treats every NaN as equal to every other NaN, and otherwise follows
  IEEE 754, so `-0.0 == 0.0`. In ordering, NaN comes after every number.

## Failure

Only code that has `Panic` panics. It panics where it calls `Panic.crash`,
directly or through a callee such as `expect`, and where an integer
operation fails. Running out of memory and overflowing the stack are the
exceptions.

No allocation holds more than `core.maximum_length` elements, which is
`Int64.maximum`, so the `length` of a `String` ensures
`result <= core.maximum_length`. A length plus one, or the sum of two
lengths, therefore cannot overflow `UInt64`.

Every operation that can fail is a proof obligation, in every function and
every test: integer overflow, division by zero, indexing or slicing out of
bounds, a shift that is too large, and `unreachable`. Where the compiler
cannot prove one safe, the code is an error, and one of these makes it
compile:

1. Establish the fact locally, as with an `if`.
2. Require it with `requires`.
3. Call a method that returns an `Option` or a `Result`, such as
   `checked_add` or `get`.
4. For an integer operation, declare `uses Panic`.

**In code that has `Panic`, an integer operation that fails panics.** An
overflow, a division by zero, and a shift that is too large are then not
proof obligations. Indexing, slicing, and `unreachable` are proven there
too.

- Code that uses `Panic unless C` proves its integer operations where `C`
  holds.
- A lambda has `Panic` where its type uses it. A lambda whose capabilities
  are inferred, such as one passed to `map`, takes `Panic` for an integer
  operation where the code it is written in has `Panic`.
- `unreachable` admits only the first way.
- `left.checked_add(right).expect("the total fits Int64")` panics with the
  message given to `expect`. A failing operation panics with a message that
  names the failure, such as `arithmetic overflow`.

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
  parameters without their defaults: a call fills a default in from the
  capability's method, so an implementation receives every argument.
- `provide implementation, ... { body }` runs the body with the given
  implementations, passed as arguments are: a place is written with `mut`
  when its methods mutate it, and it holds the mutations afterward, on
  every path out of the body, a `return` or a `break` among them.
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

`Panic`, `RunForever`, and `System` are *built-in* capabilities: the
compiler gives each its meaning, and no `impl` implements any of them. The
runtime holds a *real implementation* of every other standard capability.
A capability that a package declares has no real implementation. An
intrinsic that reaches the operating system uses `System`, which no
package but the standard library can name. The runtime grants `System`
only to the real implementations.

### Handles

A handle is a value that stands for something the operating system holds,
such as an open file. It is released when its owner is done with it, on
every path, and releasing it runs no Truss code and never fails.

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
fn total_score(players: List[Player]) -> Int64
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
  control goes. So after an early exit, a place that another branch or
  iteration mutates holds a value of its type, and which of its writes
  happened is not known.
- The code after the block does not run when a branch exits early, so a
  branch that moves a value out of a place reinitializes it before it ends.
- **In a cancelled task, a standard capability call that would wait returns
  at once:** an `Err` of `SystemError.Cancelled` where it returns a
  `Result`, `None` where it returns an `Option`, and early where it returns
  nothing. `Tasks.cancelled()` tells whether the task is cancelled. A task
  blocked on the mutex of a `mut` implementation waits until it acquires it.
- A function that waits for another task has no `time` clause, and the end
  of a `concurrent` block or a `concurrent for` waits for its tasks.

The iterations of a `parallel for` and of a `concurrent for` run at the same
time, and a `concurrent for` iteration keeps running after the loop
advances.

- An iteration that reads its element is lent it for the whole loop, from
  any collection.
- **Only a `List` or an `Array` lends its elements `mut` to such a
  loop.** Its elements at different positions are different places.
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
method with a parameter that can hold a function that uses a capability
other than `Panic` and `RunForever`. An implementation provided without
`mut` has no mutex.

## Strings

- A string literal is a `String` constant without a name. Reading it, taking
  a view of it, and binding it with `let` cost nothing. Where an owned
  `String` is needed, as in a `var`, an `own` argument, or a returned value,
  the literal is copied, and a copy of a non-empty literal counts as one
  allocation. The literal text of a [tagged template](#tagged-templates) is
  a constant without a name by the same rules.
- A string literal without `${...}` where a `view String` is expected is a
  view of the constant's bytes, which outlives every function.
- There is no concatenation operator: `+` on strings is an error, and
  adjacent literals do not join.
- A value in `${...}` has a type that implements `Display`.

### Tagged templates

```truss
let query = SqlQuery"select name from users where id = ${user_id}"
let pattern = Regex"[a-z]+@${domain}"
```

- The tag, a type name without type arguments, is the type of the result. A
  tag of another module is written after its module, as in
  `sql.SqlQuery"select 1"`.
- A type is a tag by implementing the prelude trait `FromTemplate`. Its
  associated type `Interpolation` is the type each interpolated value is
  converted to. Its method `from_template` takes a
  `Template[Interpolation]`. The template's `literals` hold the literal text
  as `text.Literal` values, which only the compiler makes, and its
  `interpolations` hold the converted values.
- An interpolated value of a type other than `Interpolation` is converted
  by `Interpolation`'s impl of `From` for that type. A place of a `List` or
  a `String` that is not passed `own` is converted from a view of it where
  `Interpolation` implements `From` for the view, as `Regex"^${name}"`
  converts from `view String`: the place is read, not moved.
- A tag's `is_valid_template` states the rules for valid literal text, and
  `from_template` requires it.
- The literal text of a template is a `List[text.Literal]` constant without
  a name, as a string literal is a `String` constant without a name.
- A tagged template is the call of its tag's `from_template`, after
  `assert Tag.is_valid_template(literals) by evaluation` on that constant
  (see [Statements and blocks](#statements-and-blocks)). `Regex"[a-z"` is
  therefore an error when the code is checked, and so is a check that
  reaches `todo`.
- Where the tag mentions a type parameter of the code around it, nothing is
  evaluated, and the `requires` of `from_template` is proven as any other
  is.

```truss
impl FromTemplate for Regex {
  type Interpolation = RegexInterpolation

  fn is_valid_template(literals: List[text.Literal]) -> Bool {
    todo
  }

  fn from_template(template: Template[RegexInterpolation]) -> Regex {
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
                | "capability" UPPER_NAME "=" capability_use { "," capability_use } ;
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
  their names, modes, and types, and no default; and the result. `Self`, the
  trait's arguments, and the associated types are as the `impl` gives them,
  and a function type has the trait's `uses` and `cost` clauses. The
  method's generic parameters may have other names, its capability
  parameters have the trait's names (see
  [Capability parameters](#capability-parameters)), and a type parameter's
  bounds and a function type's `cost` clauses may come in another order.
  The body of the method and every call of it are checked against this one
  signature. The method states of its own only its `uses`, which stays
  within the trait's, and the contract clauses that the next two rules allow.
- **An `impl`'s method may promise more than its trait.** Its contract is
  the trait method's, with the method's own `ensures` and `cost` clauses
  added, and its own `requires`, if it has any, in place of the trait's.
  The trait's `requires` must imply the method's, and the condition after
  the trait's `Panic unless` must imply the method's. A call known to reach
  that `impl` is proven against the `impl`'s contract, and a call through a
  bound against the trait's.
- An `impl`'s method without a `time` clause has its trait's.
- **Required traits:** a type implements the traits a trait requires before
  it implements the trait, and a bound includes them. A trait can add an
  overload of a required trait's method in another mode. Traits cannot
  require each other in a cycle.
- **A trait can restate a method of a trait it requires, to promise more.**
  The restated method has the required trait's signature, adds `ensures`
  and `cost` clauses, and has no body. It is the same method: an `impl` of
  the trait does not write it, and each `impl` proves the added clauses
  from the contract of the method in its type's `impl` of the required
  trait. A call through a bound of the trait, and a call on a type that
  implements it, has the added clauses. `FiniteCursor` restates
  `Cursor.next` (see [Cursors](#cursors)).
- **A method with a body** is provided to every implementation. An `impl` can
  override it with a method that keeps the trait's contract for it, as it
  keeps the contract of every other method.
- **A method with a default has one declaration.** In a trait, only a method
  with a body declares a default. No `impl` overrides that method and no
  trait restates it, so a call on a known type or through a bound reads the
  default from the trait. A method without a body has no
  default: each `impl` writes it, and a call on a known type names the
  `impl`'s method, which would not show the default.

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
  `pair.count()` is an error, and is written `Bag[Int64].count(pair)`.

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

```truss
trait IntoCursor {
  type Cursor: Cursor
  fn cursor(own self) -> Self.Cursor
}
```

- A trait's associated type is chosen by each `impl`, with
  `type Key = ...`, which appears only in an `impl`.
- **A bound on an associated type holds for every `impl`.** The type that an
  `impl` chooses for `type Cursor: Cursor` implements `Cursor`, so code
  bounded by `Source: IntoCursor` calls `Cursor`'s methods on
  `Source.Cursor`.

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
- A capability in a set takes `unless`, as in `uses`. A cursor whose `next`
  pulls its source until a value matches defines
  `capability Uses = Source.Uses, RunForever unless Source: FiniteCursor`,
  and a call of its `next` uses `RunForever` only where the source is not a
  `FiniteCursor`.
- A bound cannot constrain a set, and `calls(...)` cannot count one.

### Equality

A type's equality is *structural* when `==` compares contents: two values are
equal exactly when they are the same variant and their fields are equal. The
built-in integers, `Bool`, `Character`, `Unit`, and `String`, whose `==`
compares text, have it, and so does a type that derives `Equal` when all its
fields do. A hand-written `Equal`, float equality, and an opaque type's
equality outside its package are not structural.

A type's equality is *identity* when equal values are `identical`, so
`a == b` implies `f(a) == f(b)` for every function `f`. The built-in
integers, `Bool`, `Character`, `Unit`, and the types of specifications have
it, and so does a type that derives `Equal` when the equality of all its
fields is identity. `String`'s equality is structural but not identity: two
equal strings can differ in `capacity()`.

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
| `serialization.Serialize` | A record as its fields by name, in declaration order. A variant with no fields as its name, and a variant with fields as a record of them under its name |
| `serialization.Deserialize` | The same form, read back. A missing field takes its default if it has one, and a missing field of type `Option` is `None`. A value that breaks an `invariant` clause of its type is an error |
| `Copyable`, `Plain` | Nothing: an opaque type declares that it copies (see [Copying](#copying)) |

- Every field has the trait, and a derived trait's required traits are
  derived too: `Ordered` and `Hash` need a derived `Equal`.
- A generic type has a derived trait only where its parameters do.
- A derived implementation satisfies the trait's laws; a hand-written one
  proves them.
- A derived `Equal`, `Ordered`, or `Hash` states a cost on each resource:
  the sum of the method's cost for the type of every field of every
  variant, plus 1 for `time`. For
  `type Score(points: Int64, rank: UInt8)`, the derived `compare` states
  `cost time O(1 + time(Int64.compare) + time(UInt8.compare))` and
  `cost allocations <= allocations(Int64.compare) + allocations(UInt8.compare)`.
- A derived `Default` takes no arguments, so its cost is the cost of its
  body: the `default()` of each field without a written default, and the
  evaluation of each written default.
- `serialization.Deserialize` is derived only for a type whose `invariant`
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
  a trait's method of that name and mode is found instead.
- A view has the methods of the type that it views that take `self`
  read-only. An `Array` has the methods of the `List` of its elements too,
  in each mode of `self` that its own methods and its traits' methods do
  not take: the receiver is the range of all its elements, so
  `values.contains(1)` is `List.contains(values[..], item: 1)`. In the rules
  below, the methods an `Array` has from `List` count as its own.
- A method written in full, as in `String.trim(name)`, takes `self` as its
  first parameter, so the receiver is its first argument and has no label.
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

## Tests

```ebnf
test = "test" plain_string [ "uses" capability_list ] block ;
```

```truss
test "config loads with defaults" uses RunForever {
  var disk = files.MemoryFiles.new().with_text(Path.new("app.toml"), contents: "")
  let config = provide mut disk, log.DiscardLog() {
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
- A failed `assert` ends the test as failed, and the rest of the test can
  rely on the asserted fact.
- Tests run only when no proof in their packages fails. A proof that holds
  a `todo` does not fail.
- A test build checks every primitive operation that could fail when it
  runs, and a failed check fails the test. A `requires` is not run.
- A panic fails only its test. A test that reaches a `todo` is incomplete.

## Proofs

```ebnf
theorem   = "theorem" LOWER_NAME [ generics ] parameters { clause } block ;
law_proof = "proof" path_type "." LOWER_NAME "for" type_head block ;
```

Every promise is proven before a program is built: contracts, invariants,
laws, loop invariants, and every operation that could fail.

```truss
theorem reverse_twice[Element](items: Sequence[Element])
  ensures identical(items.reversed().reversed(), items)
{
  assert forall i in 0..items.length() =>
    identical(items.reversed().reversed()[i], items[i])
}

proof Ordered.transitive for Box[Item: Ordered] {
  box_order_is_transitive(first, second: second, third: third)
}
```

```truss
theorem sorted_between(items: List[Int64], first: UInt64, second: UInt64)
  requires items.is_sorted()
  requires first <= second
  requires second < items.length()
  ensures items[first] <= items[second]
  decreases second - first
{
  if first < second {
    sorted_between(items, first: first, second: second - 1)
  }
}

theorem sorted_up_to(items: List[Int64], last: UInt64)
  requires items.is_sorted()
  requires last < items.length()
  ensures forall i in 0..last + 1 => items[i] <= items[last]
{
  assert forall i in 0..last + 1 => {
    sorted_between(items, first: i, second: last)
    items[i] <= items[last]
  }
}
```

- A theorem's `requires` are its assumptions, its `ensures` its conclusions,
  and its body the proof, using calls, `let`, `match`, `if`, and `assert`. An
  empty body asks the prover to prove it alone.
- Calling a theorem makes its `ensures` available. A theorem that calls
  itself on smaller input is a proof by induction, as `sorted_between` is.
- **A call in a quantifier's body is made for each value of the binder.**
  The prover proves its `requires` for every value, and its `ensures` holds
  for that value within the body. So a quantifier's body that calls a theorem
  and then states a fact proves the fact for every value. This is universal
  introduction, as in `sorted_up_to`.
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
- An `impl`'s laws, and the clauses that its trait adds to a required
  trait's method, are proven from the contracts of its type's methods.
- A derived `Ordered` states its comparison in its `ensures`.
- A clause applies only where every name that it mentions is visible.
- A function with a `requires` is defined only where it holds.

### Circular proofs

A proof assumes the contract of each function that its definition calls and
the invariant of each value that the definition uses. A proof that assumes a
fact whose own proof assumes it back proves nothing: a false postcondition
can be proven that way.

- The proof of a definition depends on these definitions, and on the
  definitions that their proofs depend on:

  | The definition has | Its proof depends on |
  |---|---|
  | A call or a read of a constant, in its body or in its contract | The callee or the constant, and the code that the call supplies |
  | A contract that its trait declares, for a method of an `impl` | Each function that the trait's contract calls, as the `impl` resolves the call |
  | A value of a type of its own package: a parameter, a result, a local, or, for a type, a field | The type |
  | A value of a generic type | Each function that the invariant or the `potential` of the type calls at those type arguments, and the same for the types of its fields. Where a field's type is a generic type that holds the field, with other type arguments, every method of the `impl`s that those type arguments supply to its bounds |
  | An invariant or a `potential`, for a type | Each function that the clause calls and each constant it reads |

- A cycle of these dependencies is an error unless calls alone form it. A
  cycle of calls is a recursion, which a measure shows to end (see
  [Termination](#termination)). The error is reported where the cycle leaves
  a specification:

  | Where the cycle closes | Reported at |
  |---|---|
  | An invariant or a `potential` calls into the cycle | The call in the clause |
  | A contract calls into the cycle, and no invariant does | The call in the contract |
  | A contract that a method takes from its trait calls into the cycle, and the method does not restate that call | The method |
  | The invariant of a generic type, or of the type of one of its fields, calls into the cycle at one instantiation only | The value of that type |

  `fn clamp(n: UInt64) -> UInt64 requires clamp(n) >= 0` is an error at the
  call in its `requires`. A recursive function's `ensures` may call the
  function, since its body's calls already form that cycle.

- A fact that relates two functions is not a clause of one where the
  contract of the other calls back. `Set.count` cannot ensure that every
  member is `self.element(position)` for some position, because
  `Set.element` requires `position < self.count()`. A theorem states the
  fact, as `set.every_member_is_an_element` does, and a proof that needs it
  calls the theorem.

### Writing specifications

A *specification* is a `requires`, `ensures`, `decreases`, or `cost` clause,
an invariant, a law, or a proof.

- A call in a specification uses no capability, so it terminates. A
  capability parameter in the callee's `uses` stands for nothing at that
  call: `values.map(fn(value) { value + 1 })` is
  such a call, although `map` passes a capability parameter on.
- Every specification is well defined: each call meets its callee's
  `requires` and the condition of a callee's `Panic unless`, and each index
  is in bounds. `&&`, `||`, `==>`, and `if` read
  left to right, so the right side can rely on the left.
- `==` is the type's `Equal`, and `identical(a, b)` is identity, for any type.
- A specification is read as a formula, not run: it holds no `return`,
  `break`, `continue`, `?`, `var`, loop, or `unreachable`.

| Form | Meaning |
|---|---|
| `forall index in 0..count => items[index] >= 0` | True for every value in a range or a collection |
| `forall value: Int64 => value + 0 == value` | True for every value of a type |
| `exists item in items => item == target` | True for at least one value |
| `a ==> b` | When `a` holds, so does `b` |
| `old(self.items)` | A value as it was when the function was called |
| `transform.ensures(value, output)` | The function passed for `transform` may return `output` for `value` |

- A quantifier over a range or a collection is also an expression in code,
  which runs as a loop that stops when the answer is known. Its body may rely
  on the bound name being in its range, and uses no capabilities.
- A quantifier over a collection ranges over its elements at the positions
  below its `count()`, in code and in specifications alike: the element
  places of a `List` or an `Array`, and the values that any
  other collection's `element` lends. A pattern that does not match a value
  leaves that value out.
- A quantifier over a type appears only in specifications and in functions
  for specifications only.
- A quantifier's body runs to the end of the expression.
- Integer arithmetic in a specification is exact. It is done on `Integer`, a
  prelude type that exists only in specifications, of which every built-in
  integer type is a subset, so comparisons can mix integer types. A range
  whose bounds have two integer types, as in `middle + 1..items.length()`,
  is a range of `Integer`. An `Integer` can stand where a built-in integer
  is expected, and the prover shows that it fits.
- A specification never decides a type that code computes with. An integer
  literal or local of the code whose type is undecided is an `Integer` in a
  specification, so `invariant small <= limit` with a `UInt8` `small` leaves
  the type of `limit` to the code. A use that would decide the type of a
  float literal of the code, or join or bind a type that the code left open,
  is an error. Declaring the local with a type, as in
  `let ratio: Float32 = 0.75`, removes the error.
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

The prelude types `Sequence`, `FiniteSet`, and `FiniteMap` exist
only in specifications, and their equality is identity. A type gives its
value in their terms with the prelude trait `Model`, whose `model()` can be
called only in specifications:

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
- A `todo` in a specification is a hole: on the paths through it, the
  specification is neither proven nor assumed.
- The laws of an `impl` that holds a `todo` are not proven, so the `todo` is
  a hole in each proof that assumes them.
- A release build refuses a program whose `main` can reach a `todo`. It
  reaches the code that `main` calls, the proofs of that code, the
  definitions whose contracts those proofs read, and the `impl`s whose
  methods that code calls or passes to generic code. In a development
  build, a `todo` that runs stops the program and reports its position.
- A constant whose evaluation reaches a `todo` has no value. A proof knows
  the constant by the contracts of the calls in its value, a test that can
  reach the constant is incomplete, and a program that can reach it is not
  built.
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
use standard.json

let settings = json.parse(text)?
```

- `use` imports a module, never names. Every name that is not local, not a
  definition of the module, and not from the prelude is written with its
  module.
- A `use` belongs to its file. Each file of a module imports the modules it
  names.
- There are no import aliases. A full path works without a `use`, and
  importing two modules with the same last name is an error.
- An unused `use` is an error. A `use` is used when a path in the file
  begins with its last name where no local has that name.

### Module paths

Each directory of a package that holds a `.truss` file is a module, whose
path is the package's name, then the directory's names. The files of
`forecast/` in the `weather` package, such as `forecast/hourly.truss` and
`forecast/daily.truss`, are the module `weather.forecast`, and the files
beside the package's manifest are its root module, `weather`.

- The files of a module share one namespace: each names the others'
  definitions without a module, private ones included. Two files of a
  module cannot define one name.
- A module's subdirectory is a module of its own: `forecast/hourly/` is
  `weather.forecast.hourly`, which names `weather.forecast` by its full path
  like any other module.
- Every path starts with a package name, including inside the package.
- A path holds no version.
- The modules of a package may use each other in a cycle.

### The prelude

The prelude is in scope in every file, and all its names are
`UpperCamelCase`:

- the built-in types, `Option` and `Result`, and `List`, `Map`, and `Set`
- the core traits, such as `Equal`, `Ordered`, `From`, `TryFrom`, `Default`,
  `Copyable`, `Plain`, `Storable`, `Index`, `IndexMut`, `IndexAssign`,
  `Iterable`, `IterableMut`, `Cursor`, `FiniteCursor`, `IntoCursor`,
  `FromTemplate`, `FromElements`, `FromEntries`, `Model`, and the arithmetic
  traits
- `Integer`, `Sequence`, `FiniteSet`, and `FiniteMap`
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
  has its own visibility.
- A use that reaches a member through its type finds it only where it is
  visible: `Shape.unit`, `shape.area()`, `Shape.area(shape)`, a constant in
  a pattern, and the `count`, `element`, and `cursor` of a `for` loop or a
  quantifier. A member that the use cannot see is skipped, as if it did not
  exist. A use that finds no member except one it cannot see is an error
  that names that member, whether the member is defined on its own or
  written in a trait that the type implements.
- `opaque` appears only before `public type`. Outside its package, an opaque
  type's fields cannot be read, built, updated, or matched on. Visibility is
  set for a type as a whole.
- A public signature cannot mention a private or `internal` type, and
  neither can a public type's fields unless the type is opaque.
- The `requires` and `cost` of a public function, of a method of a public
  trait or capability, and of a method of an `impl` that other packages can
  use call no private or `internal` function and name no such constant. An
  `ensures` may name any function the definition can.
- An `internal` function, method, or constant that no definition of its
  package uses is an error, and a private one is a warning. A method or
  constant written in a trait, a capability, or an `impl` is not checked.
  A use counts when the user is public, is a test, an `impl`, or another
  definition the rule does not check, or is itself used, so definitions
  that use only each other are reported together. The `main` of a
  package's root module is exempt, and so is a definition the compiler
  calls by name.
