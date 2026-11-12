# Truss Language Specification

This document defines the Truss language: its grammar and the rules that
decide a program's semantics and whether it compiles. [DESIGN.md](DESIGN.md)
gives the reasons for these rules, and [PACKAGES.md](PACKAGES.md) defines
manifests, lock files, and the registry. The documents of stage0's stages,
which [IMPLEMENTATION.md](IMPLEMENTATION.md) lists, say how much of the
language stage0 builds.

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
comma. `lines(item)` is items separated by line breaks, as inside braces:

```ebnf
list(item)  = [ item { "," item } [ "," ] ] ;
lines(item) = [ item { NEWLINE item } ] ;
```

[`grammar/truss.mly`](grammar/truss.mly) is the whole grammar written for
the Menhir parser generator. A test checks that it accepts every example in
the repository's documents, and that the parser agrees with it (see
[PARSER.md](PARSER.md#recursive-descent-with-no-backtracking)).

Some examples show a signature without a body. In a program, every function
has a body, except a method declared in a trait or a capability. A function
that is not written yet has the body `{ todo }`.

## Source files

- A source file is UTF-8, with no other encoding.
- A byte order mark may appear only as the first character, and is ignored.
- Tab and space are whitespace.
- A carriage return followed by a line feed is one line break. A carriage
  return on its own is a compile error.
- Each language version names one Unicode version, and every rule here that
  uses a Unicode property follows that version. A string can still hold a
  character from a later Unicode version.
- `truss fmt` removes the byte order mark, indents with spaces, and writes
  line feeds only.

These characters are a compile error anywhere in a file, including inside
string literals. They can make code display differently from how it
compiles:

- the bidirectional controls: U+061C, U+200E, U+200F, U+202A to U+202E, and
  U+2066 to U+2069
- the control characters U+0000 to U+001F, U+007F, and U+0080 to U+009F,
  except tab, line feed, and a carriage return before a line feed
- every other character with the Unicode property
  `Default_Ignorable_Code_Point`, such as zero-width space, word joiner, soft
  hyphen, and the tag characters U+E0000 to U+E007F, except the zero-width
  non-joiner (U+200C), the zero-width joiner (U+200D), and the variation
  selectors

An ordinary string writes a forbidden character as an escape, such as
`\u{2068}`. A raw string cannot contain one.

## Lexical elements

```ebnf
token = UPPER_NAME | LOWER_NAME | "_" | keyword
      | INTEGER | FLOAT | STRING | TAGGED_STRING
      | punctuation | NEWLINE ;
```

Whitespace and line feeds separate tokens. A line feed becomes a `NEWLINE`
token only as [Line breaks](#line-breaks) says. Truss has no comment syntax.

### Names

```ebnf
letter   = "a" ... "z" | "A" ... "Z" ;
raw_name = letter { letter | digit | "_" } ;
```

A `raw_name` that is a keyword is that keyword. Otherwise:

- It is an `UPPER_NAME` if it starts with an uppercase letter, and must not
  contain `_`.
- Otherwise it is a `LOWER_NAME`. It contains no uppercase letter, does not
  end with `_`, and does not contain `__`.
- `_` on its own is the token `"_"`, the wildcard pattern.

Names are ASCII. A letter outside ASCII where a name is written, such as `é`
in `café`, is an error. The lexer reads the whole word, as Unicode's
`XID_Start` and `XID_Continue` define one, as a single name and reports it
once. Text in any language goes in strings, including test names, as in
`test "café counts accents"`.

Types, constructors, traits, and capabilities are `UpperCamelCase`. Values,
constants, functions, fields, modules, and files are `lower_snake_case`. The
parser relies on this: in a pattern, `Circle` is a constructor and `radius`
binds a new variable, unless a constant named `radius` is in scope.

By convention, names are whole words: `items`, not `xs`; `length`, not
`len`; `[Element]` and `[Key, Value]`, not `[T]` and `[K, V]`. Single letters
are kept for loop indices such as `i` and `j`. The compiler does not enforce
this.

### Keywords

Reserved everywhere:

```text
any assert break capability concurrent continue cost decreases derives echo else
ensures exists false fn for forall if impl in indirect internal invariant is law
lends let match mut opaque own parallel proof provide public requires return self
Self test theorem todo trait transparent true type unreachable use uses var while
with yield yields
```

Reserved for later use, and an error if written:

```text
as async await const defer extern loop macro static unsafe where
```

The lexer has no contextual keywords. The words below are names to it,
`LOWER_NAME`s except `O`, which is an `UPPER_NAME`. The parser recognizes
them by their spelling in the positions the grammar shows, and
name resolution gives the rest their meaning:

```text
amortized time allocations allocated_bytes calls O finite potential
log power result old
```

| Words | Where they have a meaning of their own |
|---|---|
| `amortized`, `time`, `allocations`, `allocated_bytes`, `calls`, `O`, `finite`, `potential` | The fixed positions of a `cost` clause: `cost [amortized] resource bound` and `cost potential expression` |
| `time(...)`, `calls(...)` | Called inside a `cost` bound, where they are the cost functions |
| `log(...)`, `power(...)` | Called inside a `cost` bound or another specification, where they are functions on exact integers |
| `result` | Inside `ensures` and `cost`, where it names the return value |
| `old` | Inside specifications, where `old(e)` is the value of `e` when the function was called |
| `identical` | Inside specifications: `identical(a, b)`, whether two values of one type are the same value |
| `yielded`, `finished` | Inside the `ensures` of a lending or yielding method, and `yielded` in the clauses of a `for` loop |

A parameter cannot be named `result`, and no function can be named `old` or
`identical`. Other names are unaffected: in
`fn wait(time: Duration) cost time O(time.seconds())`, the second `time` is
the resource and the third is the parameter. A function named `log` or
`power` can be defined and called anywhere except inside a `cost` bound.

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

| Literal | Meaning |
|---|---|
| `42`, `1_000_000` | Decimal |
| `0xFF`, `0xdead_beef` | Hexadecimal |
| `0b1010_0001` | Binary |
| `0o755` | Octal |
| `0.5`, `6.02e23`, `1.0e-9` | Floating point |

- A `FLOAT` needs a digit right after its `.`, so `1..2` lexes as `1`, `..`,
  `2`, and `1.max` as `1`, `.`, `max`.
- The whole-number part of a decimal literal has no leading zero, so `0755`
  and `007` are errors. The digits after the `.` and in an exponent may start
  with zeros: `0.05`, `1.0e-09`.
- A number literal is never directly followed by a name character: `3u8` is
  an error. Literals have no type suffixes.
- `-` is never part of a literal.

A literal takes its type from its context, as in `let small: UInt8 = 3`.
When nothing decides it, an integer literal is an `Int64` and a float literal
is a `Float64`, so `var best = 0` makes an `Int64`.

- A literal operand of an arithmetic operator, a comparison, or a range takes
  the type of the other operand when it can be that type. In `count + 1` with
  a `UInt8` count, the `1` is a `UInt8`. In `duration * 2`, `Duration` is not
  an integer type, so the `2` is an `Int64`. An expression made only of
  literals waits for the same decision, so `count + (60 * 60)` works.
- A literal shift amount, as in `flags << 3`, is a `USize`.
- An integer literal is never a float: `let ratio: Float64 = 1` is an error.
- A literal that does not fit its type is a compile error. A negated literal
  is checked after the negation, so `-128` fits an `Int8`.
- A literal of `USize` or `ISize` must fit in 32 bits, except in the standard
  library.
- A literal whose type is a type parameter bounded by an integer trait must
  fit every type that implements the trait: -128 to 127 under
  `SignedInteger`, 0 to 255 under `UnsignedInteger`, and 0 to 127 under
  `FixedWidthInteger`.

### String literals

The lexer returns a string literal as one `STRING` token, with each
interpolation already split into the tokens of its expression.

```ebnf
STRING        = ordinary_string | raw_string ;
TAGGED_STRING = UPPER_NAME string_start ;
```

A `TAGGED_STRING` is an `UPPER_NAME` with no whitespace between it and the
string, as in `Regex"[a-z]+"`. A module path before the tag, as in
`database::SqlQuery"..."`, is ordinary tokens: `database`, `::`, then the
`TAGGED_STRING`. [Tagged templates](#tagged-templates) gives its meaning.

**Ordinary strings** begin and end with `"` on the same line:

```ebnf
ordinary_string = '"' { ordinary_char | escape | interpolation } '"' ;
ordinary_char   = ? any character except '"', '\', and a line feed ? ;
escape          = '\n' | '\t' | '\r' | '\0' | '\\' | '\"' | '\${'
                | '\u{' hex_digit [ hex_digit ] [ hex_digit ] [ hex_digit ]
                        [ hex_digit ] [ hex_digit ] '}' ;
```

| Escape | Meaning |
|---|---|
| `\n`, `\t`, `\r` | Line feed, tab, carriage return |
| `\0` | The NUL character |
| `\\`, `\"` | A backslash, a double quote |
| `\${` | The text `${` |
| `\u{1F600}` | The Unicode scalar value with that hexadecimal code: at most `10FFFF`, and not a surrogate |

Any other backslash sequence is a compile error.

**Raw strings** have no escapes of any kind:

```ebnf
raw_string = { "$" } quotes raw_body quotes ;
quotes     = '"""' { '"' } ;
```

```truss
let phone = Regex"""\d{3}-\d{4}"""

let query = SqlQuery"""
  select name, email
  from users
  where id = ${user_id}
    and active = true
  """
```

- The opening and closing delimiters have the same number of quotes, at
  least three. A run of more quotes than the delimiter is an error, so text
  that contains `"""` uses a longer delimiter.
- If the opening delimiter is followed by a line feed, the string is
  multi-line. Spaces and tabs between the delimiter and the line feed are
  ignored, and `truss fmt` removes them. The closing delimiter is on a line
  of its own, preceded only by whitespace, and that whitespace is the
  indentation. Every other line starts with exactly that whitespace, which is
  removed, so `query` starts with `select` and the `and` line keeps its two
  extra spaces. A line that holds only whitespace and does not start with the
  indentation is an empty line. The line feeds after the opening delimiter
  and before the closing one are not part of the string, so a string that
  ends with a line break has an empty line before the closing delimiter.
- Otherwise the string is on one line, and its text cannot start or end with
  `"`.
- All other whitespace is kept exactly, including at the ends of lines.
- A line break in a raw string is `\n`, whatever line endings the source
  file uses.

**Interpolation.** In an ordinary string, and in a raw string opened with no
`$`, an interpolation starts at `${`. In a raw string opened with *n* `$`
characters, it starts at *n* `$` characters followed by `{`, and any `$`
characters before those are text:

```ebnf
interpolation = "${" expression "}" ;
```

```truss
let fixture = """
  { "name": "${name}", "tags": [] }
  """

let script = Shell$$"""
  echo "${HOME}/$${folder}"
  """
```

- A single `{`, `}`, or `$` is text. In `script`, `${HOME}` is text and
  `folder` is interpolated. In `"""Total: $${price}"""`, the first `$` is
  text.
- The lexer counts `{` and `}` inside an interpolation, and lexes string
  literals inside it recursively, so `"Players: ${names.join(", ")}"` is one
  string.
- An interpolation cannot contain a line break, and cannot be empty.

### Punctuation

```text
(  )  [  ]  {  }  ,  :  ::  .  ..  ..=  ->  =>  ?  |
=  +=  -=  *=  /=  %=  &=  |=  ^=  <<=  >>=
+  -  *  /  %  ==  !=  <  <=  >  >=  &&  ||  ==>  !  &  ^  ~  <<  >>
```

The lexer takes the longest match.

### Rejected sequences

These sequences are compile errors rather than tokens:

```text
//  /*  #  ;  '  `  @  ++  --  ===  !==
```

`--` is rejected even where it could be read as two negations: `--x` is an
error, and `-(-x)` negates twice. `//` is never two divisions.

### Line breaks

A line feed becomes a `NEWLINE` token exactly when the token before it can
end a statement and the token after it can begin one, outside `(` and `[`.
The lexer keeps a stack of open brackets, `(`, `[`, and `{`. An interpolation
is lexed on its own and cannot contain a line feed, so it needs no entry.

1. While the innermost open bracket is `(` or `[`, line feeds are skipped.
   Inside a `{`, they count again, so a block inside a call's arguments has
   statements as usual.
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
     `use`, `var`, `while`, `yield`.
3. Several line feeds in a row produce at most one `NEWLINE`.
4. At the end of the file, a `NEWLINE` follows the last token if it can end a
   statement.

Every other token continues the line before it: `.`, `,`, `:`, `::`, `)`,
`]`, `}`, `?`, `|`, `=>`, `->`, `=` and the compound assignments, the binary
operators other than `-`, `..`, `..=`, and the keywords `cost`, `decreases`,
`derives`, `else`, `ensures`, `in`, `indirect`, `invariant`, `is`, `lends`,
`opaque`, `requires`, `transparent`, `uses`, `with`, and `yields`. So no
`NEWLINE` comes before a closing `}`, and statements, `match` arms, and
members are separated by `NEWLINE`s, not ended by them. The parser skips a
`NEWLINE` immediately before a `{` that must open a body.

Both of these continue onto the next line:

```truss
let active_names = users
  .filter(fn(user) { user.is_active })
  .map(fn(user) { user.name.copy() })

let total = subtotal
  + shipping
  + tax
```

A line that starts with `-` begins a new statement, so the second line below
is a statement of its own, an unused value, which is a compile error:

```truss
let balance = deposits
  - withdrawals
```

`truss fmt` puts line breaks only where they continue the statement.

## Files and definitions

```ebnf
file        = { use NEWLINE } { definition NEWLINE } ;
use         = "use" module_path ;
module_path = LOWER_NAME { "::" LOWER_NAME } ;

definition = [ visibility ] ( function | type_definition | trait
                            | capability | constant | theorem )
           | impl | test | law_proof ;
visibility = "public" [ "opaque" | "transparent" ] | "internal" ;
```

Each file is a module, and each top-level definition is its own. There is no
block that groups definitions, and nothing about a definition depends on its
position in the file. [Modules and visibility](#modules-and-visibility)
defines `use` and the visibility keywords.

### Scope

- A name refers to one thing in a scope. No name can hide another: not a
  prelude name, not a definition in the same file, and not a variable of an
  enclosing scope. `let name = name.trim()` is an error; write
  `let trimmed_name = name.trim()`.
- Module names are a namespace of their own, because a module is only ever
  written before `::`. A variable can be named `url` in a file that imports
  the `url` module.
- `::` reaches into a module, and `.` into a type or a value.

## Types

### Built-in types

| Type | Values |
|---|---|
| `Int8`, `Int16`, `Int32`, `Int64` | Signed integers |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | Unsigned integers |
| `USize` | Sizes, lengths, and indices |
| `ISize` | Offsets and differences between positions |
| `Float32`, `Float64` | IEEE 754 binary floating point |
| `Bool` | `true` and `false` |
| `String` | UTF-8 text |
| `Character` | A Unicode scalar value: any code point except the surrogates |
| `Array[Element, count]` | Exactly `count` elements, stored in place. See [Arrays](#arrays). |
| `Unit` | The result of a function that returns nothing. Its only value is also written `Unit`. |
| `Never` | No values: the result of a function that never returns |

`USize` and `ISize` have 32 or 64 bits, and a package is verified for both
widths unless its manifest says `usize_bits = 64` (see
[PACKAGES.md](PACKAGES.md#package-manifest)).

Integer types never convert implicitly. `Int64.from(size)` converts where no
information can be lost, and `UInt32.try_from(size)` returns a `Result` where
it can.

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

A record has named fields. A sum type has one or more variants, and each
variant has fields of its own or none:

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

```truss
let origin = Point(x: 0.0, y: 0.0)
let unit_circle = Shape.Circle(center: origin, radius: 1.0)
let answer = Some(3)
let quiet = DiscardLog()
```

- A value is built the way a function is called (see
  [Calls and arguments](#calls-and-arguments)), and a field can have a
  default, as a parameter can:

  ```truss
  public type Request(
    method: Method,
    path: String,
    headers: Map[String, String] = [:],
  )

  let request = Request(method: Method.Get, path)
  ```

- In an expression, a variant is written under its type, as in
  `Shape.Circle`, and from another module also under the module, as in
  `geometry::Shape.Circle`. The prelude's variants `Some`, `None`, `Ok`, and
  `Err` are written bare everywhere.
- A `type_clause` after the last variant belongs to the whole type, never to
  that variant.
- The order of a record's fields has no meaning, except to a derived
  `Ordered`.
- `type Session = todo` declares a type that is not defined yet (see
  [Unfinished code](#unfinished-code)).
- `truss fmt` writes a sum type that fits on one line without the first `|`,
  as for `Bit`, and otherwise puts each variant on its own line starting with
  `|`, as for `Shape`.

Truss has no type aliases and no tuples.

### Recursive types

A type that contains itself marks the variant where it does so `indirect`:

```truss
type Expression =
  | Number(value: Int64)
  | indirect Sum(left: Expression, right: Expression)
  | Call(function: String, arguments: List[Expression])
```

- An `indirect` variant keeps its fields on the heap, in one allocation.
  Building one, as in `Expression.Sum(left, right)`, costs one allocation,
  which `cost` clauses count. Changing its fields in place, or moving them out
  with `own`, allocates nothing.
- Every cycle of types that contain each other passes through an `indirect`
  variant, unless it passes through a collection. `Call` needs no mark,
  because a `List` keeps its elements on the heap. A missing mark is a
  compile error, with a fix that adds it.
- A record cannot contain itself, even through an `Option`, because there is
  no variant to mark.
- A variant that is not recursive may be marked `indirect` too, so that one
  large variant does not make every value of the type large.
- In its own fields, at any depth, through type arguments and associated
  types, a type does not occur in the input of a function type that has a
  `time` clause: `type Knot(run: (fn(Knot) -> Bool cost time finite))` is a
  compile error. A function stored in a `Knot` could be called on that `Knot`
  and call itself through it, so its `time` clause would be proven for a
  function that does not terminate. A function type without a `time` clause
  may take the type, as in `type Button(label: String, on_click: fn(Button))`,
  and the output of a function type may be the type, as in
  `type Lazy(next: (fn() -> Lazy cost time finite))`.

### Single-field records

A record with one field gives a value a type of its own:

```truss
type UserId(number: UInt64)
type Meters(meters: Float64)

let user = UserId(42)
let distance = Meters(12.5)
let raw = user.number
```

- `UserId` is a different type from `UInt64` and from every other record.
- The record has none of the field's methods or operators: `distance +
  distance` does not compile unless `Meters` implements `Add[Meters]`.
- A record with one field has the same representation as the field.

### Grouping values

Values that belong together go in a record. The standard library has records
for the common cases:

```truss
public type Indexed[Element](index: USize, element: Element)
public type Entry[Key, Value](key: Key, value: Value)
public type Pair[First, Second](first: First, second: Second)
```

`enumerate` yields `Indexed` values, maps hold `Entry` values, and `zip`
yields `Pair` values. They are in `standard::core` and `standard::map`, not
in the prelude: a pattern never names them, and a signature writes
`core::Pair`. A function that returns several values declares a record for
its result:

```truss
type Extremes(lowest: Int64, highest: Int64)

fn extremes(scores: Slice[Int64]) -> Option[Extremes]
```

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

- `UPPER_NAME "." UPPER_NAME` names an associated type of a type parameter,
  such as `Items.Element` (see [Associated types](#associated-types)).
- An `INTEGER` or `LOWER_NAME` argument is the value of a `USize` generic
  parameter, as in `Array[UInt8, 32]` or `Array[Int64, count]`. It cannot be
  an expression, so `Array[Float64, rows * columns]` is not a type.
- `UPPER_NAME "=" type` constrains an associated type in a bound or after
  `any`, as in `Iterable[Element = Int64]`.
- `any` is defined in [Values of any type with a trait](#values-of-any-type-with-a-trait),
  and function types in [Function types](#function-types).

### Generic parameters

```ebnf
generics          = "[" generic_parameter { "," generic_parameter } [ "," ] "]" ;
generic_parameter = UPPER_NAME [ ":" bound ]
                  | LOWER_NAME ":" type
                  | "capability" UPPER_NAME ;
bound             = path_type { "+" path_type } ;
```

- A type parameter may have a bound, a trait or several joined by `+`, as in
  `[Key: Hash + Ordered]`.
- A `LOWER_NAME` parameter is a value, and its type is `USize`:
  `[Element, count: USize]`. Its value is known when the code is compiled.
- A `capability` parameter stands for a set of capabilities (see
  [Capability parameters](#capability-parameters)). Only a function, a
  method, or a theorem takes one.
- Generic code is compiled once for each set of type arguments. So a generic
  function cannot call itself, or a function in a cycle with it, with a type
  argument built from its own type parameters, such as `Option[Element]`, and
  a generic type cannot contain itself with other arguments. Type checking
  reports such an instantiation cycle.

### Invariants

A type can state an `invariant`, a condition that every value of the type
meets:

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

- `self` names the value. A record's fields can also be named directly, as in
  `start <= end`. A condition on one variant is a `match`, as for
  `Interval`, or a field whose own type has the invariant.
- `invariant` may repeat. Every condition holds, and each may rely on the
  ones before it.
- A function called in an invariant is pure and has a `time` clause.
- Invariants are proven when the code is compiled, never checked when it
  runs. An invariant holds wherever other code can see the value: when the
  value is built, directly or with `with`, when it is passed to a call or
  returned, and when the function that holds it ends. Between those points a
  function body may break it. A `with` is checked after all of its updates.
- A private method that takes `mut self` is a step of an update: the
  invariant of its `self` is neither assumed when it is called nor required
  when it returns. It states its precondition and postcondition with `requires`
  and `ensures`:

  ```truss
  fn SortedList[Element: Ordered].sift_into_place(mut self, index: USize)
    requires index < self.items.length()
    requires is_sorted(self.items[..index])
    ensures is_sorted(self.items)
  {
    todo
  }
  ```

When the compiler cannot prove an invariant where a value is built, a
constructor checks or establishes it:

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

## Values and ownership

Truss has mutable value semantics. Every variable holds its own value, and
no two names refer to one value that either can change. There are no
references that can be stored, no lifetimes, and no garbage collector.

- **A place** is a variable, `self`, or a constant, followed by any number of
  field accesses and indexes: `scores`, `config.servers`, `scores[0]`. A
  constant is a read-only place.
- **A temporary** is any other value, such as a literal or the result of a
  call. Nothing else can see it, so it is handed over as owned.
- **An owned value is needed** by a `var`, an `own` parameter, a record field,
  a collection element, and a return value. A place there is marked `own`,
  which moves it, or copied with `copy()`. `let name = config.name` needs
  neither, but `Person(name: config.name.copy())` needs the copy.
- **There is no mutable global state.** A top-level `let` is a constant, and
  `var` is allowed only inside functions.

### Copying

- **`Plain` types copy implicitly.** A type made only of fixed-size data with
  nothing on the heap, such as integers, floats, `Bool`, `Character`,
  `Array`s of those, and records and sum types built only from those, is
  `Plain`. Copying one is a copy of its bytes.
- **`Copyable` types have `copy()`,** which is how every other value is
  copied. An implicit copy never allocates.
- **The standard library's handles are not `Copyable`,** nor is a type that
  holds one: an open file, a connection, a listener, and a running process.
  A `List[Connection]` is a list without `copy()`.
- `Copyable` and `Plain` are prelude traits that the compiler implements and
  no `impl` can. `Plain` requires `Copyable`. The compiler derives them from a
  type's fields, except for an opaque type, which has them only when it
  declares them, as in
  `public opaque type Token(bytes: Array[UInt8, 16]) derives Plain`. The
  compiler checks such a declaration against the fields, and other packages
  rely only on the declaration.
- A generic type has them under the conditions its fields give:
  `List[Element]` is `Copyable` when `Element` is, and `Slice[Element]` is
  `Plain` for every `Element`, because the view it holds is. `any Trait` is
  `Copyable` only when `Trait` requires it.
- Generic code copies only where a bound allows it, as in
  `fn repeat[Element: Copyable](value: Element, count: USize)`.

### Views

A read-only name can refer to the original value instead of a copy. This
covers read-only parameters, a `let` bound to a place, the variable of a
`for x in items` loop, and slices:

```truss
let middle = items[1..4]
let total = middle.sum()
mut items.push(9)
```

While a view is in use, its original cannot be changed or moved. Here `push`
is allowed because `middle` is not used after it. The compiler checks this
within each function, from the function's body and the signatures it calls.

- **Being a view is a property of a type.** `Slice`, `StringSlice`, a cursor
  from a `self` method, and a lambda that reads local variables are views,
  and so is any type that holds one: in a field, a variant, an element, or a
  type argument. `Option[Slice[Int64]]` and the record that `split_at`
  returns are views. An `any Trait` is a view unless `Trait` requires
  `Storable`.
- **`Storable`** is the prelude trait of every type that is not a view. The
  compiler derives it from the fields of every type, opaque or not, and no
  type declares it. A type parameter has it only through a bound, as in
  `Channel[Message: Storable]`.
- **A view never outlives the function that made it.** A view can be bound,
  held in local records and collections, and passed as an argument. It
  cannot go where a `Storable` value is needed, such as an `own` parameter of
  function type, and putting it into a record or a list makes that record or
  list a view.
- **A function returns a view only of the places its parameters view, or of the
  parameters themselves,** never of its own locals, as `items[1..4]`,
  `split_at`, `split_first`, and `text.trim()` do. The caller treats the
  result as viewing everything that its read-only and view arguments view:
  after `let chosen = cached.unwrap_or(default: backup[..])`, `backup` cannot
  change while `chosen` is in use. Arguments that are `Plain` lend nothing.
- **A function keeps only the views it is given.** To keep a view of an
  argument in a `mut` parameter or in `mut self`, the function takes the
  argument as a `Slice`, a `StringSlice`, or a function. An argument that is
  only lent is never kept, so after `mut reader.read(mut buffer, limit: 64)`
  the reader does not view the buffer. A value cannot keep a view of its own
  part: `self.recent = self.items[0..1]` is an error.
- A `var` can hold a view, such as a cursor over a list, as long as the view
  never leaves the function.
- **`mut` access is never stored.** It has a name only as a `mut` parameter,
  a `mut` loop's variable, or a lambda's `mut` parameter, and lasts for that
  call, iteration, or `provide mut` block. Disjoint parts of one `List`,
  `Slice`, or `Array` can be passed `mut` side by side, as in
  `sort(mut items[..middle])` and `sort(mut items[middle..])`, when the
  prover shows that they do not overlap.
- A view of a temporary cannot be bound with `let`. Bind the value first:
  `let loaded = load()`, then `let first = loaded.first()`.
- **The one implicit conversion** is from a `List` passed to a `Slice`
  parameter, or a `String` passed to a `StringSlice` parameter, to a view of
  it, without copying.

## Constants

```ebnf
constant      = "let" constant_name ":" type "=" expression ;
constant_name = LOWER_NAME | type_head "." LOWER_NAME ;
```

A constant is a `let` at the top level. A constant of a type is written under
the type's name, as a method is:

```truss
public let pi: Float64 = 3.141592653589793

public let UInt8.maximum: UInt8 = 255
public let Instant.epoch: Instant = Instant(nanoseconds: 0)
public let seconds_per_day: Int64 = 24 * 60 * 60

fn circle_area(radius: Float64) -> Float64 {
  pi * radius * radius
}
```

- A constant's type is always written.
- `UInt8.maximum` has no parentheses, because it is a value, not a call.
- The value is a *constant expression*: literals, arithmetic on numbers,
  other constants, and records, variants, lists, maps, arrays, sets, and
  strings built from those. It calls no function. The compiler evaluates it,
  by running the standard library's compiled code where a `Map` or `Set` is
  built, with no random hash key.
- A constant lives in static memory. Reading it or taking a view of it costs
  nothing. An owned value from it is made with `.copy()`, as from any place:
  `var scores = starting_scores.copy()`. A constant is never marked `own` or
  `mut`.
- A constant can be used as a pattern (see [Patterns](#patterns)).

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

result        = "->" type | "yields" [ mode ] type | "lends" [ mode ] type ;
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

- Parameter and return types are always written. A function that returns
  nothing leaves out the return type, and its result is `Unit`; `truss fmt`
  removes a written `-> Unit`. A function that never returns has the return
  type `Never`.
- Inside a body, types are inferred one statement at a time: a variable's
  type comes from its own `let` or `var`, its annotation and its
  initializer, and never changes. When the statement alone cannot decide it,
  as in `var names = []`, the `let` has a type:
  `var names: List[String] = []`.
- `self` is only the first parameter, and only of a method (see
  [Methods](#methods)). `yields` and `lends` are defined in
  [Lending and yielding methods](#lending-and-yielding-methods).

### Calls and arguments

Parameter names are part of a function's interface. Arguments after the
first are named, by a label or by a variable of the same name:

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

```ebnf
argument = [ LOWER_NAME ":" ] expression ;
```

1. `label: value` passes `value` to the parameter named `label`.
2. A bare name that matches a parameter's name passes that variable to that
   parameter, wherever it appears. A mode keyword can come first, as in
   `mut destination`.
3. Any other first argument goes to the first parameter, as `original` and
   `area` do. Any other later argument is a compile error, with a fix that
   adds the label.
4. Arguments are written in the order of the parameters.

A parameter's default is a constant expression and cannot refer to other
parameters. An argument for a parameter with a default can be left out, as
`port` and `secure` are in `connect(host)`. The function fills in the
default, so changing it recompiles only the function. Where the default must
be owned, it is copied, which costs one counted allocation for a non-empty
`List`, `Map`, or `Set`.

Building a record or a variant follows the same rules, with two differences:

- Fields can be written in any order. Their values are evaluated in the order
  written.
- Only a record or variant with exactly one field takes a bare value, as in
  `Some(3)`, `UserId(42)`, and `ConfigError.Malformed(error)`. With more
  fields, every argument has a label or a matching name, as in
  `Point(x: 0.0, y: 0.0)` or `Summary(count, best, average)`.

A call through a function value, such as `visit(item)`, passes its arguments
by position, because function types have no parameter names. An
`UpperCamelCase` name before `(` is always a type or a variant being built,
never a function.

### Explicit type arguments

Type arguments are inferred. Where they cannot be, they are written in
square brackets after the function's name:

```truss
let value = parse[Int64](text)?
let names = items.map[String](describe)
let builder = List[String].with_capacity(64)
```

`parse[Int64]` is written as an index is, and name resolution decides which
it is (see [Constructs resolved after parsing](#constructs-resolved-after-parsing)).
A local variable cannot be generic, so a variable followed by `[...]` is an
index. For a method, the receiver's type decides. A diagnostic about `f[X]`
says which reading applied.

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
| `uses Capability, ...` | The capabilities the function may use. Without it, the function is pure. | At most one |
| `requires condition` | A precondition, proven at every call. | Any |
| `ensures condition` | A postcondition, proven for the body. `result` names the return value. | Any |
| `decreases measure, ...` | Proves that recursion ends. See [Termination](#termination). | At most one |
| `cost resource bound` | A proven bound on a resource. See [Cost clauses](#cost-clauses). | Any |

- Clauses of different kinds may come in any order. `truss fmt` orders the
  kinds `uses`, `requires`, `ensures`, `decreases`, `cost`, and never
  reorders clauses of one kind.
- Repeated clauses all hold, and each may rely on the ones before it. Each
  `requires` may rely on the `requires` before it, and each `ensures` on
  every `requires` and the `ensures` before it:

  ```truss
  fn bump(items: mut List[Int64], index: USize)
    requires index < items.length()
    requires items[index] < Int64.maximum
  ```

  The second `requires` reads `items[index]`, which is in bounds because of
  the first. Repeated `invariant` clauses, on types and loops, work the same
  way.
- `requires` and `ensures` are never evaluated when the program runs.
- `Self.Uses` and `Source.Uses` name an associated capability set (see
  [Associated capability sets](#associated-capability-sets)).

### Termination

- A function with a `time` clause terminates. `cost time finite` promises
  termination without a bound. A function without a `time` clause may not
  terminate.
- A function called in a specification is pure and has a `time` clause.
- A recursive function with a `time` clause shows that its recursion ends.
  A recursive call on a part of a parameter needs nothing written. A part is
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

- Other recursion states a `decreases` clause:

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

  A measure is an integer expression over the parameters that stays at or
  above zero, and every recursive call makes it smaller. A list of measures
  is compared in order: each call makes the first smaller, or keeps it and
  makes the second smaller, and so on. Functions that call each other in a
  cycle each state a `decreases` clause, and every call between them makes it
  smaller. The compiler never guesses a measure.
- A function reaches itself through more than calls: by naming a function as
  a value, and by using an `impl` where a bound needs one. Inside an `impl`'s
  methods, using that same `impl`, as by passing `self` to a generic function
  bounded by the trait being implemented, is a recursive call to every
  method of the `impl`. Such a use passes no arguments the prover can
  compare, so it cannot be shown to decrease.
- A loop that runs until a capability says to stop, such as reading until the
  end of a stream, or until a channel delivers a message, cannot be proven to
  terminate. A function that contains one has no `time` clause.

### Cost clauses

```ebnf
cost        = [ "amortized" ] resource bound ;
resource    = "time" | "allocations" | "allocated_bytes"
            | "calls" "(" call_target ")" ;
call_target = LOWER_NAME | path_type [ "." LOWER_NAME ] ;
bound       = "O" "(" expression ")" | "finite"
            | ( "<=" | "==" ) expression ;
```

| Resource | Bounds |
|---|---|
| `time` | `O(expression)` or `finite` |
| `allocations` | `O(...)`, `<= expression`, `== expression` |
| `allocated_bytes` | `O(...)`, `<= expression`, `== expression` |
| `calls(target)` | `O(...)`, `<= expression`, `== expression` |

- The target of `calls` is a function parameter (`calls(visit)`), a
  capability method (`calls(FileRead.read)`), or a whole capability
  (`calls(FileRead)`). It cannot be an associated capability set.
- `O(f)` means that the cost is at most `c * f + d` for every input, for some
  constants `c` and `d` that the prover finds. So `O(rows * columns)` holds
  for every input size, small inputs included.
- `time` counts abstract steps: each primitive operation and each call counts
  as one.
- A caller's cost is proven from its callees' cost clauses, not their bodies.

```truss
public fn load_configs(paths: List[Path]) -> Result[List[Config], ConfigError]
  uses FileRead
  cost calls(FileRead.read) == paths.length()
  cost time O(paths.length())
```

A bound is an expression on exact integers that can use:

- the parameters, `self`, their fields, and pure methods with a `time` clause,
  such as `items.length()`
- `result`, as in `cost time O(text.length() + result.length())`
- `+` and `*`, and `/` and `-` where the result stays at or above zero
- `log(n)`, the smallest integer at least log₂(n + 1), so `log(0)` is 0 and
  `log(1)` is 1
- `power(base, exponent)`, as in `O(power(2, items.length()))`
- `time(visit)`, a bound on the time of any one call to the function
  parameter `visit`, and `calls(...)` as above
- `time(Element.equal)`, a bound on the time of any one call to a method of a
  trait that bounds a type parameter

`time(visit)` cannot depend on the arguments `visit` is called with, because
a function type's parameters have no names. If `visit` has the type
`(fn(Item) cost time O(1))`, `time(visit)` is a constant. If it has
`cost time finite`, `time(visit)` is a fixed bound that is not known.

A generic function counts the methods of its bounds:

```truss
fn Slice[Element: Equal].contains(self, item: Element) -> Bool
  cost time O(self.length() * time(Element.equal))
```

- In `time(Element.equal)`, `Element` is a type parameter of the definition,
  or `Self` in a trait, and `equal` is a method of a trait that bounds it. If
  the name has several versions, the term means the read-only one.
- An operator counts as the method it calls: `==` and `!=` spend
  `time(Element.equal)`, and `<`, `<=`, `>`, and `>=` spend
  `time(Element.compare)`.
- At a call, the term has the value the type gives it. For `List[Int64]`,
  `time(Int64.equal)` is a constant, because `impl Equal for Int64` promises
  `cost time O(1)`, so `contains` is `O(self.length())`. For `List[String]`,
  the term is a fixed bound that is not known.
- A trait's provided method states its cost the same way, as in
  `cost time O(time(Self.equal))`, and an `impl` that writes the method keeps
  that bound.

`log` and `power` are also specification functions, with the same meaning in
`requires`, `ensures`, invariants, `decreases`, and proofs. The prover knows
`log` of a number exactly, and that `log` of a value of an integer type is at
most the type's width. Outside a `cost` bound, a local or a definition of the
file named `log` or `power` takes precedence. Neither function can be called
in code that runs.

```truss
fn digit_count(value: UInt64, base: UInt64) -> USize
  requires base >= 2
  ensures result <= log(value) + 1
```

#### Amortized costs

A method that is cheap almost every time promises an *amortized* bound:

```truss
public opaque type List[Element](buffer: Buffer[Element], length: USize, capacity: USize)
  invariant length <= capacity
  cost potential growth_credit(length, capacity)

fn List[Element].push(mut self, item: own Element)
  cost amortized time O(1)
```

- A type can declare a `cost potential`: an integer expression over its
  fields that never goes below zero. A value's potential is its type's
  potential plus the potentials of its parts.
- `cost amortized time O(f)` promises that the method's actual cost, plus the
  change in the potential of the values it changes or returns, is within
  `O(f)`. `amortized` works with every resource that takes an `O(...)` bound.
- Amortized bounds add up: a function that pushes `count` times can promise
  `cost amortized time O(count)`, or a plain bound that includes the
  potential the list came in with, as in `cost time O(count + items.length())`.
- A function can state both bounds on a resource. `List.pop` promises
  `cost time O(1)` and `cost amortized time O(1)`. A caller with an amortized
  bound counts the amortized one, and any other caller the plain one.
- A value's potential belongs to that value alone. `copy()` makes a new
  potential, and pays for it with its own cost.
- There are no bounds that hold only on average over random choices. Every
  bound holds for every input.

### Function types

```ebnf
function_type        = "fn" "(" list([ LOWER_NAME ":" ] [ mode ] type) ")" [ "->" type ] ;
function_type_clause = "uses" capability_list | "cost" cost | "requires" expression ;
```

A function type is written `fn(Input) -> Output`, and `-> Unit` is left out.
A function type with clauses is in parentheses, with the clauses after its
return type:

```truss
fn sort_by(items: mut List[Item], compare: fn(Item, Item) -> Ordering)
fn record_all(items: List[Item], record: (fn(Item) uses Clock, Random))
fn serve(handle: (fn(Request) -> Response uses Database, Log cost time finite))
```

- A function type without `uses` is pure. One without a `time` clause may not
  terminate.
- Its `uses` and `cost` clauses cannot mention its parameters: `cost time
  O(1)`, `cost time finite`, and `cost allocations == 0` are allowed.
- The parentheses end the clauses, so they never run into the next parameter
  or type argument, as in `List[(fn(Item) uses Clock, Random)]`.
- Clauses after a definition's return type belong to the definition. A
  function that returns a function type with clauses puts it in parentheses:
  `fn make_counter() -> (fn(Int64) -> Int64 uses Clock)`.

The type of a function-typed parameter can constrain, with a `requires`, the
arguments the function passes it. Its inputs are then named, and the
`requires` can also mention the parameters before it:

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

- The function meets the `requires` at every call it makes through
  `transform`, and a lambda passed for it may rely on it. Above, the lambda
  knows that `i` is one of `indices`.
- A named function passed for it accepts every argument the `requires`
  allows.
- The names are only for the `requires`. They are not labels.
- A function type names its inputs exactly when it has a `requires`, and only
  the type of a definition's parameter, at its top, can have one: not a
  field's type, a result type, or a type argument.

A function-typed parameter can be called but not kept, so it accepts lambdas
that read local variables. A parameter declared `own` can be kept, and
accepts only functions that read no local variables:

```truss
fn List[Element].sort_by(mut self, compare: fn(Element, Element) -> Ordering)
fn Router.add(mut self, route: String, handler: own fn(Request) -> Response)
```

`mut router.add("/users", handler: list_users)` compiles. Passing `add` a
lambda that reads a local variable is a compile error.

### Capability parameters

A function that passes on whatever capabilities its callback uses declares a
capability parameter:

```truss
public fn for_each[Item, capability Granted](
  items: List[Item],
  visit: (fn(Item) uses Granted cost time finite),
)
  uses Granted
  cost calls(visit) == items.length()
  cost time O(items.length() * time(visit))
```

A type that holds a function writes the capabilities in the field's type, as
in `type Timer(tick: (fn() uses Clock))`.

### Parameter modes

```truss
fn total(scores: List[Int64]) -> Int64
fn sort[Element: Ordered](items: mut Slice[Element])
fn push[Element](items: mut List[Element], item: own Element)
```

A parameter is read-only by default. `mut` lets the function change the
caller's value, and `own` gives the function ownership of it. When a place
is passed to a `mut` or `own` parameter, the call repeats the keyword:

| Call | Meaning |
|---|---|
| `sort(mut scores)` | `scores` may change. |
| `push(mut names, item: own name)` | `name` is moved, and cannot be used afterward. |
| `push(mut names, item: name.copy())` | `name` is kept, and `push` gets a copy. |
| `push(mut names, item: "Alice")` | A temporary is never marked. |

Copies that would allocate are never made implicitly.

A keyword before a longer expression marks the longest place the expression
starts with. The first method call after that place takes it as its
receiver, in the keyword's mode, and anything after that call works on the
call's result, a temporary:

| Expression | Marked place |
|---|---|
| `mut scores.sort()` | `scores` |
| `mut config.servers.sort()` | `config.servers`, so `config.clients` can still be used, as by another parallel branch |
| `mut items[0].push(name)` | `items[0]` |
| `mut config.load_servers().sort()` | `config`, for `load_servers`. `sort` changes the list it returns. |
| `own config with (debug: true)` | `config` |
| `sort(mut items[..middle])` | `items[..middle]`, since there is no method call |

An expression that does not start with a place cannot be marked:
`mut make_list().push(1)` is a compile error, with a fix that removes `mut`.
Whether an expression starts with a place is known after name resolution:
`mut parse[Int64](text)` starts with a function.

`own` can move one field out of a record:

```truss
let name = own config.name
let port = config.port
config.name = "default"
save(own config)
```

After `own config.name`, the other fields of `config` can still be used, and
`config` as a whole can be used again once `config.name` is assigned.

A place lent `mut` can be moved out of in the same way, if it is assigned
again before it goes back to its owner:

```truss
fn Option[Value].take(mut self) -> Option[Value] {
  let previous = own self
  self = None
  previous
}
```

- The place moved out of is the whole place or a field of it, and the place
  is a `mut` parameter, `mut self`, the variable of a `mut` loop, a `mut`
  binding of a `match`, or a lambda's `mut` parameter.
- It is assigned again on every path: before the function returns, `return`
  and `?` included, before the loop's iteration or the `match` arm ends, and
  in a yielding method before each `yield`.
- Until then it cannot be read or passed to a call.

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

- A method whose first parameter is `self` can be called with a dot. One
  without `self`, such as `List.with_capacity(64)`, is called through the
  type's name.
- `self` has no type annotation: its type is the one named before the dot.
  It is written `self`, `mut self`, or `own self` to give its mode.
- In a `type_head`, the generic parameters are the type's, with any bounds
  the method needs. The method's own go after its name, as in `map[Output]`.
  A bound before the dot, as in `List[Element: Ordered].sort`, means the
  method exists only for those element types.
- Every call uses parentheses: `point.x` reads a field, and `names.length()`
  runs code.
- A method is defined in its type's package, in any file where the type is
  visible. In another file than the type's, the type is named with its
  module: `fn hourly::Forecast.summary(self) -> String`.

### Versions by receiver mode

A method can have up to three versions that differ only in how they take
`self`:

```truss
fn List[Element: Copyable].filter(self, keep: fn(Element) -> Bool) -> List[Element]
fn List[Element].filter(own self, keep: fn(Element) -> Bool) -> List[Element]

fn List[Element].enumerate(self) yields Indexed[Element]
fn List[Element].enumerate(mut self) yields mut Indexed[Element]
```

The keyword at the call picks the version, and no keyword picks the
read-only one. On a temporary, the `own` version is used if there is one, so
`load_scores().filter(is_valid)` keeps the elements of the list it was given.
Truss has no other overloading by a function's parameters.

A type's versions of one name need not all be its own methods. One can come
from a trait that the type implements in its own package:

```truss
impl Iterable for Grid {
  type Element = Cell
  fn each(self) yields Cell { todo }
}

fn Grid.each(mut self) yields mut Cell { todo }
```

A call picks among all of a name's versions by its keyword. See
[Method lookup](#method-lookup) for which versions can be combined.

### Lending and yielding methods

A method can give its caller parts of `self` instead of returning a value. A
*lending* method, with `lends` in place of a return type, gives out one part,
exactly once. A *yielding* method, with `yields`, gives out any number of
parts, one after another. Both give out a part with a `yield` statement.

`yield` is allowed only in a method whose signature `yields` or `lends`.
`yield mut part` is `yield` followed by the expression `mut part`, whose
`mut` marks the place being lent.

#### Lending methods

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
  access.
- **The part is lent for the rest of the caller's statement.** Then the
  method continues after its `yield`, even if the statement leaves early
  with `?` or `return`.
- **For that long, the receiver is lent whole:** the statement makes no other
  use of a receiver lent `mut`, and does not change one lent read-only.
  `mut grid[a].swap(mut grid[b])` is an error for a user's `Grid`.
  `List`, `Slice`, and `Array` are the exception: their `at` has nothing to do
  after its `yield`, so two of their indexes or slices can be lent together,
  `mut` or not, when the prover shows that they do not overlap.
- **The mark is on the place the part is lent from.** In
  `mut grid.cell(position).visit()`, `mut` chooses the `cell` that lends
  `mut`, and `visit` changes the lent part with no mark of its own.
- **A lent part is not the caller's to keep.** It cannot be moved with `own`,
  returned, stored, or bound with `let`, except by copying it, which a
  `Plain` part does implicitly.
- **A lending method yields exactly once on every path.** A path with no
  `yield`, or with two, is a compile error. A loop body that yields and then
  returns is one path with one `yield`.
- A part need not be stored in `self`: the method may yield a value it made,
  and take it back after the caller's statement.
- A lending method cannot drive a `for` loop or make a cursor.

The operand of `yield` may be a constructor applied to places, which lends
those places inside a value built for the caller:

```truss
fn Slice[Element].get(self, index: USize) lends Option[Element] {
  if index < self.length() {
    yield Some(self[index])
  } else {
    yield None
  }
}
```

- An argument of the constructor that is a place is lent, with no `own` and
  no copy. It can be any place the method could yield by itself.
  Constructors nest, as in
  `yield Some(SplitFirst(first: self[0], rest: self[1..]))`.
- Only the constructor written directly after `yield` counts. A `let`, an
  `if` expression, or a call around it does not.
- Every other field is a place, a nested constructor, or a `Plain` value,
  such as an index or a `Slice`. An owned value there is an error; bind it to
  a name first, and the name is then a place.
- A `mut` lend marks each place it lends `mut`:
  `yield Indexed(index: index, value: mut self[index])`. The caller's changes
  to a marked field reach the place when the lend ends. A field without the
  mark is a value. Two places lent `mut` by one `yield` are different places.
- **A place lent `mut` cannot be inside a variant,** at any depth. After
  `yield Some(mut self.second)`, the caller could change the variant, as
  `mut pair.maybe() = None` does, and `self.second` would have no value: a
  use after free. A method that lends an `Option` to be changed yields a
  local with `yield mut`, and after the `yield` writes the local to the
  field.
- The built value owns nothing it was lent, and the receiver is lent whole
  for as long as it is lent.

#### Yielding methods

- `yields Cell` gives read-only parts, `yields mut Cell` lends `mut` access
  to each, and `yields own Cell` hands over owned values.
- **A yielding method drives a `for` loop:**

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
  continue. So the type's invariants, and the method's `ensures` clauses
  about how it ends, hold at each `yield`, whatever the caller did to the
  part it was lent.
- `for item in items` calls `items.each()`, and `for item in mut items` and
  `for item in own items` call the `mut self` and `own self` versions. A type
  supports `for` by defining `each`, as its own method or by implementing
  `Iterable`, whose one method is `each(self)`.
- A method yields a view only of its parameters, as a function returns one.

#### Cursors

A call of a yielding method anywhere but as the collection of a `for` loop
makes a cursor, which is pulled one value at a time:

```truss
var first_cursor = first.each()
var second_cursor = second.each()
var differences = 0
while mut first_cursor.next() is Some(left) && mut second_cursor.next() is Some(right) {
  if left != right { differences += 1 }
}
```

- `mut cursor.next()` runs the method to its next `yield` and returns `Some`
  of the value it yields, or `None` when the method ends. A cursor that is
  dropped ends the method at its last `yield`, as `break` does.
- A cursor from an `own self` method owns its receiver. A cursor from a
  `self` method is a view of it.
- A pull returns an owned value. So a method that yields read-only places, as
  `List.each` yields `self[index]`, makes a cursor only where the element is
  `Plain`. A method that yields only temporaries yields owned values.
- A method that yields `mut` access makes no cursor, since the cursor would
  store the access between pulls. Two collections are changed side by side
  through indexes, or through `zip` of two indexable collections:
  `for (first, second) in mut names.zip(mut ages)`.
- A method that yields through a recursive call, such as a tree's `each` that
  runs `for item in left { yield item }`, drives a `for` loop but makes no
  cursor. Creating one is a compile error that names the recursive loop.
- Whether a method can make a cursor is derived from its body, and checked
  where the cursor is created.
- **A cursor's type has no name.** It implements the prelude trait `Cursor`,
  as a cursor type written by hand does:

  ```truss
  trait Cursor {
    type Element
    capability Uses
    fn next(mut self) -> Option[Self.Element]
      uses Self.Uses
  }

  type Lexer[Characters: Cursor[Element = Character]](characters: Characters, line: USize)
  ```

  A function or record that holds a cursor is generic over it, as `Lexer` is.
  To return a cursor, or to store one without a type parameter, use
  `any Cursor[Element = Int64]`, which allocates once.
- **A cursor's `Uses` is its method's `uses` clause.** Each `next`, and each
  iteration of a `for` loop over the cursor, needs those capabilities, and
  uses the implementations provided where `next` is called, not where the
  cursor was made. Two cursors advanced in turn share those implementations,
  so two cursors that each read a line from the console read alternate lines.

#### Contracts of lending and yielding methods

A lending or yielding method's `ensures` describes its yielded parts and its
final state:

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
  is the part being yielded. The caller's statement, or the loop's body, may
  rely on it.
- **Every other clause holds wherever the method ends:** after its last
  statement, and, for a yielding method, at any `yield` where the loop stops.
- **`yielded` is a `Sequence` of the parts yielded so far,** each as the
  caller left it. A lending method's `yielded` holds its one part once the
  caller is done with it.
- **`finished` is `true` when the method ran to its end,** and `false` when a
  loop stopped it at a `yield`.

The facts of every `for` loop, such as `i < count` in `for i in 0..count` and
that a loop over a list runs once per element, come from these clauses on the
standard library's `each` methods. A user's collection gets the same facts by
making the same promises.

### Constructors

| Name | Use |
|---|---|
| `Type.new(...)` | The main constructor: `Account.new(owner)` |
| `Type.from(value)`, `Type.try_from(value)` | Conversions, through standard traits |
| `Type.default()` | A default value, through a standard trait |
| A descriptive name | Any other constructor: `List.with_capacity(64)`, `Map.seeded()` |

`new` is an ordinary name. A record whose fields are all visible is built
directly, as in `Point(x: 0.0, y: 0.0)`. Lists and maps are built with
literals (`[]`, `[:]`).

## Statements and blocks

```ebnf
block     = "{" lines(statement) "}" ;

statement = "let" pattern [ ":" type ] "=" expression [ "else" block ]
          | "var" pattern [ ":" type ] "=" expression [ "else" block ]
          | expression [ assignment_operator expression ]
          | "for" pattern "in" expression { loop_clause } block
          | "while" expression { loop_clause } block
          | "parallel" block
          | "parallel" "for" pattern "in" expression { loop_clause } block
          | "concurrent" block
          | "concurrent" "for" pattern "in" expression { loop_clause } block
          | "proof" block
          | "assert" expression
          | "yield" expression ;

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

- `let` binds an immutable value and `var` a mutable one. Both take a
  pattern, as in `var (low, high) = bounds`, and every name a `var` binds is
  mutable.
- A block's value is its last expression, so `summarize` returns the
  `Ok(...)` on its last line. Blocks, `if`, and `match` are expressions.
- The left side of an assignment is a place.
- **Every value is used.** A statement whose value is not `Unit`, such as a
  call that returns a `Result`, is a compile error. `let _ = expression`
  discards a value. An `if` or `match` written as a statement has `Unit`
  branches.
- **Every variable is used.** A `let` or a pattern that binds a name nothing
  reads is a compile error; bind `_` instead. Parameters are exempt.
- **Unreachable code is a compile error:** a statement after an expression of
  type `Never`, such as `return`, `break`, `continue`, `unreachable`, a call
  that returns `Never`, or a `while true` that is never left. The check uses
  types alone, so `if false { ... }` is not reported. Code after a `todo` is
  exempt.
- `return`, `break`, `continue`, and `unreachable` have type `Never`, so they
  can stand where a value is expected: `None => return Err(error)`. `break`
  and `continue` are allowed only in loops, and take no value and no label.
- `assert` is allowed only in tests, theorems, and proofs. In a proof it is
  proven when the code is compiled; in a test it is checked when the test
  runs.
- `parallel` and `concurrent` are defined in [Parallelism](#parallelism) and
  [Concurrency](#concurrency), `proof` in [Proof blocks](#proof-blocks), and
  `yield` in [Lending and yielding methods](#lending-and-yielding-methods).

### Patterns

```ebnf
pattern         = pattern_primary { "|" pattern_primary } ;
pattern_primary = "_"
                | range_end [ ( ".." | "..=" ) range_end ]
                | [ module_path "::" ] UPPER_NAME [ pattern_fields ]
                | pattern_fields ;
range_end       = literal_pattern | constant ;
literal_pattern = [ "-" ] INTEGER | "true" | "false" | plain_string
                | [ module_path "::" ] TAGGED_STRING ;
constant        = LOWER_NAME
                | module_path "::" LOWER_NAME
                | [ module_path "::" ] UPPER_NAME "." LOWER_NAME ;
pattern_fields  = "(" list(pattern_field) ")" ;
pattern_field   = LOWER_NAME ":" pattern | pattern | ".." ;
```

A pattern is written the way its value is built. A variant pattern names the
variant without its type or module, and the variant is looked up in the type
of the matched value. A record pattern has no type name:

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
  name, so `(index, element)` binds both fields of an `Indexed`.
- `field: pattern` matches one field against a pattern: `(index, element:
  score)` binds the field `element` to `score`.
- In a record or variant with exactly one field, a bare pattern matches that
  field whatever its name, so `Some(count)` binds the value in the `Some`.
- Fields can be written in any order. `..` skips the remaining fields, and is
  only the last field.
- A nested pattern is looked up the same way: in `Some(Circle(..))`, `Circle`
  is looked up in the type inside the `Option`.
- Parentheses in a pattern always hold fields, so patterns have no grouping
  parentheses.

Patterns can also match values:

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
| `301 \| 302 \| 307`, `Some(Low \| Normal)` | A value that matches any of the alternatives |
| `_` | Anything, without binding it |
| `code` | Anything, binding it to `code` |

- A bare name that names a constant in scope means that constant. Any other
  bare name binds a new variable. Constants of other modules and of types are
  qualified, as everywhere: `http::ok`, `Status.teapot`.
- A constant in a pattern has a type with structural equality (see
  [Equality](#equality)), so that matching it and comparing it with `==`
  agree.
- The ends of a range are literals or constants, and both are written. A name
  there is a constant.
- Float literals are not patterns. Write a guard: `value if value == 0.0`.
- Every alternative of an or-pattern binds the same names, with the same
  types.
- A pattern in `let`, `var`, `for`, or a lambda's parameters matches every
  value of its type. A pattern that can fail, such as `Some(user)`, goes in a
  `match`, an `is` test, or `let ... else`.

### `match`

```ebnf
match = "match" expression { "," expression } "{" lines(arm) "}" ;
arm   = pattern { "," pattern } [ "if" expression ] "=>" statement ;
```

- Each arm goes on its own line, with no comma between arms. An arm's body
  can continue on the next line after `=>`, or be a block.
- An arm's body is a statement, so it can be an assignment, a `yield`, an
  `assert`, or a loop: `Click => clicks += 1`. When the `match` is used as a
  value, an arm whose body is not an expression has type `Unit`.
- A *guard*, `if condition` after the patterns, takes the arm only when the
  patterns match and the condition is true.
- **A `match` covers every case.** An arm with a guard never counts toward
  covering its pattern. When the guards cover everything, the last arm is
  `_ => unreachable`, which the prover checks.
- **Every arm is reachable.** An arm that earlier arms already cover is a
  compile error. A misspelled constant binds a variable that matches
  everything, so it makes the arms after it unreachable, or leaves its
  binding unused, and either is an error.

A `match` on several values has one pattern per value in each arm:

```truss
match state, event {
  Idle, Start => todo
  Running, Stop => todo
  Idle | Paused, Tick if elapsed > limit => todo
  _, Reset => todo
}
```

No tuple is made. The values are matched together, as if by nested
`match`es, and coverage and reachability are checked across all of them.

### `is`

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

- `is` has the precedence of a comparison, so it combines with `&&` and
  `||`. The pattern can be anything an arm can have.
- The names the pattern binds can be used only where the test is known to be
  true: in the rest of an `&&` chain, in the block of the `if` or `while`, and
  in an arm whose guard contains the test. They cannot be used after `||` or
  in an `else`.

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
- The `else` block has type `Never`: it ends with `return`, `break`,
  `continue`, or `unreachable`, or with a call that returns `Never`.
- `var ... else` binds mutable names.
- The expression before `else` cannot end with `}`. Put such an expression in
  parentheses: `let Some(choice) = (if ready { first } else { second }) else { ... }`.

### Updating records

A `with` expression makes a record with some fields changed:

```truss
let moved = origin with (x: 1.0)
let production = own config with (server.port: 443, log_level: LogLevel.Warning)
let retry = request.copy() with (attempt: request.attempt + 1)
```

```ebnf
update = LOWER_NAME { "." LOWER_NAME } ":" expression | LOWER_NAME ;
```

It means the same as copying the base into a new variable, assigning to its
fields, and returning it:

```truss
{
  var updated = own config
  updated.server.port = 443
  updated.log_level = LogLevel.Warning
  updated
}
```

- The base is handed over as an `own` argument is: a place is marked `own` or
  copied. A `Plain` base needs neither, as with `origin`.
- An owned base is reused in place, so the update costs one write per field.
- A field can be a path, such as `server.port`, to update a nested field.
- `origin with (x)` uses a variable named `x`, as building a record does.
- `with` works on records. Only fields visible at that point can be updated.
- `with` applies to the expression directly before it:
  `(own config with (debug: true)).validate()`.

### Lambdas

```ebnf
lambda = "fn" "(" list(pattern) ")" block ;
```

```truss
let passing = scores.filter(fn(score) { score >= threshold })
let total = entries.fold(0, combine: fn(sum, (value, ..)) { sum + value })
mut scores.update_each(fn(score) { score = score / 2 })
```

- A lambda's parameter types, modes, and result type are never written. They
  come from the function type the lambda is passed as. In `update_each`,
  which takes `fn(mut Element)`, `score` can be changed.
- Types are inferred from the outside in: the receiver and the other
  arguments decide the function type, and then the lambda's body is checked.
  A parameter's type is never inferred from its uses in the body. Where
  nothing gives the lambda a function type, the `let` has a type, or the call
  has type arguments:

  ```truss
  let is_ready: fn(Job) -> Bool = fn(job) { job.is_ready() }
  let handler = make_handler[HttpRequest](fn(request) { respond(request) })
  ```

  `let length = fn(text) { text.length() }` is a compile error, with a fix
  that adds a type to the `let`.
- A parameter is a pattern that matches every value, such as `(value, ..)`,
  or `_`.
- **A lambda reads local variables through views, and cannot change them.** A
  lambda that reads local variables is a view: it can be bound with `let`,
  held in a local record or list, and passed to a function-typed parameter.
  It cannot be returned, stored where the caller keeps it, or given to an
  `own` function-typed parameter. A named function, and a lambda that reads
  no local variable, can be returned, stored, and moved.
- A lambda's capabilities are inferred from its body. A lambda that calls
  `Clock.now()` can be passed only where a function type with `uses Clock` is
  expected.
- Inside a lambda, `return` and `?` leave the lambda. `break` and `continue`
  cannot reach a loop outside it.
- A lambda is always passed inside the call's parentheses.

### Errors

Recoverable errors are values of type `Result[Value, Error]`. `?` after a
`Result` returns the error from the enclosing function, unchanged, so it
works only where the error type is the function's. A conversion is written
with `map_error`:

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

- A variant with exactly one field can be used as a function, so
  `ConfigError.Unreadable` is a function from `SystemError` to
  `ConfigError`, and `names.map(Some)` works. A variant with more fields is
  not a function.
- `?` after an `Option` works in a function that returns an `Option`. `?`
  never converts between the two: `.ok_or(error)?` turns an `Option` into a
  `Result`, and `.ok()?` the reverse.
- `main` returns an `ExitCode`, so it cannot use `?`.

### Loops

| Loop | Meaning |
|---|---|
| `for score in scores { ... }` | Read each element. |
| `for score in mut scores { score = score / 2 }` | Change elements in place. |
| `for item in own items { ... }` | Move each element out of the collection. |
| `for (index, element) in mut scores.enumerate() { ... }` | The mode applies to `scores`. |
| `for i in 0..items.length() { ... }` | Loop over a range. |
| `while low < high { ... }` | Loop while a condition holds. |

- The mode keyword goes on the collection, by the rule for calls. A `mut`
  loop may change elements but not add or remove them.
- `while true { ... }` is the infinite loop. A `while` whose condition is the
  literal `true`, and that no `break` leaves, has type `Never`.
- Loops are statements, not expressions.

A loop can state facts for the prover in clauses:

```truss
while low < high
  invariant high <= sorted.length()
  decreases high - low
{
  todo
}
```

- `invariant` holds at the start of every iteration and when the loop ends,
  and may repeat.
- `decreases` names a measure that shrinks on every iteration and never goes
  below zero, which proves the loop ends. A loop has at most one, which may
  be a list of measures compared in order, as for a function. A `while` loop
  in a function with a `time` clause is proven to terminate, and states a
  `decreases` when the compiler cannot show it alone.
- In the clauses of a loop over a range, the loop variable is the index of
  the next iteration. In `for i in start..end`, `i` is `start` on entry, one
  more after each iteration, and `end` where the loop ends; after the last
  iteration of `start..=end`, it is `end + 1`. A range whose start is past
  its end runs no iteration, and `i` stays `start`:

  ```truss
  var kept: USize = 1
  for index in 1..count
    invariant kept <= index
  {
    todo
  }
  ```

- In the clauses of any other `for` loop, `yielded` is the `Sequence` of the
  values of the iterations before. The clauses cannot name the loop's
  element, which is bound only in the body:

  ```truss
  var total: Int64 = 0
  for score in scores
    invariant total == sum(yielded)
  {
    todo
  }
  ```

A loop's `cost` clause bounds the loop's cost so far, at the start of every
iteration and when it ends. A loop needs one only when its iterations cost
different amounts:

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

- A loop's `cost` takes the resources and bounds of a function's and may
  repeat. It is never `amortized` and its bound is never `finite`.
- Its bound can use the variables in scope at the loop and, in a `for` loop,
  `yielded` or a range's index.
- `sum` adds a measure of each element of a `Sequence`, here each row's
  length. The measure is a lambda or a named function that terminates and
  uses no capabilities, and two lambdas with the same body are the same
  measure.

### Ranges

```truss
let all = 0..count
let bytes = 0..=UInt8.maximum
let backward = (0..count).reversed()
let evens = (0..count).step_by(2)
```

- `0..count` holds 0 up to `count`, without `count`. `0..=UInt8.maximum`
  includes its end.
- A range whose start is at or past its end is empty.
- A range of characters, such as `Character"a"..=Character"z"`, holds the
  characters between its ends in the order of their code points. The
  surrogates are not characters, so U+E000 follows U+D7FF.
- A range with no start or no end, such as `2..`, is allowed only directly in
  brackets, as in `items[2..]`.

### Collections

| Literal | Value |
|---|---|
| `[2, 3, 5, 7]` | A `List`, or an `Array` or `Set` where one is expected |
| `[]` | An empty `List`, or an empty `Set` or `Sequence` where one is expected |
| `["http": 80, "https": 443]` | A `Map` |
| `[:]` | An empty `Map` |

```ebnf
map_entry = expression ":" expression ;
```

- A `[...]` literal is a `List` unless the expected type is an `Array`, a
  `Set`, or a `Sequence`, `FiniteSet`, or `FiniteMap` in a specification, as in
  `let colors: Set[String] = ["red", "green"]`. An `Array` literal has
  exactly as many elements as its type says.
- The element types of `[]` and `[:]` come from the context or an
  annotation.
- Map keys are expressions, so `[name: 1]` uses the value of `name`.
- A non-empty list literal in a function body counts as one allocation in
  `cost` clauses, and an empty one as none.
- A set or map literal means: make an empty collection with room for every
  element, then `insert` each element in order. It costs the sum of those
  calls. `insert` requires that the key is not there yet, so keys in a map
  literal are proven distinct.
- The keys of a `Map` and the elements of a `Set` are `Hash` and `Ordered`.
  Lookups, insertions, and removals cost O(log n) in the worst case, and
  O(1) in typical use. A `Map` and a `Set` iterate in insertion order.
- `Map.seeded()` and `Set.seeded()` make an empty collection whose hashing
  takes a key from the `Random` capability, and declare `uses Random`. They
  give the same results as ordinary ones.
- `truss fmt` puts each element of a long literal on its own line.

#### Arrays

```truss
let digest: Array[UInt8, 32] = Array.filled(0)
let squares: Array[USize, 8] = Array.generate(fn(index) { index * index })
public let round_constants: Array[UInt32, 4] = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5]

fn sum[count: USize](values: Array[Int64, count]) -> Int64
```

- An `Array` holds its elements in place, with no heap allocation, and is
  `Plain` when its elements are.
- `Array.filled(value)` and `Array.generate(fn(index) { ... })` take the
  length from the expected type. A literal works too, including in
  constants.
- An `Array` is never moved to the heap without being asked. A very large one
  can overflow the stack.

#### Indexing

| Indexing | Meaning |
|---|---|
| `items[i]` | Element `i`, which is proven in bounds. `i` is a `USize`. |
| `items.get(i)` | `Some(element)`, or `None` if `i` is out of bounds. |
| `items[1..4]`, `items[2..]`, `items[..3]` | A `Slice`, whose bounds are proven. |
| `scores[i] = 0` | Replaces element `i`, which is in bounds. |
| `ports[name]` | The value for `name`, which is proven present, as by an earlier `if ports.contains(name)`. |
| `ports.get(name)` | `Some(value)`, or `None` if `name` is missing. |
| `ports[own name] = 8080` | Inserts or replaces the value for `name`. The map keeps the key, so a key that is not `Plain` is moved with `own` or copied. |

- Strings cannot be indexed: `text.bytes()` and `text.characters()` say which
  is meant.
- A type supports `[]` by implementing the prelude trait `Index`, whose
  lending methods `at` give read and `mut` access to an element, and whose
  `contains_key` states an index's precondition (see
  [Associated types](#associated-types)).
- `collection[key] = value` inserts a missing key when the type also
  implements `IndexAssign`, whose one method `assign` takes the key and the
  value, as `Map` does. For any other type, the assignment replaces the
  element that `Index` lends, so the key is there.

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

- In an expression, the brackets after a name hold expressions, which cover
  type names and their arguments, such as `List[String]` and
  `Array[UInt8, 32]`. A function type cannot appear there, because `fn(...)`
  would be a lambda; give such a type in an annotation.
- `return` and `echo` take everything after them. A `{` right after
  `return`, on the same line, starts the value being returned.
- `forall` and `exists` are defined in
  [Writing specifications](#writing-specifications), and `provide` in
  [Capabilities](#capabilities).

### Operators

The set of operators is fixed, and code cannot define new ones:

- Arithmetic: `+ - * / %`, and prefix `-` for negation
- Comparison: `== != < <= > >=`
- Logic: `&& || !`, and `==>` for implication in specifications
- Bitwise: `& | ^ << >>`, and `~` for bitwise NOT

`!` works on `Bool`, and `~` on integers. Negation works on signed integers
and floats.

`==` and `!=` call the `Equal` trait, and `<`, `<=`, `>`, and `>=` call
`Ordered`, whose `compare` returns `Ordering.Less`, `Ordering.Equal`, or
`Ordering.Greater`. Both sides have the same type, so `Int64 == Int32` does
not compile. Functions, and `any` values, cannot be compared.

The arithmetic operators call traits with a type parameter for the right
side and an associated type for the result:

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

Each arithmetic trait has a second method that says where the operation is
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

| Trait | Defined where | Fixed-width integers | Floats |
|---|---|---|---|
| `Add[Right]` | `add_is_defined(right)` | the sum fits the type | always |
| `Subtract[Right]` | `subtract_is_defined(right)` | the difference fits the type | always |
| `Multiply[Right]` | `multiply_is_defined(right)` | the product fits the type | always |
| `Divide[Right]` | `divide_is_defined(right)` | `right != 0`, and not `minimum / -1` | always |
| `Remainder[Right]` | `remainder_is_defined(right)` | `right != 0`, and not `minimum % -1` | always |
| `Negate` | `negate_is_defined()` | `self != minimum` | always |

Generic code states the obligation that an operator on a built-in type has,
and can test it:

```truss
fn doubled[Number: Add[Number]](value: Number) -> Number.Output
  requires value.add_is_defined(value)
{
  value + value
}
```

A type whose operation is defined everywhere returns `true`.

#### Precedence

Operators bind in this order, tightest first:

| Operators | Notes |
|---|---|
| `.` `()` `[]` `?` `with (...)` | `a.b()?.c()`. `with` applies to the expression directly before it. |
| `mut` `own` `any` | Apply to the whole postfix expression after them, such as `mut config.servers.sort()`. See [Parameter modes](#parameter-modes) for the place they mark. |
| `-` `!` `~` | `-x.abs()` is `-(x.abs())`. `!is_ready == expected` is `(!is_ready) == expected`. |
| `*` `/` `%` | |
| `+` `-` | |
| `..` `..=` | `0..count - 1` is `0..(count - 1)`. |
| `==` `!=` `<` `<=` `>` `>=` `is` | |
| `&&`, `\|\|` | |
| `==>` | `a && b ==> c` is `(a && b) ==> c`. |
| `echo`, `return`, and the body after `=>` in `forall` or `exists` | `echo player.wins * 3` shows the product. |

Precedence is a partial order. These combinations have none, and need
parentheses:

- **Shifts and bitwise operators** combine only with themselves. A `bitwise`
  expression is a whole expression, so `a | b | c` is valid, but
  `(flags & 0xFF) | extra`, `a << (b + 1)`, and `(flags & mask) != 0` need
  their parentheses.
- **`&&` and `||`** do not mix: `(is_ready && is_valid) || is_forced`.
- **Comparisons, `is`, ranges, and `==>`** do not chain: `a < b < c`,
  `a == b == c`, `0..10..20`, and `a ==> b ==> c` are errors.
- **`!` directly before the left operand of `is`:** `!response is Ok(_)` is
  an error. Write `!(response is Ok(_))` or `(!response) is Ok(_)`.

A missing pair of parentheses is a compile error with a fix that adds them.

#### Compound assignment

```truss
self.buckets[index].count += 1
totals[region] += sale.amount
deadline += extension
flags |= Permission.write
```

- `+=`, `-=`, `*=`, `/=`, `%=`, `&=`, `|=`, `^=`, `<<=`, and `>>=` exist
  for the binary operators. They are statements, and their left side is a
  place.
- `a += b` means `a = a + b`, with the place evaluated and checked once: an
  index is proven in bounds once.
- The old value of `a` is handed to the operator as owned. When the
  operator's trait method has a version that takes `own self`, that version
  is used, so `matrix += other` can update in place.
- `truss fmt` writes `x = x + y` as `x += y`.

#### Evaluation order

- Operands, arguments, and fields are evaluated left to right, in the order
  written.
- `target = value` evaluates `value`, then the index keys of `target`, and
  then stores. In `items[next()] = compute()`, `compute()` runs before
  `next()`.
- `target += operand` evaluates `operand`, then the index keys of `target`,
  once. Then the operator takes the old value of `target`, and the result is
  stored. In `totals[region()] += parse(text)?`, a failed `parse` returns
  before `region()` runs, and `totals` is left as it was.
- `&&` and `||` evaluate their right side only when the left does not decide
  the result.

### Integers

- **No integer operation overflows silently.** An operation that could
  overflow is proven not to. Otherwise the code calls an explicit
  alternative: `checked_add`, which returns an `Option`, `wrapping_add`, or
  `saturating_add`.
- `/` on integers rounds toward zero, and `%` has the sign of the left
  operand, so `-7 / 2` is `-3` and `-7 % 3` is `-1`.
  `value.floor_divide(divisor)` and `value.floor_modulo(divisor)` round down.
- `>>` on a signed integer copies the sign bit. On an unsigned integer it
  shifts in zeros.
- A shift amount can be any unsigned integer type, and is proven smaller than
  the number of bits in the value being shifted.
- Negating a signed integer is proven not to overflow, since `-Int8.minimum`
  does not fit. Unsigned integers cannot be negated.
- A proof about `USize` or `ISize` holds for both widths, 32 and 64 bits,
  unless the package says `usize_bits = 64`.
- `FixedWidthInteger` is implemented by every built-in integer type,
  `SignedInteger` by `Int8` through `ISize`, and `UnsignedInteger` by `UInt8`
  through `USize`. They are sealed: no other type implements them. A
  provided method of one, such as `checked_power`, is a method of every width.
  A type's own bounds are `minimum_value()`, `maximum_value()`, and
  `bit_width()`.

### Floats

- Float arithmetic follows IEEE 754, and NaN and infinity are ordinary
  values, so no float operation fails.
- **Float results are the same on every platform.** The operations IEEE 754
  defines exactly, such as `+`, `*`, `sqrt`, and `fma`, are never contracted
  or reordered. Functions such as `sin` and `exp`, and conversions between
  floats and text, are the standard library's own, the same everywhere.
  `to_bits()` returns one bit pattern for every NaN.
- **`==` treats every NaN as equal to every other NaN,** and otherwise
  follows IEEE 754, so `-0.0 == 0.0`. In ordering, NaN comes after every
  number. This makes `Equal` and `Ordered` on floats lawful.
- `x.is_nan()` tests for NaN. `x.ieee_equal(y)`, `x.ieee_less(y)`, and the
  other `ieee_` comparisons follow IEEE 754 exactly, and compile to a single
  instruction.

## Failure

Code stops abruptly only where its signature says it can, except by running
out of memory or overflowing the stack.

Every operation that can fail is a proof obligation: integer overflow,
division by zero, indexing or slicing out of bounds, a shift that is too
large, `unwrap`, `expect`, and `unreachable`. Where the compiler cannot prove
the operation safe, the code is a compile error, and one of these makes it
compile:

1. Establish the fact locally, as with an `if` that checks the length first.
2. Require it from the caller with `requires`.
3. Call the checked version, which returns an `Option` or a `Result`, such as
   `items.get(index)` or `checked_divide`.
4. Declare `uses Panic`, which allows a failure when the program runs.

`unreachable` marks a point the code can never reach, and only the first fix
applies to it: it is proven unreachable, or the code does not compile.

### `Panic`

`Panic` is a built-in capability. `Panic.crash(message)` prints its message
and location to standard error and ends the process with a nonzero exit
code. No Truss code runs afterward; the operating system releases the
process's memory and handles. `expect` and `unwrap` declare `uses Panic`.

- **A panic cannot be caught.** Code cannot `provide` an implementation of
  `Panic`, so no code can observe a value that a panic left half updated.
- `main` may declare `uses Panic`.

## Capabilities

```ebnf
capability = "capability" UPPER_NAME "{" lines(signature) "}" ;
provide    = "provide" expression { "," expression } block ;
```

A capability is a set of methods for doing something outside pure
computation, such as reading files or getting the time. A function lists the
capabilities it uses with `uses`, and a function without `uses` is pure. The
code that runs a function decides which implementation of each capability it
gets:

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
`Random.next()`, and never calls an implementation directly. An
implementation is a type with an `impl`. Its methods take `self`, or
`mut self` where they change the implementation's state:

```truss
type LoadedDie(face: UInt64)

impl Random for LoadedDie {
  fn next(self) -> UInt64 { self.face }
}

let rolled = provide LoadedDie(face: 5) {
  roll_die()
}
```

`provide implementation, ... { body }` runs the body with the given
implementations. They are handed over as arguments are: a temporary needs no
mark, and a place is marked `mut` when its methods change its state, and then
holds the changes afterward:

```truss
var disk = files::MemoryFiles.new()
let config = provide mut disk, log::DiscardLog() {
  save_and_reload(Path.new("app.toml"))
}
```

- A type can implement several capabilities, and providing it provides all
  of them.
- An `impl` can declare `uses` when its methods use capabilities of their
  own. Providing it then requires those capabilities.
- An `impl`'s methods use only the capabilities that their trait or
  capability declares, and those of the `impl`'s `uses` clause.
- **A capability method always returns to its caller.** It cannot leave the
  code around the call, stop it partway, or run it more than once.
- A capability's method keeps no view that it is given, and returns no view
  of its implementation's state.

### Standard capabilities

These capabilities are in the prelude:

| Capability | Allows |
|---|---|
| `Console` | Reading standard input, writing standard output and standard error |
| `FileRead` | Opening files to read, reading files, and listing directories |
| `FileWrite` | Creating, writing, renaming, and deleting files |
| `NetworkClient` | Opening outgoing connections and looking up names |
| `NetworkServer` | Listening for incoming connections |
| `Handles` | Reading, writing, and closing open handles: a file, a connection, a listener, a running program |
| `Clock` | The current time, a monotonic clock, and sleeping |
| `Random` | Random numbers from the operating system |
| `Environment` | Environment variables, the current directory, and the operating system and processor the program runs on |
| `Processes` | Running other programs |
| `Signals` | Waiting for a signal sent to the program |
| `Tasks` | Running `concurrent` code and using channels |
| `Log` | Writing to the program's log |
| `Panic` | Ending the program (see [`Panic`](#panic)) |

Each capability declares the least an implementation provides. Everything
built on those methods is an ordinary function of the standard library, such
as `files::write_with` and `network::connect`, which works with every
implementation.

### Handles

A handle to something the operating system holds, such as an open file, a
connection, or a running process, is released when its owner is done with
it, as memory is:

```truss
fn first_line(path: Path) -> Result[Option[String], SystemError]
  uses FileRead, Handles
{
  var file = FileRead.open(path)?
  mut file.read_line()
}
```

The file is closed when `first_line` returns, on every path, including the
early return of `?`.

- **Opening is one capability and using an open handle is another.** `open` is
  `FileRead`'s, and every method of a handle, such as `read_line`, has
  `uses Handles`. Code that is handed a handle needs `Handles` alone, and can
  open nothing with it.
- Releasing a handle never runs Truss code and never fails. No type defines
  code that runs when its value is released.
- An operation that can fail, or whose outcome the program needs, is an
  explicit call that returns a `Result`, such as `flush`, `sync`, `shutdown`,
  and `wait`.
- **A buffered writer is only lent, inside a scope.** `files::write_with`
  lends the writer to a function, then writes out the remaining buffered data, and returns
  the first error, from the function or from writing:

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

  Code never owns a writer, so no writer is dropped with data in it. A type
  that writes in stages takes the writer as a `mut` parameter of each call.

### main

A program starts at the `main` of its package's `main` module, which has
this signature and its own `uses` clause:

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

Inside an implementation, a call to the capability it implements goes to
the next provider out. So an implementation can check each call and pass it
on:

```truss
type FilesWithin(root: Path)

impl FileRead for FilesWithin
  uses FileRead
{
  fn read(self, file: Path) -> Result[List[UInt8], SystemError] {
    FileRead.read(self.root.join_confined(file)?)
  }
}

let summary = provide files::FilesWithin(root: Path.new("logs")) {
  log_report::summarize(Path.new("access.log"))
}
```

The `impl` shows one of `FileRead`'s methods; the rest are written the same
way. `log_report::summarize` declares `uses FileRead`. Its read of
`access.log` reaches `logs/access.log`, and a path such as `../secrets` fails
with a `SystemError`. Narrowing again inside the block narrows further, and a
capability that is not narrowed passes through unchanged.

### Layering

A capability can be implemented with others, and cannot inherit from them:

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

Code that `uses ReadDatabase` can run queries and nothing else. Providing a
`PostgresReader` requires `NetworkClient`. A capability cannot be declared as
a bundle of others, as in `capability FileSystem: FileRead + FileWrite`, so
`uses` always names exactly the capabilities the code can call.

## Parallelism

A `parallel` block runs each of its statements at the same time, and ends
when all of them have ended:

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

- Each statement directly inside the block is a *branch*. Several statements
  in one branch are wrapped in a block.
- A `let` in a branch is in scope after the block, not in the other branches.
- **Branches cannot race.** Any branch may read any place. A place that one
  branch changes, by assigning to it or passing it `mut` or `own`, is used by
  no other branch.
- Branches use no capability but `Panic`. A function that contains
  `parallel` is still pure.
- A branch cannot leave the block with `return`, `break`, `continue`, or `?`.
  A branch returns a `Result`, and `?` goes after the block.
- A `parallel` block has the result of running its branches one after
  another, and the prover reads it so. Its `time` is the sum of its branches'
  times. If more than one branch panics, which message is printed may vary.

`parallel for` runs the iterations of a loop at the same time:

```truss
parallel for player in mut players {
  player.rating = estimate_rating(player.history)
}
```

It works with every form of `for`. The body may read any place, and changes
only its own element and its own variables. It uses no capability but
`Panic`, and cannot use `break`, `return`, or `?`. `continue` is allowed.

## Concurrency

A `concurrent` block runs each of its statements as a task, and ends when
every task has ended. The enclosing function declares `uses Tasks`:

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

- Branches are written as in a `parallel` block, and follow its rule about
  places, so tasks cannot race.
- A branch may use the capabilities of the code around it.
- A task never outlives the block that started it.
- **A `?`, `return`, or `break` that leaves the block cancels the other
  branches,** waits for them to end, and then leaves. A branch that has not
  started does not start. The first branch to leave decides where control
  goes and with which value; a later one's is dropped.
- The code after the block does not run when a branch leaves early, so a
  branch that moves a value out of a place reinitializes the place before it
  ends.
- **In a cancelled task, a call of a standard capability that would wait
  returns at once:** `Err(SystemError.Cancelled)` where it returns a
  `Result`, `None` where it returns an `Option`, and early where it returns
  nothing, as `Clock.sleep` does. `Tasks.cancelled()` tells whether the task
  has been cancelled. A cancelled task blocked on the mutex of a `mut`
  implementation waits until it acquires it.

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

The body may read any place, and changes only its own element and its own
variables. `break` leaves the loop and cancels the iterations still running,
and `continue` ends one iteration.

An iteration keeps running after the loop has advanced to the next value, so
its inputs stay valid until the loop ends:

- A range, a cursor, and a method that `yields own` give each task a value of
  its own.
- A method that yields read-only values may yield a place inside a parameter
  that it takes read-only, such as `yield self[index]` in `List`'s
  `each(self)`. The method cannot change that parameter, so each task
  borrows its element for the whole loop.
- A method may yield a value that it computes for the `yield`. The task owns
  it.
- A `Plain` value may be yielded from any place. The task gets a copy.
- A method that yields `mut` access drives a `concurrent for` when its body
  is one `for` over a range whose body is one `yield`, as the `each(mut self)`
  methods of `List`, `Slice`, and `Array` are. Each task then runs one
  iteration of that loop and changes its own element.

Any other `concurrent for` is rejected with `ownership.task_outlives_yield`.
A place in a local of the method or in a `mut` parameter, or a view of one,
could change or be freed when the method resumes while a task still uses it:
a use after free.

`yield` is not allowed in a `concurrent` block or a `concurrent for`.

A time limit is a function whose two branches each return from the
function, which cancels the other:

```truss
public fn with_timeout[Output, capability Granted](
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

A function that waits for another task can wait forever, so it has no `time`
clause.

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

- A message is owned, and sending it moves it. Its type is `Storable`: never
  a view, a function, or an `any` of a trait that does not require
  `Storable`.
- A channel's methods take `self` read-only, so every branch can use a
  channel declared before the block. A channel is a reference to its queue:
  `channel.copy()` is another reference to the same queue, which is freed
  when the last reference is dropped.
- `Channel[Message].new()` has capacity 0 and holds no message: `send`
  returns when another task has received the message.
- The messages of one sender are received in the order it sent them. The
  messages of two senders interleave in any order.
- `send` returns `Err(SendError.Closed)` on a closed channel. `receive`
  returns the messages a closed channel still holds, and then `None`.
  `try_receive` never waits, and returns `None` when the channel is empty.
- In a cancelled task, a `send` that would wait returns
  `Err(SendError.Cancelled)`, and a `receive` that would wait returns `None`.
- `tasks::Limiter` bounds how many tasks do something at once.
  `limiter.hold(work)` runs `work` when one of its permits is free, and
  returns `Some` of the result. In a task cancelled while it waits for a
  permit, `hold` returns `None` and does not run `work`.

### Shared state

State that several tasks change belongs to a capability implementation.
When the code inside a `provide mut` can use `Tasks`, the calls of the
implementation's methods are mutually exclusive: each call holds the
implementation's mutex from start to end, and a task that calls meanwhile
blocks.

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

- Whether the code inside a `provide mut` can use `Tasks` is known from the
  signatures it calls. Code that uses a capability parameter of the
  enclosing function counts. Only such a `provide` has a mutex.
- Other tasks' calls can come between two calls, so a check and the change
  that depends on it go in one method.
- **The mutexes cannot deadlock.** An implementation's methods call only
  capabilities provided outside it, so every task acquires mutexes in one
  order, from the innermost implementation outward. To keep this true, an
  implementation with a mutex has no method with a parameter that can hold a
  function, or an `any` value, that uses a capability.
- An implementation provided without `mut` is only read, and has no mutex.
- `tasks::Cell` holds a value that several tasks update.
  `cell.update(change)` runs `change`, a function that uses no capability, on
  the value while it holds the cell's mutex, and requires `Tasks`.
  `cell.copy()` is another reference to the same value. `tasks::Counter` is a
  cell that holds an `Int64`.

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

- The seeded implementation switches tasks only at capability calls.
- A test that deadlocks fails, and reports the event each task was waiting for.
  The report is a panic, so a function that provides a `SeededTasks` or a
  `World` outside a test declares `uses Panic`.

`simulation::World` provides every standard capability, with tasks scheduled
by a seed and a clock of its own. The clock advances only when every task is
blocked, and then jumps to the earliest deadline of a sleeping task, so a
test of a time limit takes no real time:

```truss
test "a reply that never arrives ends at the time limit" {
  let world = simulation::World.new(seed: 3)
  provide world {
    let reply = tasks::with_timeout(Duration.seconds(5), work: fn() { wait_for_reply() })
    assert reply is None
    assert Clock.monotonic() == Duration.seconds(5)
    assert world.output() == ""
  }
}
```

- `simulation::Setup` holds a world's initial state, such as its console's
  input, its environment's variables, and its files.
  `World.from(setup, seed: seed)` makes the world.
- A world's file system is in memory. `Setup.with_file(path, contents)` puts
  a file in it, with the directories above it, and `world.file_text(path)`
  reads one back.
- `world.fail_next(operation, error)` makes the next `Open`, `Read`, or
  `Write` of a file fail with `error`, once.
- A `World` is a reference to its state, so it is provided without `mut`. A
  test reads the world's record of events, such as `world.output()` and `world.records()`,
  inside the `provide`.
- Each capability call into a `World` is a point where the seed may switch
  to another task.

## Strings

```truss
let greeting = "Hello, ${name}!"
let path = "C:\\logs\\today.txt"
```

- A string literal is a `String` in static memory, so making one costs
  nothing. It is copied to the heap the first time it is changed, which only
  methods that write bytes, such as `push`, do, and their cost clauses allow
  an allocation. `copy()` of a literal's `String` costs nothing.
- `StringSlice` is the view of a `String`, returned by methods such as
  `trim()`, `split()`, and `lines()`.
- There is no concatenation operator, and adjacent literals do not join.
  Text is joined with interpolation or methods:

  ```truss
  let greeting = "${salutation}, ${name}"
  let line = fields.join(", ")
  mut report.push(footer)
  ```

  `+` on strings is a compile error, with a fix that writes an
  interpolation.
- A value in `${...}` has a type that implements `Display`.
- `truss fmt` never breaks a string, and never changes the text inside one.

### Tagged templates

A type name directly before a string of either form makes a tagged template:

```truss
let query = SqlQuery"select name from users where id = ${user_id}"
let pattern = Regex"[a-z]+@${domain}"
```

- The tag is the type of the result. A plain `"..."` string is the case where
  the tag is `String`.
- The tag is a type name without type arguments. If its type is generic, the
  arguments are inferred.
- Extra `$`s for a raw string go between the tag and the quotes, as in
  `Shell$$"""`.

The literal text and the interpolated values are kept apart. The first
example above becomes, roughly, the following, where `Literal(...)` stands for
a piece of literal text, of the type `text::Literal`, which only the compiler
can make:

```truss
SqlQuery.from_template(Template.new(
  literals: [Literal("select name from users where id = "), Literal("")],
  parts: [SqlParameter.from(user_id)],
))
```

A type is a tag by implementing the prelude trait `FromTemplate`, whose one
method is `from_template`. Its associated type `Part` is the type each
interpolated value is converted to, and the method's parameter,
`Template[Part]`, holds the literal text and the converted values.

A tag states the rules for valid literal text with `requires`:

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

- The literal text is known when the code is compiled, so the compiler
  proves the `requires` by running `is_valid_template` on it, as compiled
  code. `Regex"[a-z"` is a compile error, and `Regex"[a-z]+"` needs no `?`.
- A check reads a piece's text with `literal.text()`, a `StringSlice`, and
  its bytes with `text.byte(index)`.
- `from_template` is the one method whose `requires` may be stronger than its
  trait's. A call of `from_template` through a bound or through `any` is a
  compile error.
- Text known only when the program runs goes through a function that returns
  a `Result`, such as `Regex.parse(text)`.

### Characters and bytes

A single character or byte is a tagged template:

```truss
let separator = Character","
let accent = Character"é"
let newline = UInt8"\n"
```

`Character"..."` holds exactly one Unicode scalar value, and `UInt8"..."`
exactly one ASCII character. Both are checked when the code is compiled, and
neither allows `${...}`.

`text.characters()` gives the `Character`s of a string, and
`text.graphemes()` gives its grapheme clusters as `StringSlice`s.

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

- A `law` is a property that every implementation satisfies, proven for each
  `impl`. Its `requires` clauses are its premises: the law holds for every
  set of values that meets them.
- A law uses only methods with a `time` clause and no capabilities, which the
  prover can treat as functions. An `impl`'s method keeps its trait's `time`
  clause.
- Contracts and costs on a trait's methods bind every `impl` and are proven
  for each one.
- **An `impl`'s method may promise more than its trait:** `ensures` and
  `cost` clauses of its own, which it proves, and a `requires` that the
  trait's `requires` implies. A call known to reach that `impl`, such as
  `grid[position]` on a `Grid`, is proven against the `impl`'s contract. A
  call through a bound or through `any` is proven against the trait's.
- A trait states its methods' preconditions through its own methods, as
  `Index` does with `contains_key`, so generic code can meet them.

### Required traits

A trait can require other traits, written like a bound:

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

- A type implements the required traits before it can implement the trait:
  `impl Ordered for Point` needs `Point` to implement `Equal`.
- A bound includes the required traits, so with `[Element: Ordered]`, `==`
  works on `Element`. Laws can use the methods of required traits.
- A trait cannot redeclare a method of a trait it requires. It can add a
  version of one that takes `self` in another mode, as a
  `trait Changeable: Iterable` can declare `each(mut self)`.
- Traits cannot require each other in a cycle.
- A trait with no methods of its own, like `Loggable`, combines traits, as
  for `any`: `List[any Loggable]`.

In the standard library, `Hash` and `Ordered` require `Equal`.

### Methods with bodies

A trait's method with a body, such as `max`, is provided to every
implementation. An implementation can replace it only with a version proven
to give the same result:

```truss
impl Ordered for Int64 {
  fn compare(self, other: Int64) -> Ordering { todo }
  fn max(own self, other: own Int64) -> Int64 { Int64.maximum_of(self, other) }
}
```

- A provided method can be replaced only when the prover reads its body as
  its definition (see [Bodies and contracts in proofs](#bodies-and-contracts-in-proofs)).
- A call of the method is proven from the trait alone, so a replacement never
  changes a call's meaning.

### Implementations

- **A type has at most one `impl` of each trait,** for each set of the
  trait's type arguments, whatever the type's own arguments. Every `impl` is
  written out: none covers every type that matches a bound.
- **An `impl` for a generic type states its conditions on the type's
  parameters,** as a method does:

  ```truss
  impl Display for List[Element: Display] {
    fn display(self, output: mut TextBuilder) { todo }
  }

  impl Equal for Option[Value: Equal] {
    fn equal(self, other: Option[Value]) -> Bool { todo }
  }
  ```

  `List[Element]` implements `Display` exactly when `Element` does, and an
  `impl Display for List[String]` cannot sit beside it.
- **An `impl` lives in the package of the trait, of the implementing type, or
  of the outermost type of one of the trait's arguments.** So
  `impl Multiply[Vector] for Float64`, which makes `2.0 * velocity` work,
  lives with `Vector`. `From[List[UserId]]` cannot be implemented for `Int64`
  in `UserId`'s package.
- An `impl` takes no visibility keyword. It applies wherever its trait and
  the types it names are visible.

### Traits with type parameters

A trait can take type parameters, and a type can implement it once for each
set of arguments:

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

- The `impl` is chosen by the types of the arguments, which are inferred
  first, without looking at which `impl`s exist. A literal argument has its
  default type, or the other operand's type for an operator. So adding an
  `impl` never changes which one an existing call uses.
- The `impl` is never chosen from the expected type of the result. The target
  of a conversion is always named, as in `Int64.from(count)`.

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

- `type Key = Position` appears only in an `impl`.
- `Items.Element` names an associated type of a type parameter, and
  `Iterable[Element = Int64]` constrains it in a bound.

### Associated capability sets

A trait can leave a set of capabilities for each implementation to choose:

```truss
trait Cursor {
  type Element
  capability Uses
  fn next(mut self) -> Option[Self.Element]
    uses Self.Uses
}

impl Cursor for Lines {
  type Element = String
  capability Uses = FileRead
  fn next(mut self) -> Option[String]
    uses FileRead
  { todo }
}

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

- `capability Uses` in a trait declares the set. `Self.Uses` in the `uses`
  clause of the trait's methods is the set of the implementing type.
- `capability Uses = FileRead` in an `impl` defines the set, as a list of
  capabilities, capability parameters, and the sets of the type's
  parameters. An `impl` that leaves the member out has the empty set. A
  method of the `impl` uses the capabilities of the set and no others.
- `Source.Uses` names the set of a type parameter, in the `uses` clause of a
  function or of a function type. A call needs the capabilities of the set
  for its type arguments: `count` needs `FileRead` for a `Lines`, and nothing
  for the cursor of a list.
- A function generic over a `Cursor` that advances it declares
  `uses Source.Uses`. Without the clause, the call of `next` is an error.
- A bound cannot constrain a set, and `calls(...)` cannot count the calls of
  one.

### Equality

A type's equality is *structural* when two equal values cannot be told apart
by any function, so that from `a == b` the prover concludes `f(a) == f(b)`.

- The built-in integers, `Bool`, `Character`, `Unit`, `String`, and the types
  of specifications have structural equality.
- A type that derives `Equal` has structural equality when every one of its
  fields does.
- A hand-written `Equal` is not structural, and promises only an
  equivalence. Float equality is not structural, since `-0.0 == 0.0` while
  `1.0 / -0.0 != 1.0 / 0.0`, so a `Point` of floats derives a lawful but not
  structural `Equal`.
- Outside its package, an opaque type's equality is not structural.

### Deriving

A `derives` clause on a type asks the compiler for trait implementations:

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

| Trait | Derived implementation |
|---|---|
| `Equal` | Two values are equal when their variants are the same and all their fields are equal. |
| `Hash` | Combines the hashes of all fields. |
| `Ordered` | Compares variants in the order they are declared, then fields in the order they are declared. |
| `Default` | Uses each field's default. Only a record can derive it. |
| `serialization::Serialize`, `serialization::Deserialize` | See below. |
| `Copyable`, `Plain` | Nothing: an opaque type declares that it can be copied, explicitly or implicitly (see [Copying](#copying)). |

- Every field already has the trait.
- A derived trait needs the traits it requires. Deriving `Ordered` or `Hash`
  also needs `Equal` to be derived, not written by hand.
- A generic type has a derived trait only where its parameters do:
  `Option[Value]` is `Equal` only when `Value` is.
- A derived implementation satisfies the trait's laws. A hand-written `impl`
  proves them.
- A derived `Serialize` writes a record as its fields by name, in declaration
  order, a variant with no fields as its name, and a variant with fields as a
  record of them under its name. A derived `Deserialize` accepts a missing
  field that has a default, and reads a missing field of type `Option` as
  `None`. A format may rename every field, as
  `serialization::Names.CamelCase` does.

Every type has debug output, which `echo` and the test runner use. Nothing is
derived for it.

### Method lookup

- A trait's methods are called with a dot, without importing the trait.
- A call with a dot finds the type's own methods, and the methods of the
  traits it implements that come from the standard library, the calling
  package, or a package the calling package lists in its manifest.
- If two of those traits give a type methods with the same name, a call with
  a dot is a compile error, whatever their modes. The call is written in
  full: `Ordered.compare(first, second)`. A trait and a trait it requires are
  the exception.
- A type's own method and a method of a trait it implements cannot be the
  same method: the same name, taking `self` in the same mode. An `impl` that
  would give a type such a method is a compile error. An `impl` in the type's
  own package can give it another version of a method it has, by writing that
  method. A method the `impl` leaves to the body its trait provides, and any
  method of an `impl` in another package, cannot use a name the type's
  methods have.

### Values of any type with a trait

`any Trait` is the type of a value of some type that implements the trait:

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
  once, which `cost` clauses count.
- `any` names exactly one trait, and fixes every associated type of it:
  `any Cursor[Element = Int64]`.
- `any` fixes every associated capability set of its trait to the empty set.
  So `any value` is an error for a value whose type has a capability in such
  a set, as the cursor of a method with a `uses` clause has.
- A method can be called through `any` if it takes `self`, `mut self`, or
  `own self`, has no generic parameters of its own, and does not take or
  return `Self`. A call of any other method is a compile error.
- A call through `any` is proven against the trait's contract.
- An `any` value cannot be tested for, or converted back to, its type.

## Tests

```ebnf
test = "test" plain_string [ "uses" capability_list ] block ;
```

`plain_string` is a `STRING` with no interpolation.

```truss
test "config loads with defaults" {
  let disk = files::MemoryFiles.new().with_text(Path.new("app.toml"), contents: "")
  let config = provide disk, log::DiscardLog() {
    load_config(Path.new("app.toml"))
  }
  assert config == Ok(Config.default())
}
```

A test provides every capability its code uses, except `Panic`, unless it
declares them with `uses`. A test with `uses` is *external*: it gets the real
implementations of exactly those capabilities, as `main` does.

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

- A test without `uses` is deterministic, and its result is kept until its
  code changes. An external test runs every time the test suite runs.
- An external test gets exactly the capabilities it declares, with no isolation that it
  does not provide itself.
- A failed test is never retried.
- A failed `assert` ends the test as failed. After an `assert`, the rest of
  the test can rely on the asserted fact.
- A test does not wait for proofs. A test build checks, when the test runs,
  every primitive operation that could fail, such as an index, a division,
  or an addition that could overflow, and a failed check ends the test as
  failed and names the operation. A `requires` clause is not run.
- A panic fails only the test it happens in. No test expects a panic.
- A test that does not finish within the project's time limit fails (see
  [PACKAGES.md](PACKAGES.md#projects)).

## Proofs

Most facts are proven automatically. A proof is written only where the
prover needs help, in ordinary Truss.

```ebnf
theorem   = "theorem" LOWER_NAME [ generics ] parameters { clause } block ;
law_proof = "proof" path_type "." LOWER_NAME "for" type_head block ;
```

Everything a program promises is proven before it is built: `requires` and
`ensures` clauses, cost clauses, type invariants, laws, loop invariants, and
the safety of every operation that could fail. There is no `assume`; the
only gap in a proof is `todo`.

### Theorems

A `theorem` is a named fact with its proof. Its `requires` clauses are its
assumptions, its `ensures` clauses its conclusions, and its body the proof:

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

- An empty body asks the prover to prove the theorem alone.
- Calling a theorem makes its `ensures` available at that point. After
  `reverse_twice(rest)`, the prover knows that `rest.reverse().reverse()`
  equals `rest`.
- A theorem that calls itself on smaller input is a proof by induction, and
  its `decreases` clause proves that the recursion ends.
- A theorem's body uses calls, `let`, `match`, `if`, and `assert`.

### Proof blocks

A `proof { }` block in a function body gives the prover hints at that point:

```truss
fn SortedList[Element: Ordered].insert(mut self, item: own Element) {
  let position = self.items.partition_point(fn(existing) { existing < item })
  mut self.items.insert_at(position, item)
  proof {
    insert_at_partition_point_keeps_sorted(old(self.items), position, item)
  }
}
```

A proof block holds the statements a theorem's body can hold, and is removed from the
compiled program.

### Proving laws

A `proof` definition supplies the proof of a law for one implementation:

```truss
proof Monoid.associative for Int64 {
  wrapping_add_is_associative()
}
```

- The body is checked as the law's own body is: it names the law's
  parameters, which are read-only, `Self` is the type that the proof is for,
  and the law's `requires` hold in it.
- A law that holds by induction is proven by a theorem that calls itself,
  which the proof calls with the law's values:

  ```truss
  proof Ordered.transitive for Path {
    compare_is_transitive(first, second: second, third: third, from: 0)
  }
  ```

- A proof for a generic `impl` names the type as the `impl` does, by a
  `type_head` with its parameters and their bounds, and is proven once for
  every type the `impl` is for. `for Self` and `for any Shown` are syntax
  errors.

  ```truss
  proof Ordered.transitive for Box[Item: Ordered] {
    box_order_is_transitive(first, second: second, third: third)
  }
  ```

- A law proof takes no visibility keyword.

### Bodies and contracts in proofs

The prover knows a function by its contract, or by its definition.

- **A functional body is the function's definition** when the function is
  pure and has a `time` clause. A functional body uses `let`, `if`, `match`,
  `is`, calls, fields, building values, `with`, operators, and quantifiers.
  It has no `var`, no assignment, and no loop, and passes nothing `mut` or
  `own`. The prover then reads `is_sorted(items)` below as exactly its
  quantifier.
- **Every other function is known by its contract,** its `requires` and
  `ensures`.
- A definition is read only where everything it reads is visible: a body that
  reads the fields of an opaque type is a definition inside the type's
  package, and elsewhere the function is known by its contract. In another
  package, a proof reads only the contract, unless the function is
  `transparent` (see [Visibility](#visibility)).
- A function with a `requires` is defined only where its `requires` holds.
- A trait's provided method is read everywhere, since an `impl` in any
  package inherits it.

### Writing specifications

A *specification* is a `requires`, `ensures`, `decreases`, or `cost` clause,
an invariant, a law, or a proof.

- **A function called in a specification is pure,** with no `uses` at all,
  not `Panic` either, and has a `time` clause. A function defined only for
  some inputs says so with `requires`, which every specification that calls
  it meets.
- **Every specification is well defined:** each call in it meets its
  callee's `requires`, and each index is in bounds.
- **`&&`, `||`, `==>`, and `if` read from left to right,** so the right side
  can rely on the left: in `index < items.length() && items[index] > 0`,
  `items[index]` is in bounds.

| Form | Meaning |
|---|---|
| `forall index in 0..items.length() => items[index] >= 0` | True for every value in a range or a collection |
| `forall value: Int64 => value + 0 == value` | True for every value of a type |
| `exists item in items => item == target` | True for at least one value |
| `index < split ==> items[index] < pivot` | Implication: when the left side is true, so is the right |
| `old(self.items)` | A value as it was when the function was called |
| `identical(result, self.model()[key])` | The same value, for values of any one type, whether or not it implements `Equal` |
| `assert condition` | In a proof: a fact the prover shows, which can then be used |

- `==` is always the type's `Equal`. `identical` is identity.
- A quantifier over a range or a collection is an expression, and can be
  used in code too. It runs as a loop that stops as soon as the answer is
  known, and costs as much as such a loop. Its body may rely on the bound
  name being in its range, and uses no capabilities:

  ```truss
  fn is_sorted[Element: Ordered](items: Slice[Element]) -> Bool
    cost time finite
  {
    forall i in 1..items.length() => items[i - 1] <= items[i]
  }
  ```

- A quantifier over a type, such as `forall value: Int64`, and `==>` cannot
  run, so they appear only in specifications and in the bodies of functions
  for specifications only.
- A quantifier's body runs to the end of the expression, so a quantifier is
  only the last operand of `&&`, `||`, or `==>`. In
  `requires count > 0 && forall i in 0..count => items[i] > 0`, the body is
  `items[i] > 0`.
- `a ==> b` binds more loosely than `&&` and `||`, so `a ==> b || c` is
  `a ==> (b || c)`, and does not chain. Outside specifications, write
  `!a || b`.

Integer arithmetic in specifications is exact. It is done on `Integer`, the
mathematical integers, a prelude type that exists only in specifications:

- Every built-in integer type is a subset of `Integer`. In a specification,
  arithmetic on integers gives an `Integer`, and comparisons can mix integer
  types: `requires count <= items.length()` works with a `UInt32` count.
- An `Integer` can stand where a built-in integer is expected, as in
  `items[i + 1]`, and the prover shows that it fits.
- A function whose signature mentions `Integer`, or another type that exists
  only in specifications, such as `fn sum(items: Slice[Int64]) -> Integer`,
  is for specifications only. It is called only from specifications and
  never compiled. Its body is a specification, so its arithmetic is exact,
  and it may use `==>` and quantifiers over a type.

Float arithmetic in specifications follows IEEE 754, as in code.

#### Mathematical collections

Specifications describe collections through mathematical values that exist
only in specifications:

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

`List` and `Slice` are modeled by a `Sequence` of their elements, `String`
by the `Sequence[UInt8]` of its bytes, `Map` by a `FiniteMap` and the order
of its keys, and `Set` by a `FiniteSet` and its order. Contracts compare
models:

```truss
fn List[Element].push(mut self, item: own Element)
  ensures identical(self.model(), old(self.model()).append(item))
  cost amortized time O(1)
{
  todo
}
```

- `model()` can be called only in specifications.
- The mathematical types have structural equality, so two lists with
  identical models are interchangeable in a proof.
- Their operations are in `standard::specification`.
- A `[...]` literal is one of these types where one is expected, as in
  `ensures identical(self.model(), [])`.

## Unfinished code

`todo` stands for code that is not written yet: an expression of any type, a
whole function body, or a type's definition:

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

- For each `todo`, the compiler reports the type it must have and the names
  in scope, such as "hole of type `String`; in scope: `report: Report`,
  `header: String`".
- Code with holes is type-checked and proven. Callers are checked against
  the signature of an unfinished function.
- `truss build` refuses a program whose `main` can reach a `todo`, including
  one in a proof.
- A test that reaches a `todo` is reported as incomplete, not failed.
- A type defined as `todo` can be named and passed around, but its contents
  cannot be used.

## Debug output

`echo` shows a value while the code runs, and returns it unchanged:

```truss
fn score(player: Player) -> Int64 {
  let base = echo player.wins * 3
  base.saturating_add(echo bonus(player))
}
```

- It records the value's debug output with the file, line, and expression
  text.
- It needs no `uses`. `echo expr` has the type of `expr`, and proofs and cost
  clauses treat it as `expr`.
- In tests, the output is attached to the test's report, grouped by parallel
  branch or task. In other runs, it goes to standard error.
- It is not allowed in proofs.
- `truss build` refuses a program whose `main` can reach an `echo`, and a
  package that contains one cannot be published.

## Modules and visibility

`use` imports a module, never individual names. Names from the module are
then written after the module's name and `::`:

```truss
use standard::json
use standard::url

let settings = json::parse(text)?
let url = url::parse(raw)?
let fallback = json::Value.Null
```

- Every name that is not local or from the prelude is written with its
  module.
- There are no import aliases.
- A full path such as `standard::json::parse(text)` works without a `use`.
  Importing two modules with the same last name is a compile error.
- `use` lines come before every definition in a file, and `truss fmt` sorts
  them. A `use` whose module the file never names is a compile error.

### Module paths

Each `.truss` file of a package is a module. Its path is the package's name,
then the directories it is in, then its file name:

| File in the `weather` package | Module |
|---|---|
| `forecast.truss` | `weather::forecast` |
| `forecast/hourly.truss` | `weather::forecast::hourly` |

- Every path starts with a package name: `standard`, a dependency's name, or
  the package's own name. A file names another file of its own package the
  same way: `use weather::forecast::hourly`.
- A registry package's name has its owner in it, so a path into one starts
  with two parts: `use acme::geometry::vector` imports the module `vector`
  of the package `acme::geometry`. A path holds no version.
- There are no relative paths.
- A directory is not a module. `forecast.truss` and a `forecast/` directory
  can sit side by side.
- File and directory names are `lower_snake_case` names.
- The modules of a package can use each other in a cycle. Packages cannot
  depend on each other in a cycle.

The standard library's root module is `standard`.

### The prelude

A fixed *prelude* is in scope in every file without a `use`. Its names are
all `UpperCamelCase`:

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
- the standard capabilities, and the types that signatures are written with
  everywhere: `Path`, `Instant`, `Duration`, and `SystemError`

Everything else is imported with `use`, including `core::Pair`,
`core::Indexed`, and `text::Literal`. A project cannot define its own
prelude, and no definition can have a prelude name. The prelude changes only
with a new language version.

### Visibility

| Keyword | Visible to |
|---|---|
| *(none)* | The same file only. This is the default. |
| `internal` | The whole package. |
| `public` | Every package. |

An `impl`, a test, and a law proof take no visibility keyword.

A public type can hide its contents with `opaque`, which is allowed only
before `public type`:

```truss
public type Point(x: Float64, y: Float64)

public opaque type SqlQuery(text: String, parameters: List[SqlParameter])
```

`Point` makes its name and fields public. `SqlQuery` makes only its name
public: outside its package, it can be named and passed around, but its
fields cannot be read, built, updated, or matched on. Visibility is set for a
type as a whole, never for one field.

- A public function's signature cannot mention a private or `internal` type,
  and neither can a public type's fields, unless the type is opaque.
- A public function's `requires`, `ensures`, and `cost` clauses call no
  private or `internal` function and name no such constant. The same holds
  for a method of a public trait or capability, and for a method of an
  `impl` that other packages can use.

A public function can show its body to the proofs of other packages with
`transparent`:

```truss
public transparent fn is_sorted(items: Slice[Int64]) -> Bool
  cost time O(items.length())
{
  forall index in 1..items.length() => items[index - 1] <= items[index]
}
```

- A `transparent` function's body is part of the package's interface, as
  its signature is.
- The body calls only public functions and names only public constants, as a
  public contract does. It can read a field that other packages cannot see.
- Only a function or a method of a type can be `transparent`, and only one
  whose body can be a definition: it has a `time` clause, no `uses` clause,
  and no `mut` parameter, and it returns its result.

## No foreign code

Truss code cannot call functions written in other languages. There is no
`extern` declaration and no raw pointer type. The standard library reaches
the operating system through the compiler, in ways that are not part of the
language and that no other package can use. So the standard library is the
only code that differs between operating systems; other code asks which one
it runs on through the `Environment` capability.

## Constructs resolved after parsing

The parser builds the same tree for some constructs that mean different
things. These are decided afterward, without changing the tree's shape:

| Construct | Decided by | How |
|---|---|---|
| `name[...]` | Name resolution | Type arguments if `name` is a generic function, a type, or a trait; otherwise an index. For a method, type checking decides. |
| A bare `LOWER_NAME` in a pattern | Name resolution | The constant if one with that name is in scope; otherwise a new binding. |
| A bare argument after the first | Type checking | Names a parameter or field of the callee; otherwise an error. |
| Whether an expression after `mut` or `own` starts with a place | Name resolution | It starts with a variable, a parameter, `self`, or a constant, followed by fields and indexes. |
| A variant in a pattern | Type checking | Looked up in the type of the matched value. |
| A method call or field | Type checking | Looked up in the type of the receiver. |
| An `impl` of a trait with type parameters | Type checking | Chosen by the argument types, inferred first, with a literal operand taking the type of the other operand. |
| The cost words, `log`, `power`, `result`, `old` | The parser and name resolution | Names to the lexer. The parser checks their spelling where a `cost` clause expects them, and name resolution gives `log`, `power`, `time(...)`, `calls(...)`, `result`, and `old` their meaning in specifications. |
| The expected type of `[...]` | Type checking | `List` unless an `Array`, a `Set`, or a type of specifications is expected. |

## Ambiguities in the grammar

The grammar has two shift/reduce conflicts. Both are resolved by shifting,
and the test of `grammar/truss.mly` checks that Menhir finds exactly these:

- **`else` after `let pattern = if ... { } else { }`.** Shifting attaches the
  `else` to the `if`. The rule that the expression of a `let ... else` does
  not end with `}` is checked after parsing.
- **`{` after `return`.** Shifting makes the block the value being returned.

The next token decides every other construct, including labels against
values that begin with a name, list literals against map literals, and
lambdas against function types.
