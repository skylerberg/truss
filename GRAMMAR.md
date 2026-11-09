# Truss Grammar

This document gives the grammar of Truss precisely, for building the lexer and
parser. [SYNTAX.md](SYNTAX.md) explains each construct and
[DESIGN.md](DESIGN.md) gives the reasons. Where this document and SYNTAX.md
disagree, one of them has a mistake, and the disagreement should be fixed
rather than worked around.

## Notation

The grammar is written in EBNF:

| Notation | Meaning |
|---|---|
| `rule = ... ;` | Defines `rule` |
| `"fn"` | The literal token `fn` |
| `UPPER_NAME` | A token class, defined in the lexical grammar |
| `a b` | `a` followed by `b` |
| `a \| b` | `a` or `b` |
| `[ a ]` | `a`, optional |
| `{ a }` | `a`, zero or more times |
| `( a )` | Grouping |

`list(item)` is shorthand for a comma-separated list that may be empty and
may end with a comma:

```ebnf
list(item) = [ item { "," item } [ "," ] ] ;
```

`lines(item)` is shorthand for items separated by line breaks, as inside
braces. The lexer never puts a `NEWLINE` right after `{` or right before `}`,
and never two in a row (see [Line breaks](#line-breaks)):

```ebnf
lines(item) = [ item { NEWLINE item } ] ;
```

## Lexical grammar

### Source text

A source file is UTF-8. A byte order mark may appear only as the first
character, and is ignored. A carriage return followed by a line feed is read as
a line feed; a carriage return on its own is an error. Tab and space are
whitespace.

Every Unicode property this grammar uses comes from the Unicode version named
by the language version (see [SYNTAX.md](SYNTAX.md#source-files)).

These characters are an error anywhere in a file, including inside string
literals:

- U+061C, U+200E, U+200F, U+202A to U+202E, U+2066 to U+2069
- U+0000 to U+001F except tab and line feed, U+007F, U+0080 to U+009F
- every other character with the Unicode property `Default_Ignorable_Code_Point`,
  except U+200C, U+200D, and the variation selectors

### Tokens

```ebnf
token = UPPER_NAME | LOWER_NAME | "_" | keyword
      | INTEGER | FLOAT | STRING | TAGGED_STRING
      | punctuation | NEWLINE ;
```

Whitespace and line feeds separate tokens. Line feeds become `NEWLINE` tokens
only as described in [Line breaks](#line-breaks).

### Names

```ebnf
name_start    = ? a character with the Unicode property XID_Start ? ;
name_continue = ? a character with the Unicode property XID_Continue ? ;
raw_name      = name_start { name_continue } ;
```

A `raw_name` that is a reserved keyword is that keyword. Otherwise:

- It is an `UPPER_NAME` if its first character has the Unicode general category
  `Lu` or `Lt`. It must not contain `_`.
- Otherwise it is a `LOWER_NAME`. It must contain no character of category
  `Lu` or `Lt`, must not start or end with `_`, and must not contain `__`.
- `_` on its own is the token `"_"`.

Every name must be in Unicode Normalization Form C, must contain only
characters with `Identifier_Status=Allowed` in UTS #39, and must meet UTS
#39's "Moderately Restrictive" level (Latin plus at most one other script, and
never Latin with Cyrillic or Greek). The lexer checks these, since each
depends only on the name. After lexing, a name
containing a character outside ASCII must not be confusable with another name
visible in the same package. Two names that are both entirely ASCII are never
compared.

### Keywords

Reserved everywhere:

```text
any assert break capability continue cost decreases derives echo else ensures
exists false fn for forall if impl in indirect internal invariant is law let match mut
opaque own parallel proof provide public requires return self Self test
theorem todo trait true type unreachable use uses var while with yield yields
```

Reserved for later use, and an error if written:

```text
as async await const defer extern loop macro static unsafe where
```

The lexer has no contextual keywords. These words are ordinary names to it,
`LOWER_NAME`s except `O`, which is an `UPPER_NAME`. The parser recognizes
them by their spelling in the positions shown in the syntactic grammar, and
name resolution gives the rest their meaning:

```text
amortized time allocations allocated_bytes calls O finite potential
log power result old
```

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

digit        = "0" ... "9" ;
nonzero_digit = "1" ... "9" ;
hex_digit    = digit | "a" ... "f" | "A" ... "F" ;
binary_digit = "0" | "1" ;
octal_digit  = "0" ... "7" ;
```

- A `FLOAT` needs a digit right after its `.`, so `1..2` lexes as `1`, `..`,
  `2`, and `1.max` as `1`, `.`, `max`.
- A number literal is never directly followed by a name character. `3u8` is
  an error.
- `-` is never part of a literal.
- The whole-number part of a decimal literal has no leading zero, so `0755`
  and `007` are errors, with fixes to `0o755` and `755`. The digits after
  the `.` and in an exponent may start with zeros: `0.05`, `1.0e-09`.

### String literals

A string literal is a sequence of text pieces and interpolations. The lexer
returns it as one `STRING` token, with each interpolation already split into
the tokens of its expression.

```ebnf
STRING        = ordinary_string | raw_string ;
TAGGED_STRING = UPPER_NAME string_start ;
```

`TAGGED_STRING` is an `UPPER_NAME` with no whitespace between it and the
string. A module path before the tag, as in `database::SqlQuery"..."`, is
ordinary tokens: `database`, `::`, then the `TAGGED_STRING`.

**Ordinary strings** begin and end with `"` on the same line:

```ebnf
ordinary_string = '"' { ordinary_char | escape | interpolation } '"' ;
ordinary_char   = ? any character except '"', '\', and a line feed ? ;
escape          = '\n' | '\t' | '\r' | '\0' | '\\' | '\"' | '\${'
                | '\u{' hex_digit [ hex_digit ] [ hex_digit ] [ hex_digit ]
                        [ hex_digit ] [ hex_digit ] '}' ;
```

A `\u{...}` escape must name a Unicode scalar value. Any other `\` sequence is
an error.

**Raw strings** have no escapes:

```ebnf
raw_string   = { "$" } quotes raw_body quotes ;
quotes       = '"""' { '"' } ;
```

- The opening and closing delimiters have the same number of quotes, at
  least three.
- If the opening delimiter is followed by a line feed, the string is
  multi-line. Spaces and tabs between the delimiter and the line feed are
  ignored. The closing delimiter must be on a line of its own, preceded only
  by whitespace, and that whitespace is the indentation. Every other line
  must start with exactly that whitespace, which is removed. A line that holds
  only whitespace and does not start with the indentation is an empty line.
  The line feeds after the opening delimiter and before the closing one are
  not part of the string.
- Otherwise the string is on one line, and its text cannot start or end with
  `"`.
- A run of more quotes than the delimiter is an error.

**Interpolation.** In an ordinary string, and in a raw string opened with no
`$`, an interpolation starts at `${`. In a raw string opened with *n* `$`
characters, it starts at *n* `$` characters followed by `{`, and any `$`
characters before those are text.

```ebnf
interpolation = "${" expression "}" ;
```

- The lexer counts `{` and `}` inside the interpolation, and lexes string
  literals inside it recursively, so `"${names.join(", ")}"` is one string.
- An interpolation cannot contain a line feed, and cannot be empty.

### Punctuation

```text
(  )  [  ]  {  }  ,  :  ::  .  ..  ..=  ->  =>  ?  |
=  +=  -=  *=  /=  %=  &=  |=  ^=  <<=  >>=
+  -  *  /  %  ==  !=  <  <=  >  >=  &&  ||  ==>  !  &  ^  ~  <<  >>
```

The lexer uses the longest match.

### Rejected sequences

These are errors, each with its own message and fix (see
[SYNTAX.md](SYNTAX.md#syntax-from-other-languages)):

```text
//  /*  #  ;  '  `  @  ++  --  ===  !==
```

`--` is rejected even where it could be read as two negations.

### Line breaks

A line feed becomes a `NEWLINE` token exactly when the token before it can end
a statement and the token after it can begin one, outside `(` and `[`. This is
Scala's rule. In detail, the lexer keeps a stack of open brackets: `(`, `[`,
and `{`. An interpolation is lexed on its own and cannot contain a line feed,
so it needs no entry.

1. While the innermost open bracket is `(` or `[`, line feeds are skipped.
2. Otherwise, a line feed becomes a `NEWLINE` token when both of these hold:
   - the last token before it **can end a statement**: a name, `_`, a number
     or string literal, `)`, `]`, `}`, `?`, `true`, `false`, `self`, `Self`,
     `todo`, `unreachable`, `break`, `continue`, `return`;
   - the first token after it **can begin a statement**: a name, `_`, a
     number or string literal, `(`, `[`, `{`, `-`, `!`, `~`, a reserved word,
     or one of the keywords `any`, `assert`, `break`, `capability`,
     `continue`, `echo`, `exists`, `false`, `fn`, `for`, `forall`, `if`,
     `impl`, `internal`, `law`, `let`, `match`, `mut`, `own`, `parallel`,
     `proof`, `provide`, `public`, `return`, `self`, `Self`, `test`,
     `theorem`, `todo`, `trait`, `true`, `type`, `unreachable`, `use`, `var`,
     `while`, `yield`.
3. Several line feeds in a row produce at most one `NEWLINE`.
4. At the end of the file, a `NEWLINE` follows the last token if it can end a
   statement.

Every other token continues the line before it: `.`, `,`, `:`, `::`, `)`,
`]`, `}`, `?`, `|`, `=>`, `->`, `=` and the compound assignments, the binary
operators other than `-`, `..`, `..=`, and the keywords `cost`, `decreases`,
`derives`, `else`, `ensures`, `in`, `indirect`, `invariant`, `is`, `opaque`, `requires`,
`uses`, `with`, and `yields`. So no `NEWLINE` ever comes before a closing `}`,
and statements, `match` arms, and members are separated by `NEWLINE`s, not
ended by them.

The parser skips a `NEWLINE` immediately before a `{` that must open a body.

## Syntactic grammar

### Files and definitions

```ebnf
file       = { use NEWLINE } { definition NEWLINE } ;
use        = "use" module_path ;
module_path = LOWER_NAME { "::" LOWER_NAME } ;

definition = [ visibility ] ( function | type_definition | trait | impl
                            | capability | constant | test | theorem
                            | law_proof ) ;
visibility = "public" [ "opaque" ] | "internal" ;
```

`opaque` is allowed only before `type`.

### Functions

```ebnf
function      = "fn" function_name [ generics ] parameters [ result ]
                { clause } body ;
function_name = LOWER_NAME | type_head "." LOWER_NAME ;
type_head     = [ module_path "::" ] UPPER_NAME [ generics ] ;

parameters    = "(" list(parameter) ")" ;
parameter     = [ mode ] "self"
              | LOWER_NAME ":" [ mode ] type [ "=" expression ] ;
mode          = "mut" | "own" ;

result        = "->" type | "yields" [ mode ] type ;
body          = block ;
```

- In a `type_head`, the generic parameters are the type's own, with any
  bounds the method needs: `fn List[Element: Ordered].sort(mut self)`.
- A default is a constant expression and cannot refer to other parameters.
- `self` may only be the first parameter, and only in a method.

### Clauses

```ebnf
clause        = "uses" capability_list
              | "requires" expression
              | "ensures" expression
              | "decreases" expression { "," expression }
              | "cost" cost ;
capability_list = path_type { "," path_type } ;

cost          = [ "amortized" ] resource bound ;
resource      = "time" | "allocations" | "allocated_bytes"
              | "calls" "(" call_target ")" ;
call_target   = LOWER_NAME | path_type [ "." LOWER_NAME ] ;
bound         = "O" "(" expression ")" | "finite"
              | ( "<=" | "==" ) expression ;
```

- `"amortized"`, `"time"`, `"allocations"`, `"allocated_bytes"`, `"calls"`,
  `"O"`, `"finite"`, and `"potential"` stand for a `LOWER_NAME` or
  `UPPER_NAME` with that spelling, not for a keyword token (see
  [Keywords](#keywords)).
- `uses` and `decreases` appear at most once. The others may repeat.
- `finite` is allowed only for `time`.
- In a `cost` clause, `time(...)`, `calls(...)`, `log(...)`, and
  `power(..., ...)` inside expressions are cost-only functions, and `result`
  names the return value.

### Types

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

- A `type_clause` after the last variant belongs to the whole type.
- The `|` before the first variant is optional. `truss fmt` leaves it out when
  the type fits on one line, and otherwise puts each variant on its own line
  starting with `|`.
- A record's field order is significant only for a derived `Ordered`.
- `indirect` stores a variant's fields on the heap. Every cycle of types that
  contain each other, other than through a collection, must pass through an
  `indirect` variant; type checking reports a cycle that does not.

```ebnf
type        = path_type
            | "Self" [ "." UPPER_NAME ]
            | UPPER_NAME "." UPPER_NAME
            | "any" path_type
            | function_type
            | "(" function_type { function_type_clause } ")" ;

path_type   = [ module_path "::" ] UPPER_NAME [ type_arguments ] ;
type_arguments = "[" type_argument { "," type_argument } [ "," ] "]" ;
type_argument  = type | INTEGER | LOWER_NAME | UPPER_NAME "=" type ;

function_type        = "fn" "(" list([ mode ] type) ")" [ "->" type ] ;
function_type_clause = "uses" capability_list | "cost" cost ;
```

- `UPPER_NAME "." UPPER_NAME` names an associated type of a generic
  parameter, such as `Items.Element`.
- An `INTEGER` or `LOWER_NAME` argument is the value of a `USize` generic
  parameter, as in `Array[UInt8, 32]` or `Array[Int64, count]`. It cannot be
  an expression.
- `UPPER_NAME "=" type` constrains an associated type in a bound or after
  `any`, as in `Iterable[Element = Int64]` or `any Cursor[Element = Int64]`.
- A function type with clauses must be in parentheses. The clauses of a
  function type cannot mention parameters.

```ebnf
generics         = "[" generic_parameter { "," generic_parameter } [ "," ] "]" ;
generic_parameter = UPPER_NAME [ ":" bound ]
                  | LOWER_NAME ":" type
                  | "capability" UPPER_NAME ;
bound            = path_type { "+" path_type } ;
```

A `LOWER_NAME` generic parameter is a value, and its type must be `USize`.

### Traits, implementations, and capabilities

```ebnf
trait        = "trait" UPPER_NAME [ generics ] [ ":" bound ]
               "{" lines(trait_member) "}" ;
trait_member = signature [ body ]
             | "type" UPPER_NAME [ ":" bound ]
             | "law" LOWER_NAME parameters { "requires" expression } block ;
signature    = "fn" LOWER_NAME [ generics ] parameters [ result ] { clause } ;

impl         = "impl" path_type "for" type_head [ "uses" capability_list ]
               "{" lines(impl_member) "}" ;
impl_member  = function_member | "type" UPPER_NAME "=" type ;
function_member = signature body ;

capability   = "capability" UPPER_NAME
               "{" lines(signature) "}" ;
```

### Constants, tests, theorems, and proofs

```ebnf
constant  = "let" constant_name ":" type "=" expression ;
constant_name = LOWER_NAME | type_head "." LOWER_NAME ;

test      = "test" plain_string [ "uses" capability_list ] block ;
theorem   = "theorem" LOWER_NAME [ generics ] parameters { clause } block ;
law_proof = "proof" path_type "." LOWER_NAME "for" type block ;
```

- A constant's expression is a constant expression: literals, arithmetic,
  other constants, and records, variants, lists, maps, arrays, sets, and
  strings built from those.
- `plain_string` is a `STRING` with no interpolation.

### Statements and blocks

```ebnf
block     = "{" lines(statement) "}" ;

statement = "let" pattern [ ":" type ] "=" expression [ "else" block ]
          | "var" pattern [ ":" type ] "=" expression [ "else" block ]
          | expression [ assignment_operator expression ]
          | "for" pattern "in" expression { loop_clause } block
          | "while" expression { loop_clause } block
          | "parallel" block
          | "parallel" "for" pattern "in" expression { loop_clause } block
          | "proof" block
          | "assert" expression
          | "yield" expression ;

assignment_operator = "=" | "+=" | "-=" | "*=" | "/=" | "%="
                    | "&=" | "|=" | "^=" | "<<=" | ">>=" ;
loop_clause = "invariant" expression | "decreases" expression { "," expression } ;
```

- The left side of an assignment must be a place.
- Every name a `var` pattern binds is mutable.
- In `let ... else` and `var ... else`, the expression must not end with `}`. Write
  `let Some(x) = (if ready { a } else { b }) else { ... }` with parentheses.
- `assert` is allowed only in tests, theorems, and proofs. `proof` blocks are
  allowed only in function bodies.
- `parallel` and `parallel for` are statements; each statement directly inside
  a `parallel` block is a branch.
- `yield mut part` is `yield` followed by the expression `mut part`, whose
  `mut` marks the place being lent.

### Expressions

Precedence, loosest first. Each rule below names the operators of one level.
Where the grammar offers no way to combine two operators, they need
parentheses.

```ebnf
expression = "echo" expression
           | "return" [ expression ]
           | implication
           | bitwise ;

implication = [ logical "==>" ] ( logical | quantified ) ;
quantified = quantifier
           | comparison { "&&" comparison } "&&" quantifier
           | comparison { "||" comparison } "||" quantifier ;
quantifier = ( "forall" | "exists" ) binder "=>" expression ;
binder     = pattern "in" expression | LOWER_NAME ":" type ;

logical    = comparison { "&&" comparison }
           | comparison "||" comparison { "||" comparison } ;

comparison = range [ comparison_operator range ]
           | range "is" pattern ;
comparison_operator = "==" | "!=" | "<" | "<=" | ">" | ">=" ;

range      = additive [ ( ".." | "..=" ) additive ] ;
additive   = multiplicative { ( "+" | "-" ) multiplicative } ;
multiplicative = prefix { ( "*" | "/" | "%" ) prefix } ;

bitwise    = prefix "&" prefix { "&" prefix }
           | prefix "|" prefix { "|" prefix }
           | prefix "^" prefix { "^" prefix }
           | prefix ( "<<" | ">>" ) prefix { ( "<<" | ">>" ) prefix } ;

prefix     = ( "-" | "!" | "~" ) prefix
           | ( "mut" | "own" | "any" ) postfix
           | postfix ;
```

- A `bitwise` expression is a whole expression. To use one as an operand of
  anything else, put it in parentheses: `(flags & mask) != 0`.
- `&&` and `||` cannot be mixed without parentheses, and comparisons,
  `is`, and ranges do not chain.
- `return` and `echo` take everything after them. A `{` right after
  `return`, on the same line, starts the value being returned.
- `forall`, `exists`, and `==>` are allowed only in specifications.
- A quantifier's body runs to the end of the expression, so a quantifier can
  only be the last operand of `&&`, `||`, or `==>`. In
  `a && forall x in s => p || q`, the body is `p || q`.
- `==>` does not chain: `a ==> b ==> c` needs parentheses.

```ebnf
postfix    = primary { "." LOWER_NAME
                     | "." UPPER_NAME
                     | "[" brackets "]"
                     | "(" list(argument) ")"
                     | "?"
                     | "with" "(" list(update) ")" } ;

brackets   = expression
           | [ additive ] ( ".." | "..=" ) [ additive ]
           | type_argument { "," type_argument } [ "," ] ;
argument   = [ LOWER_NAME ":" ] expression ;
update     = LOWER_NAME { "." LOWER_NAME } ":" expression
           | LOWER_NAME ;
```

- In an expression, the brackets after a name hold expressions, which cover
  type names and their arguments, such as `List[String]` and
  `Array[UInt8, 32]`, and associated-type constraints. A function type cannot
  appear there, because `fn(...)` would be read as a lambda. Give such a type
  through an annotation instead.
- `name[...]` is parsed the same way whether it indexes or gives type
  arguments. Name resolution decides which (see
  [What the grammar leaves to later stages](#what-the-grammar-leaves-to-later-stages)).
- A range with a missing start or end is allowed only directly in brackets,
  as in `items[2..]`.
- An `argument` without a label is either the first argument, or a bare name
  (with an optional mode) that matches a parameter or field.

```ebnf
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

map_entry  = expression ":" expression ;
lambda     = "fn" "(" list(pattern) ")" block ;
if         = "if" expression block [ "else" ( if | block ) ] ;
match      = "match" expression { "," expression }
             "{" lines(arm) "}" ;
arm        = pattern { "," pattern } [ "if" expression ] "=>" statement ;
provide    = "provide" expression { "," expression } block ;
```

- `break` and `continue` are allowed only in loops. They, `return`, and
  `unreachable` have type `Never`, so they can be the body of a `match` arm.
- A `match` arm has one pattern for each value after `match`.
- An arm's body is a statement, as a line of a block is, so it can be an
  assignment, a `yield`, an `assert`, or a loop. When the `match` is used as
  a value, an arm whose body is not an expression has type `Unit`.
- `[]` is an empty list, array, or set, and `[:]` is an empty map, depending
  on the expected type.

### Patterns

```ebnf
pattern          = pattern_primary { "|" pattern_primary } ;
pattern_primary  = "_"
                 | range_end [ ( ".." | "..=" ) range_end ]
                 | [ module_path "::" ] UPPER_NAME [ pattern_fields ]
                 | pattern_fields ;
range_end        = literal_pattern | constant ;
literal_pattern  = [ "-" ] INTEGER | "true" | "false" | plain_string
                 | [ module_path "::" ] TAGGED_STRING ;
constant         = LOWER_NAME
                 | module_path "::" LOWER_NAME
                 | [ module_path "::" ] UPPER_NAME "." LOWER_NAME ;
pattern_fields   = "(" list(pattern_field) ")" ;
pattern_field    = LOWER_NAME ":" pattern | pattern | ".." ;
```

- `..` may only be the last field.
- A bare `LOWER_NAME` on its own is a constant if one with that name is in
  scope, and otherwise binds. As the end of a range, a name must be a
  constant, as in `0..=max_port` or `UInt16.minimum..=UInt16.maximum`.
- A range pattern needs both ends. Open-ended ranges appear only in
  brackets.
- A pattern with no type name, as in `(index, element)`, matches a record.
- Float literals are not patterns.

## Checking the grammar

[`grammar/truss.mly`](grammar/truss.mly) is this grammar written for the
Menhir parser generator. Running `menhir --explain truss.mly` in that
directory checks it. Two shift/reduce conflicts remain, and both are resolved
by shifting, which is the intended reading:

- **`else` after `let pattern = if ... { } else { }`.** Shifting attaches the
  `else` to the `if`. The rule that a `let ... else` expression cannot end
  with `}` is checked after parsing.
- **`{` after `return`.** Shifting makes the block the value being returned.

Every other construct, including labels against values that begin with a
name, list literals against map literals, and lambdas against function types,
is decided by the next token.

## What the grammar leaves to later stages

The parser builds the same tree for some constructs that mean different
things. These are decided afterward, without changing the tree's shape:

| Construct | Decided by | How |
|---|---|---|
| `name[...]` | Name resolution | Type arguments if `name` is a generic function; otherwise an index. For a method, type checking decides. |
| A bare `LOWER_NAME` in a pattern | Name resolution | The constant if one with that name is in scope; otherwise a new binding. |
| A bare argument after the first | Name resolution | Must name a parameter or field; otherwise an error. |
| Whether an expression after `mut` or `own` starts with a place | Name resolution | It must start with a variable or `self`, followed by fields and indexes. |
| A variant in a pattern | Type checking | Looked up in the type of the matched value. |
| A method call or field | Type checking | Looked up in the type of the receiver. |
| An `impl` for a trait with type parameters | Type checking | Chosen by the argument types, worked out first. |
| The cost words, `log`, `power`, `result`, `old` | The parser and name resolution | Names to the lexer. The parser checks their spelling where a `cost` clause expects them, and name resolution gives `log`, `power`, `time(...)`, `calls(...)`, `result`, and `old` their meaning in specifications. |
| The expected type of `[...]` | Type checking | `List` unless an `Array` or `Set` is expected. |
