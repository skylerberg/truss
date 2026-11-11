# Truss Parser

This document describes the stage0 parser, in [`stage0/`](stage0). It
implements the syntactic grammar in [GRAMMAR.md](GRAMMAR.md), reads the
tokens described in [LEXER.md](LEXER.md), and follows the rules in
[SYNTAX.md](SYNTAX.md) and [DESIGN.md](DESIGN.md). Each departure from those
documents is stated here.

## What the parser does

The parser takes one file's token array from the lexer and returns a syntax
tree for each definition and a list of diagnostics. Like the lexer, it always
returns a tree, even for a file with errors, so that later stages can check
every definition that did parse.

The parser:

- splits the file into its `use` lines and its top-level definitions
- parses each definition separately into a syntax tree, with spans relative
  to the start of that definition
- recognizes the cost words, `O`, and `finite` by their spelling where a
  `cost` clause expects them
- reports operators that need parentheses, with exact fixes
- reports `Reserved` and `Foreign` tokens, and the habits from other
  languages that are made of valid tokens, with exact fixes
- checks the rules that need only the tree of one definition, such as where
  `assert`, `yield`, `break`, `==>`, and `forall` may appear

It does not:

- resolve names. `name[...]` is one node whether it is an index or type
  arguments, a bare name in a pattern is one node whether it is a constant
  or a binding, and an expression such as `List[String]` before a `.` is one
  node whether it names a type or a value. Name resolution decides, without
  changing the tree's shape (see
  [GRAMMAR.md](GRAMMAR.md#what-the-grammar-leaves-to-later-stages)).
- check that a bare argument after the first names a parameter, which needs
  the callee's signature, or that the expression after `mut` or `own` starts
  with a place, which needs name resolution (see
  [TYPECHECKER.md](TYPECHECKER.md)).
- know types, or anything outside the definition it is parsing

**A definition's tree is a function of that definition's tokens.** It never
depends on the rest of the file. GOALS.md's "incremental everything" needs
this property from the parser: a definition that only moved has exactly the
same tree as before, so no result computed from the tree is computed again.

The parsing functions cannot break this property by reading the rest of the
file. A cursor holds the definition's tokens, its base, and its source text,
the bytes from its first token to the end of its last. It holds no other
part of the file's text and no line table, so a fix or a message can quote
only the definition's own bytes.

## Structure

```text
token array ──▶ Split ──one token slice per definition──▶ Parse ──▶ Check ──▶ tree
                  │                                         │          │
                  └──────────────────▶ diagnostics ◀────────┴──────────┘
```

A piece is a `use` line or a definition. `Parser.parse` parses every piece
of a file. `Parser.definition` and `Parser.use_line` parse one piece, for
the tools and tests that need one.

### Splitting a file into definitions

The lexer guarantees balanced brackets, so the definitions in a file are
found without parsing them. A `NEWLINE` at bracket depth 0 ends a `use` line
or a definition, unless the next token is `{`. In that case the `NEWLINE`
precedes a body that starts on a line of its own, as in a signature whose
clauses end on the line above the body. No `use` line or definition starts
with `{`, so the rule never splits a definition in two.

- `Split` walks the token array once, with only a bracket depth as state,
  and returns each piece's first token index and one past its last.
- A `use` line after the first definition is an error, with a fix that moves
  it up to the other `use` lines.
- A piece that starts with a token that cannot start a definition, such as a
  statement at the top level, is still a piece. Parsing it reports one
  error, such as "statements must be inside a function", and the
  definitions before and after it are unaffected.

Because the lexer's bracket recovery closes every open bracket at a
definition keyword in column 0 (see [LEXER.md](LEXER.md#brackets)), a missing
`}` in one definition never makes the next definition part of it.

### Methods declared inside a definition

A method declared inside a trait, an `impl`, or a capability is a separate
definition. The function that parses the trait, the `impl`, or the
capability parses its header and its other members: an associated type, an
associated capability set, or a law. Where a member starts with `fn`, it
records the method's token range, found by the rule that splits a file,
and skips those tokens. Each method is then parsed from its own tokens,
with a new `Cursor`, like any other definition.

- **A method has its own base, text, and node ids,** so an edit to one
  method changes neither the trees of the other methods in the same `impl`
  nor the tree of the `impl`.
- **A method records its container.** Its item holds the index of the
  trait, `impl`, or capability among the file's definitions, and the method
  follows its container in the file's list.
- **A method has the visibility of its container,** since it declares none.
- **A method that does not parse** is a definition whose header did not
  parse, like any other, and the methods before and after it are
  unaffected.

### Parsing one definition

Each definition is parsed from its own token slice, with a new `Cursor`.

- **Spans are relative to the definition.** The definition records its
  *base*, the absolute byte offset of its first token, and every span in its
  tree is relative to the base. Adding a line above a definition changes
  only its base, so its tree, and every result computed from the tree, is
  unchanged. DESIGN.md requires exactly this of compiled positions, and
  relative spans in the tree provide it to every later stage.
- **Its diagnostics are relative too.** Each piece has a diagnostic
  collector of its own, and `Parser.definition` returns the diagnostics
  relative to the base, with their notes and fixes. They have a type of
  their own, so that they cannot be shown before `Parser.placed` adds the
  base, which converts them to file offsets. `Parser.parse` does that for a
  whole file, since tools and editors use file offsets. The one diagnostic
  that depends on the rest of the file, a `use` line after a definition, is
  reported by `Parser.parse`.
- **The definition records its source text,** the bytes from its first token
  to the end of its last token. `truss fmt` prints each literal from its
  span, as LEXER.md describes, and the spans index this text.
- **Interpolations are parsed from their own token arrays.** Each one is
  parsed as an expression by a new `Cursor` over the interpolation's tokens,
  as LEXER.md describes. The spans of those tokens are absolute, and are
  made relative with the same base.

### Recursive descent with no backtracking

The parser is hand-written recursive descent, for its error messages. A
second parser, built by Menhir from `grammar/truss.mly` for tests and tools
only, is the reference it is checked against: both must accept every piece
of every example in the documents, and accept and reject the same mutated
pieces.

The grammar makes a hand-written parser cheap. Every type position and
every pattern position is determined by the keyword or punctuation before
it, so the parser always knows which sub-grammar it is in. The parser never
backtracks, and its lookahead is at most three tokens:

| Decision | Lookahead |
|---|---|
| A label, `name:`, against an argument that starts with a name | `LOWER` then `:` |
| An associated-type constraint, `Element = Int64`, in brackets | `UPPER` then `=` |
| The empty map `[:]` | `[` then `:` then `]` |
| A map literal against a list literal | Parse each element with an optional `: value`, then check that they agree |
| A trait method with its body on the next line, against the next member | `NEWLINE` then `{` |
| A function name against a method name in a definition | `UPPER`, or `LOWER` then `::`, starts a type head |
| A range with no start in brackets, `items[..3]` | `..` or `..=` right after `[` |

Each parsing function consumes at least one token or returns, so parsing
always terminates.

Types, clauses, expressions, and statements contain each other: a statement
has a type annotation, a function type in parentheses carries clauses, a
clause holds expressions, and an expression holds blocks of statements. Their
parsing functions are therefore one group of mutually recursive functions in
one module. Patterns contain none of them, and have a module of their own.

### Limits on nesting

The depth of the tree is bounded, so that hostile input cannot make the
parser, or any later stage that walks the tree, recurse without bound. Two
limits bound it:

- **Nesting is limited to 256 levels.** The parser counts each expression,
  type, pattern, block, and prefix operator that encloses the current
  token. Every recursive call of a parsing function passes through one of
  them.
- **A chain is limited to 10,000 links.** A chain is a run of operations in
  which each takes the result of the one before as an operand: binary
  operators at one precedence level, as in `a + b + c`, postfix operations,
  as in `a.b.c`, and `else if` branches. The nesting limit does not count a
  chain's links, but each link nests the tree one level deeper.

Both limits are far above what code written by a person or an agent reaches,
as is the lexer's limit of 32 nested interpolations. Exceeding either is the
error `parser.nesting_too_deep`.

## The syntax tree

### An abstract syntax tree, not a lossless one

The tree has the program's constructs and each node's span, and not every
token. Languages with comments need a lossless syntax tree, which holds
every token and every piece of whitespace, because comments can appear
anywhere and the formatter must preserve them. Roslyn and rust-analyzer
build one for that reason. Truss has no comments, so only whitespace
separates tokens, and `truss fmt` decides all whitespace. The formatter
needs little beyond the constructs, and the tree records it:

- **The spelling of each literal,** through its span into the definition's
  source text. Values are in the tree too.
- **Blank lines.** A statement, member, `match` arm, and definition records
  whether a blank line preceded it, from the lexer's `blank_line_before`.
  `truss fmt` preserves them, collapsing a run of blank lines to one, as Go,
  Rust, and Gleam do.
- **Parentheses.** A parenthesized expression is a `Parenthesized` node, so
  that the check for operators that need parentheses can see them, and the
  formatter can preserve them.

Everything else, such as trailing commas, the optional `|` before the first
variant, and where lines break, is layout. The formatter decides it, so the
tree does not record it. The language server finds the node at a position
from the spans, and the token at a position from the lexer's token array.

### Shape

The tree types, in [`stage0/syntax/syntax.ml`](stage0/syntax/syntax.ml),
follow GRAMMAR.md closely. Most of the tree is made of one record,
`'kind node`, which holds a construct's kind, its span, and its id: an
expression is an `expression_kind node`, and patterns, types, clauses,
parameters, fields, and the rest are nodes the same way. Statements and the
members of traits, `impl`s, and capabilities are `'kind line`s, which also
record whether a blank line preceded them. A definition is a record of its
visibility, its kind, and its span.

- **Constructs with the same syntax are one node.** `Bracket` is an index or
  type arguments, `Name` is a variable, a constant, a function, a type, or a
  variant, and `Member` is a field, a variant of its type, an associated
  type, or the callee of a method call. Name resolution and type checking
  record their results for these nodes in tables keyed by node id; they
  never rebuild the tree.
- **Every node has an id,** an integer unique within its definition, as
  TYPECHECKER.md's "Node identity" requires. So do the records that
  represent a piece of syntax without being a `node`: names, path types,
  type heads, string literals, blocks, arms, variants, and the definition
  itself. A node gets its id when the parser builds it, after its children,
  from one counter for the definition. The definition's interpolations and
  the second parse of a header that failed share that counter. So the same
  tokens produce the same ids, a definition that only moved has the same
  ids, and a later stage stores its results for a node in a dense table
  indexed by the id. When the parser extends an existing node, as it does to
  the expression that a trailing lambda joins, the node keeps its id.
- **Types inside expressions are expressions.** In
  `List[String].with_capacity(64)`, `List[String]` is a `Bracket` over two
  `Name`s. Name resolution resolves it to a type. Type positions, such as
  annotations and signatures, have their own `type_expression` nodes.
- **Patterns have one node for a bare name.** Name resolution decides a
  `Binding_or_constant`, as the grammar specifies. The ends of a range are
  their own `range_end` nodes, since a name there can only be a constant.
- **Clauses are typed, not generic.** A function's clauses are a list in
  source order, since the order of clauses of one kind matters, but each is
  a specific constructor: `Uses`, `Requires`, `Ensures`, `Decreases`, or
  `Cost` with a parsed resource and bound. The hash sorts them by kind and
  preserves the order within each kind.
- **An operation records its operator's span.** `Binary`, `Is`, and `Range`
  have an `operator_span`, so an error about a combination points at the
  operator, and the language server can find it.
- **Types make invalid trees unrepresentable.** A trait's members and an
  `impl`'s members have a type each, so an `impl` cannot hold a law. A
  method without a body is a separate kind of definition, which only a trait
  or a capability can hold; a function always has a body. A `with` update
  names at least one field.
- **Every part that can fail to parse has an `Error` case:** definitions,
  members, statements, arms, clauses, parameters, generic parameters,
  fields, updates, expressions, patterns, and types. A part that did not
  parse becomes an `Error` node with the span it covered, and the rest of
  the tree is built as usual.
- **Each item records its base and its source text.** A file is its `use`
  lines and its definitions, each an `item` with the absolute offset of its
  first token, the bytes from its first token to the end of its last, and
  whether a blank line preceded it.

### Strings

A string literal in the tree has its optional tag as a `path`, so
`database::SqlQuery"..."` is one node, its texts with their values, and its
interpolations as expressions. The parser joins a module path to the tagged
string after it, which the lexer emits as separate tokens.

## Expressions

### Precedence and combinations that need parentheses

Precedence in Truss is a partial order: some pairs of operators have no
relative precedence, and need parentheses. A parser can enforce that in two
ways:

- **Encode the partial order in the grammar,** as GRAMMAR.md and
  `truss.mly` do. A combination that needs parentheses is then a syntax
  error at the second operator, such as "unexpected `==`" in
  `flags & mask == 0`, and a good fix needs both operands, which the parser
  has not built yet.
- **Parse with a total order, then check each combination.** This is
  Carbon's approach, which DESIGN.md already follows for the partial order
  itself. The parser builds the tree as if every pair had a relative
  precedence, then checks each operator against its operands. A combination
  without one gets an error that quotes both operands and offers the exact
  parentheses.

The parser does the second. The total order it parses with, tightest first:

| Level | Operators |
|---|---|
| Postfix | `.` `()` `[]` `?` `with (...)` |
| Modes | `mut` `own` `any`, which take a postfix expression |
| Prefix | `-` `!` `~` |
| Multiplicative | `*` `/` `%` |
| Additive | `+` `-` |
| Shifts | `<<` `>>` |
| Bitwise | `&`, then `^`, then `\|` |
| Ranges | `..` `..=` |
| Comparisons | `==` `!=` `<` `<=` `>` `>=` `is` |
| Logical | `&&`, then `\|\|` |
| Implication | `==>` |
| Lowest | `echo`, `return`, and the body of `forall` and `exists` |

The levels Truss defines are Truss's own. The order among the shift and
bitwise levels, which Truss does not define, is Rust's, the order that C,
Go, Rust, and Swift most often share. Then `Operators` walks every
expression, checks each operation against each of its operands, and reports:

| Written | Error and fixes |
|---|---|
| `flags & mask == 0` | Bitwise operators combine only with themselves. Fixes, Rust's grouping first: `(flags & mask) == 0`, `flags & (mask == 0)` |
| `a << b + 1` | The fixes are `a << (b + 1)`, the grouping of C and Rust, and `(a << b) + 1`, the grouping of Go and Swift |
| `a & b \| c` | Every language groups it the same way, so one fix: `(a & b) \| c` |
| `a && b \|\| c` | `&&` and `\|\|` cannot be mixed. Fixes: `(a && b) \|\| c`, then `a && (b \|\| c)` |
| `a < b < c` | Comparisons do not chain. When `b` is a name or a literal, the fix is `a < b && b < c`, its meaning in Python; otherwise there is no fix |
| `a ==> b ==> c` | `==>` does not chain. Fixes: `a ==> (b ==> c)`, Dafny's grouping, then `(a ==> b) ==> c` |
| `0..10..20` | Ranges do not chain. No fix |
| `!response is Ok(_)` | `!` and `is` have no relative precedence. Fixes: `!(response is Ok(_))`, Python's grouping, then `(!response) is Ok(_)`, the grouping of C#, Kotlin, Swift, and JavaScript |

A grouping is which of two adjacent operators is applied first. When other
languages group a combination differently, the diagnostic offers each
grouping as a separate fix, so an agent chooses the one it meant and does
not rely on a precedence table it may misremember. The groupings are
computed from a table of the precedence that Rust, C, Go, and Swift give
each operator.

- **Each fix inserts only parentheses,** except the fix for a chained
  comparison, so applying it changes nothing else.
- **A fix introduces no new combination that needs parentheses.** A
  grouping that changes which operator is applied last can make the root an
  operator that the enclosing operator cannot take as an operand, as
  `a & (b == c)` would inside `&& d`. That fix puts the whole expression in
  parentheses too: `(a & (b == c)) && d`.
- **A grouping that has no syntax is not offered.** In `x is P & y`, the
  other grouping would put `& y` inside the pattern, and a pattern has no
  parentheses for grouping, so the only fix is `(x is P) & y`.
- **Each error points at the operator** that cannot take its operand, such
  as the `==` in `flags & mask == 0`, or the second `<` in `a < b < c`.
- **Every combination is reported,** so a chain such as `a < b < c < d` gets
  one error for each `<` after the first. Applying any one fix removes its
  error and leaves the others unchanged.

### The forms at the lowest level

- **`return` and `echo`** take an expression at the lowest level. A `{` right
  after `return` starts the value only when no `NEWLINE` separates them,
  which the lexer already decides: `return` can end a statement and `{` can
  begin one, so a line break between them is a `NEWLINE`.
- **Quantifiers** may also be the last operand of `&&`, `||`, or `==>`.
- **The parser accepts these forms wherever an operand begins,** and parses
  each one's body at the lowest level, so the body extends to the end of
  the expression. `Operators` then reports one that is an operand anywhere
  else, such as `count + echo x` or `count + forall ...`, with a fix that
  puts it in parentheses.
- **`if`, `match`, `provide`, blocks, and lambdas** are primary
  expressions, so they combine with operators like any other operand.

### Brackets after an expression

Brackets after an expression hold a list of items, each an expression or an
associated-type constraint. Inside them, and only there, a range may omit
its start or its end: the parser passes a flag to the range level that
allows a missing operand when the next token is `]` or `,`. A range with a
missing start or end anywhere else is an error whose message says that
open-ended ranges are only for brackets.

- **Brackets hold at least one item,** so `items[]` is an error.
- **A range that omits an end is the only item in its brackets,** as the
  grammar specifies, so `items[1.., 4]` is an error.
- **A collection literal is a list or a map, not both.** Each element is
  parsed with an optional `: value`, and then they must agree, so
  `[1, "a": 2]` is one error at the first element that does not.
- **`for i in 0.. {}` is reported at the `..`.** The grammar parses the `{}`
  as the end of the range, which leaves the loop without a body. When a `for`
  loop's collection is a range that ends with a block and no body follows,
  the error is the open-ended range.

### Statements

A statement is chosen by its first token: `let`, `var`, `for`, `while`,
`parallel`, `concurrent`, `proof`, `assert`, and `yield` each start their
own form, and any other token starts an expression, which may be followed
by `=` or a compound assignment. A `match` arm's body is parsed by the same
function.

- **`let ... else`.** After the expression of a `let` or `var`, an `else`
  starts the `else` block. If the expression ends with `}`, as an `if` or
  `match` does, that is an error, with a fix that puts the expression in
  parentheses. GRAMMAR.md leaves this rule to a check after parsing.
- **Bodies on the next line.** The function that expects a body skips one
  `NEWLINE` before its `{`. It is called only where a body must follow:
  after a signature and its clauses, a loop header, an `if` or `while`
  condition, the scrutinees of a `match`, `provide` implementations, and a
  lambda's parameters.

## Definitions

Each definition is chosen by its first token, after an optional `public`,
`public opaque`, `public transparent`, or `internal`. The rules that the
grammar leaves to a check are checked as the definition is parsed, where the
tokens and their spans are available for fixes:

- `opaque` only before `type`, with a fix that removes it
- `transparent` only before `fn`, with a fix that removes it
- no visibility on an `impl`, a test, or a law's proof, with a fix that
  removes it
- `self` only as a method's first parameter. A method is declared
  `fn Type.name`, or is in a trait or an `impl`; a capability declares its
  methods without `self`.
- `uses` and `decreases` at most once
- no function named `old`
- no `lends own`: a part that a `lends` method lends stays with `self`, and
  a fix removes the `own`
- a function type's inputs named exactly when it has a `requires`
- a loop's `cost` neither `amortized` nor `finite`
- a body for every function outside a trait or a capability. A missing one
  gets the fix ` { todo }`, the body of unwritten code, after the signature.

### Cost clauses

The words of a `cost` clause are names to the lexer. The parser parses
`cost [amortized] resource bound`, where `amortized`, `time`,
`allocations`, `allocated_bytes`, `calls`, `O`, and `finite` must be spelled
exactly. `Cost_word` spells each word once, and the parser compares names
against that table, never against a string literal elsewhere.

- **A misspelling gets a fix when exactly one word is within an edit
  distance of 2,** such as `allocation` for `allocations`. The parser then
  continues with that word, so that the rest of the clause is checked too.
- **`finite` for a resource other than `time`** is an error, and the parser
  continues.
- **`cost potential expression`** is accepted only on a type.
- **Inside a bound,** `time(...)`, `calls(...)`, `log(...)`, and
  `power(...)` parse as ordinary calls; name resolution resolves them, as
  GRAMMAR.md specifies.

## Checks on a whole definition

`Check` walks a definition's tree once with a small context: whether the
current node is inside a specification, a test, a proof, a loop, a lambda, a
`parallel` branch, and a method that yields or lends. It reports:

- `==>`, and a quantifier over a whole type such as `forall value: Int64`,
  in a test, a constant, or a default. Specifications allow both, and so
  does a function's body: a function whose signature mentions a
  specification-only type has a body that is a specification, and only the
  type checker knows the types. The type checker reports them in a body
  that is compiled. A quantifier over a range or a collection is an
  ordinary expression, allowed anywhere. Specifications are `requires`,
  `ensures`, `invariant`, `decreases`, `cost`, laws, theorems, and `proof`
  blocks.
- `assert` outside tests, theorems, and proofs, including in a lambda there,
  and `proof` blocks outside function bodies
- `yield` outside a method whose signature `yields` or `lends`
- `break` and `continue` outside a loop, or inside a lambda in that loop
- `return`, `break`, `continue`, and `?` that would leave a `parallel` block,
  and `break`, `return`, and `?` in a `parallel for`. A `concurrent` block
  or loop may be exited early, so nothing is reported there.
- `echo` inside a specification, which is never executed
- a parameter named `result`, or, in a lending or yielding method, `yielded`
  or `finished`
- a `requires` on a function type anywhere but at the top of a parameter's
  type

These need only the one definition's tree, so they belong to the parser. They
are a separate pass, not part of each parsing function, so the parsing code
does not thread a context through every call, and each rule is tested
separately. The pass handles only the nodes that change the context, such
as a lambda, a loop, or a `proof` block, and delegates every other node to
`Syntax_walk`'s traversal of a node's child expressions and statements, so
a construct added to the tree is checked by every rule without a change to
`Check`.

## Errors and recovery

### Diagnostics

Diagnostics use the shared `Diagnostic` type from LEXER.md, with codes such
as `parser.unexpected_token` and `parser.needs_parentheses`. Each habit from
another language has a code of its own, such as `parser.increment`, so tools
and agents can match on it. Every diagnostic is an error. Messages are full
sentences, as the lexer's are, which `Diagnostic.t` requires of every stage.
When the parser can infer the intended code, the diagnostic has an exact
fix; otherwise the message states the expected tokens, such as "Expected
`=>` after the patterns of a `match` arm, found a line break."

The expected tokens come from the parsing function that failed, which knows
the tokens that may follow. A generated parser can list them too, but a
hand-written one can describe them in terms of the construct being parsed,
which an agent can act on.

### Recovery

Brackets are always balanced, so the parser has exact synchronization
points after an error:

- **Inside brackets,** an error in an item skips to the next comma of the
  list, stepping over any nested brackets, and the items after the comma
  parse normally, so three invalid arguments produce three errors. The
  parser has the index of each opener's closer, computed once per
  definition, so stepping over a nested group is one step, not a search.
- **In a block, a trait, an `impl`, a capability, or a `match`,** an error
  skips to the next `NEWLINE` at the same depth, or to the closing `}`. The
  statement, member, or arm becomes an `Error` node, and the ones after it
  parse normally.
- **In a signature,** an error in a clause skips to the next clause keyword
  or to the body's `{` at the definition's own depth. A `requires` that
  does not parse still leaves the body parsed.
- **At the top level,** an error ends the definition. The next one is
  unaffected, because `Split` already found where it starts.

To avoid cascading errors:

- One error is reported per `Error` node. No error is reported for the
  tokens that recovery skips.
- A zero-width closer that the lexer inserted (see
  [LEXER.md](LEXER.md#brackets)) already has its error, so the parser does not
  report a token missing before it. Once a statement, member, or arm has
  consumed such a closer, the tokens after it in that item were not
  delimited by the author, so no more syntax errors are reported in it. This
  applies to the one item: the items of a block inside it are reported
  normally, and so is the rest of the item that encloses the block, unless
  the block's own `}` is one the lexer inserted.
- An empty interpolation already has the lexer's error, so the parser
  reports nothing for it, and reports no missing token at the end of an
  interpolation that a line break ended.
- A file reports at most 200 diagnostics, as in the lexer.

### Syntax from other languages

SYNTAX.md's rule is that each common habit gets its own error and an exact
fix. The lexer handles the habits it can fix from the tokens alone. The rest
need the surrounding tokens, so the parsing functions recognize each one at
the point where the grammar has already rejected a token. A recognizer
therefore never changes the meaning of valid code. Each then calls
`Habits`, which holds every message and fix, and the parser builds the tree
of the fixed code and continues.

| Written | Recognized by | Fix |
|---|---|---|
| `i++`, `i--` | A `Foreign` token after an expression, at the end of its line | `i += 1`, `i -= 1` |
| `--x` | A `Foreign` token before an expression | `-(-x)` |
| `A => 1,` | `,` after a `match` arm's body | Remove the `,` |
| `x ? a : b` | `?` followed by a token that starts an expression but cannot follow `?`. The whole expression before the `?` is the condition, as in C and JavaScript, where `?:` binds most loosely | `if x { a } else { b }` |
| `let mut x` | `mut` right after `let` | `var x` |
| `&x`, `&mut x` | `&` where an expression must begin | `x`, `mut x` |
| `\|x\| x + 1`, `\|\| x` | `\|` or `\|\|` where an expression must begin | `fn(x) { x + 1 }`, `fn() { x }` |
| `Point { x: 1.0, y: 2.0 }` | An `UPPER` name, then `{`, a name, and `:`, on one line; no block starts with a label | `Point(x: 1.0, y: 2.0)` |
| `parse::<Int64>(text)` | `::` followed by `<` | `parse[Int64](text)` |
| `items.map { it.name }` | A statement that ends with a name or a member, followed on its line by a block that uses `it`, in its code or in its interpolations | `items.map(fn(item) { item.name })`, renaming every `it`, and naming the parameter with the singular of the collection's name when its plural is regular, as `item` for `items` and `entry` for `entries`, and otherwise `element` |
| `List<String>`, `fn first<T>(...)` | `<` where type arguments or generic parameters go, closed by `>` on the same line | `List[String]`, `fn first[T](...)` |
| `Shape::Circle`, `List::new()` | `::` after an `UPPER` name in an expression | `Shape.Circle`, `List.new()` |
| `Shape.Circle(radius)`, `Shape::Circle(radius)` in a pattern | `.` or `::` and an `UPPER` name after an `UPPER` name | `Circle(radius)` |
| `vec![1, 2]`, `println!(...)` | A name, `!`, and `(` or `[`, with no space between them | `[1, 2]` for `vec!`; none for the others, whose message says what to write |
| `todo!()`, `unreachable!()` | `!` and `(` right after the keyword | `todo`, `unreachable`; none when the parentheses hold arguments |
| `(a, b)`, `(Int64, String)`, `pair.0` | A comma directly inside the parentheses of an expression or a type; a number after `.` | None; the message says that Truss has no tuples and recommends a record |
| `List<String>.new()` | `<` after an `UPPER` name in an expression, when a `.`, a `(`, or a `::` follows its closer; otherwise the `<` is a comparison | `List[String].new()` |
| `impl<T> Trait for Box[T]` | `<` right after `impl` | `impl Trait for Box[T]`; none when a parameter has a bound, which belongs on the type after `for` |
| `fn(x: Int64) -> Int64 { ... }` | `:` after a lambda's parameter, or `->` after its parameters | `fn(x) { ... }` |
| `a ** b` | The `Foreign` token `**` where a binary operator goes | None; the message says that Truss has no power operator |
| `count := 0` | The `Foreign` token `:=` after a statement's expression | `let count = 0`; none when the target is not a name |
| `items \|> sum` | The `Foreign` token `\|>` after an expression | `sum(items)`; none when the right operand is a call, since languages disagree about which argument the value becomes |
| `a ?? b`, `a ?: b` | `?`, then `?` or `:` with no space between them, then the start of an expression. `a?? - 1` applies `?` twice, and `[key?: value]` is a map entry, so `??` is not followed by `-` or an opener, and `?:` has a space before it | `a.unwrap_or(b)` |
| `x as Int64` | The reserved word `as` after an expression, with a type after it on the same line | `Int64.from(x)`, then `Int64.try_from(x)`, for a conversion that can lose information, as most casts can |
| `0.0 =>` in a pattern | A float literal where a pattern begins | None; the message recommends a guard, as in `value if value == 0.0` |
| `loop {`, `const`, `static` | A `Reserved` token where a statement or a definition starts | `while true {`, `let` |
| `where` and the other reserved words | A `Reserved` token anywhere else | None; the message states that the word is reserved |
| `elif` | The name `elif` starting a statement right after an `if` | `else if` |

Habits that are names, such as `null`, `nil`, and a second argument without a
label, depend on name resolution, so name resolution and type checking
report them (see [TYPECHECKER.md](TYPECHECKER.md)).

## Interfaces to other stages

- **The lexer** passes the parser one token array per file. The parser reads
  the source bytes only through spans, to build fixes and to record each
  definition's source text.
- **Name resolution** gets one tree per definition, and records the
  referent of each name in a table keyed by node id, without changing the
  tree. It decides `Bracket`, `Binding_or_constant`, and `Name` nodes. Type
  checking then reports bare arguments that name no parameter. Both are
  designed in [TYPECHECKER.md](TYPECHECKER.md).
- **A definition with a syntax error keeps the parts that parsed,** so that
  an error in one definition does not make every use of its name an error
  elsewhere:
  - a definition whose header did not parse is a `Definition_error` with its
    keyword and its name, when those were parsed
  - any other has its whole tree, with an `Error` node for each part that
    did not parse. A function whose body is missing has its signature, with
    an `Error` statement for the body.
  - every definition lists the spans where the parser recovered, in
    `recovered`: each failure, reported or silent, that produced an `Error`
    node, each closer the lexer inserted that it consumed, and each
    diagnostic whose code means the source is not valid Truss, such as a
    habit, whose nodes are those of the fixed code. A part of the
    definition, such as a signature, a body, or a member, matches its
    source text exactly when no recovery lies in its span, whatever other
    diagnostics it has. Every recovery covers at least one byte of the part
    it is in: one at the end of the definition, or at a closer the lexer
    inserted, which is at the end of the part it closes, starts at the
    start of the token before it. The one zero-width recovery is the offset
    of a missing body, and it lies in the body that starts there.

  A diagnostic for valid syntax that breaks a rule checked after parsing,
  such as a misplaced `assert`, is not a recovery: the tree there matches
  the source text. Which codes are recoveries is one exhaustive match in
  `Cursor`, so a new code cannot be added without deciding. TYPECHECKER.md
  decides how resolution registers a definition with a syntax error and
  which of its parts it checks.
- **The formatter and the language server,** which are not built, need only
  what the tree records: a literal is printed from the definition's source
  text, a blank line is preserved, and a position maps to a node through
  the spans, after adding each definition's base.
- **The code database** lexes and parses a whole file when its text changes,
  as DATABASE.md describes. A definition whose tree is equal to the one
  before, as the tree of a definition that only moved is, invalidates no
  result that was computed from it.

## Not built

- **Parsing only the definitions whose text changed.** A definition's tree
  and its relative diagnostics are functions of its tokens, so they could be
  cached by its source text. The tokens have absolute spans, so reuse would
  need a copy of each slice with relative spans. Nothing needs it yet.
