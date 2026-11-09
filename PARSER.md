# Truss Parser

This document designs the stage0 parser. It implements the syntactic grammar
in [GRAMMAR.md](GRAMMAR.md), reads the tokens described in
[LEXER.md](LEXER.md), and follows the rules in [SYNTAX.md](SYNTAX.md) and
[DESIGN.md](DESIGN.md). Where this design departs from those documents, it
says so. The parser is built, in [`stage0/`](stage0).

## What the parser does

The parser takes one file's token array from the lexer and returns a syntax
tree for each definition and a list of diagnostics. Like the lexer, it always
returns a tree, even for a broken file, so that later stages can check every
definition that did parse.

The parser:

- splits the file into its `use` lines and its top-level definitions
- parses each definition on its own into a syntax tree, with positions
  relative to the start of that definition
- recognizes the cost words, `O`, and `finite` by their spelling where a
  `cost` clause expects them
- reports operators that need parentheses, with exact fixes
- reports `Reserved` and `Foreign` tokens, and the habits from other
  languages that are made of valid tokens, with exact fixes
- checks the rules that need only the tree of one definition, such as where
  `assert`, `yield`, `break`, `==>`, and `forall` may appear

It does not:

- decide what a name means. `name[...]` is one node whether it indexes or
  gives type arguments, a bare name in a pattern is one node whether it is a
  constant or a binding, and an expression such as `List[String]` before a
  `.` is one node whether it names a type or a value. Name resolution
  decides, without changing the tree's shape (see
  [GRAMMAR.md](GRAMMAR.md#what-the-grammar-leaves-to-later-stages)).
- check that a bare argument after the first names a parameter, which needs
  the callee's signature, or that the expression after `mut` or `own` starts
  with a place, which needs name resolution (see
  [TYPECHECKER.md](TYPECHECKER.md)).
- know types, or anything outside the definition it is parsing

**The parser is a pure function of one definition's tokens.** The tree for a
definition depends only on its own tokens, never on the rest of the file.
That is the property GOALS.md's "incremental everything" needs from this
stage: an edit to one definition re-parses that definition alone, and a
definition that only moved gives exactly the same tree as before.

## Structure

```text
token array ──▶ Split ──one token slice per definition──▶ Parse ──▶ Check ──▶ tree
                  │                                         │          │
                  └──────────────────▶ diagnostics ◀────────┴──────────┘
```

The tree has libraries of its own, so that name resolution, the formatter,
and the language server depend on it without depending on the parser:

| Library | Job |
|---|---|
| `Syntax` | The tree types, shared by every later stage |
| `Syntax_walk` | Visits the expressions of a tree, for checks that look at every one |
| `Syntax_print` | Prints a tree as a compact S-expression, for tests and `truss-parse --tree` |

The parser is one dune library, which depends on `Token`, `Source`,
`Diagnostic`, and the tree, and holds:

| Module | Job |
|---|---|
| `Split` | Finds the `use` lines and each definition's token slice |
| `Cursor` | Reads a token slice: the current token, lookahead, reporting errors, and the jumps recovery makes |
| `Atoms` | Names, module prefixes, and string literals, which every part of the grammar uses |
| `Cost_word` | The words of `cost` clauses, with the one table of their spellings |
| `Parse_pattern` | Patterns |
| `Parse_expression` | Types, clauses, expressions, statements, and blocks |
| `Parse_definition` | Definitions, and the members of traits, `impl`s, and capabilities |
| `Operators` | The check for combinations of operators that need parentheses |
| `Habits` | The messages and fixes for syntax from other languages |
| `Check` | Rules that need the whole tree of a definition |
| `Parser` | The entry points, for a whole file and for each piece of it |

`Parser.parse : Source.t -> Token.t array -> Syntax.file * Diagnostic.t list`
parses a whole file. The background process parses a file one piece at a
time instead: `Parser.split` finds the pieces, a piece being a `use` line or
a definition, and `Parser.definition` and `Parser.use_line` each parse one
piece, so a piece whose text did not change keeps what it parsed to. See
[Parsing one definition](#parsing-one-definition).

Types, clauses, and expressions are one module because they contain each
other: a statement has a type annotation, a function type in parentheses can
carry a `cost` clause, and a clause holds expressions. Patterns contain none
of them, and are their own module.

`stage0/bin/truss_parse.ml` builds `truss-parse`, which prints a file's
diagnostics, as JSON with `--json`, and its tree with `--tree`.

### Splitting a file into definitions

The lexer guarantees balanced brackets, so the definitions in a file can be
found without parsing them. A `NEWLINE` at bracket depth 0 ends a `use` line
or a definition, unless the next token is `{`. In that case the `NEWLINE` comes
before a body that starts on its own line, as in a signature whose clauses end
on the line above the body. No `use` line or definition starts with `{`, so the
rule never splits a definition in two.

- `Split` walks the token array once, keeping only a bracket depth, and
  returns each item's first and last token index.
- A `use` line after the first definition is an error, with a fix that moves
  it up to the other `use` lines.
- An item that starts with a token that cannot start a definition, such as a
  statement written at the top level, is still split off. Parsing it reports
  one error, such as "statements must be inside a function", and the
  definitions around it are unaffected.

Because the lexer's bracket recovery closes every open bracket at a
definition keyword in column 0 (see [LEXER.md](LEXER.md#brackets)), a missing
`}` in one definition never swallows the next one.

### Parsing one definition

Each definition is parsed from its own token slice, with a fresh `Cursor`.

- **Positions are relative to the definition.** The definition records the
  absolute byte offset of its first token, its *base*, and every span in its
  tree is relative to the base. Adding a line above a definition changes only
  its base, so its tree, and every result computed from the tree, stays the
  same. DESIGN.md asks for exactly this for compiled positions; doing it in
  the tree gives it to every later stage for free.
- **So are its diagnostics.** Each piece collects its diagnostics apart from
  the rest of the file's, and `Parser.definition` returns them relative to
  the base, with their notes and fixes, so a definition that only moved
  gives the same diagnostics as well as the same tree, and both can be
  cached together. They have a type of their own, so they cannot be shown
  by mistake where they would point at the wrong text: `Parser.placed`
  moves them by the base to their place in the file, which `Parser.parse`
  does for a whole file, since tools and editors work in file offsets. The one diagnostic that depends on the rest of the
  file, a `use` line after a definition, is reported by `Parser.parse`.
- **The definition keeps its source text,** the bytes from its first token to
  the end of its last token. `truss fmt` prints each literal from its span, as
  LEXER.md describes, and the spans are relative to this text.
- **Interpolations are parsed from their own token arrays.** Each one is
  parsed as an expression by a fresh `Cursor` over the interpolation's tokens,
  as LEXER.md describes. The spans of those tokens are absolute, and are made
  relative with the same base.

### Recursive descent with no backtracking

IMPLEMENTATION.md chose a hand-written recursive-descent parser for its error
messages, with `grammar/truss.mly` as a reference. The grammar makes that
cheap. Every type position and every pattern position is known from the
keyword or punctuation before it, so the parser never has to guess which
sub-grammar it is in. The parser never backtracks, and never looks more than
three tokens ahead:

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
always ends. Nesting is limited to 256 levels, so hostile input cannot make
the parser, or any later stage that walks the tree, recurse without bound.
The parser counts each expression, type, pattern, and prefix operator it is
inside, since every way it recurses goes through one of them: brackets,
blocks, `if` conditions, and the bodies of `echo`, `return`, and the
quantifiers all hold expressions. Like the lexer's limit of 32 nested
interpolations, no real code comes near it.

## The syntax tree

### An abstract tree, not a lossless one

The tree keeps what the program says, plus each node's span, and not every
token. Languages with comments need a lossless tree, which keeps every token
and every piece of whitespace, because comments can sit anywhere and the
formatter must put them back. Roslyn and rust-analyzer build one for that
reason. Truss has no comments, so the only thing between tokens is
whitespace, and `truss fmt` decides all whitespace. What the formatter needs
beyond the program is small, and the tree keeps it:

- **How each literal was written,** through its span into the definition's
  source text. Values are in the tree too, for hashing.
- **Blank lines.** A statement, member, `match` arm, and definition records
  whether a blank line came before it, from the lexer's `blank_line_before`.
  `truss fmt` keeps them, collapsing a run of blank lines to one, as Go,
  Rust, and Gleam do. Hashing ignores this.
- **Parentheses.** A parenthesized expression is a `Parenthesized` node, so
  that the check for operators that need parentheses can see them, and the
  formatter can keep them. Hashing ignores the node and hashes what is inside.

Everything else, such as trailing commas, the optional `|` before the first
variant, and where lines break, is layout. The formatter decides it, so the
tree does not record it. The language server finds the node at a position
from the spans, and the token at a position from the token array, which the
lexer already gives it.

### Shape

The tree types, in [`stage0/syntax/syntax.ml`](stage0/syntax/syntax.ml),
follow GRAMMAR.md closely. Most of the tree is made of one record,
`'kind node`, which holds what a part of the program is and its span: an
expression is an `expression_kind node`, and patterns, types, clauses,
parameters, fields, and the rest are nodes the same way. Statements and the
members of traits, `impl`s, and capabilities are `'kind line`s, which also
record whether a blank line came before them. A definition is a record of
its visibility, its kind, and its span.

- **Constructs that parse the same are one node.** `Bracket` is an index or
  type arguments, `Name` is a variable, a constant, a function, a type, or a
  variant, and `Member` is a field, a variant under its type, an associated
  type, or the start of a method call. Name resolution and type checking
  annotate these nodes; they never rebuild them.
- **Types inside expressions are expressions.** In
  `List[String].with_capacity(64)`, `List[String]` is a `Bracket` over two
  `Name`s. Name resolution reads it as a type. Type positions, such as
  annotations and signatures, have their own `type_expression` nodes.
- **Patterns have one node for a bare name.** `Binding_or_constant` is
  decided by name resolution, as the grammar says. The ends of a range are
  their own `range_end` nodes, since a name there can only be a constant.
- **Clauses are typed, not generic.** A function's clauses are kept as a
  list in the order written, since the order of clauses of one kind matters,
  but each is a specific constructor: `Uses`, `Requires`, `Ensures`,
  `Decreases`, or `Cost` with a parsed resource and bound. The hash sorts them
  by kind and keeps the order within each kind.
- **An operation records where its operator is.** `Binary`, `Is`, and
  `Range` keep their operator's span, so an error about a combination points
  at the operator, and the language server can find it.
- **Types rule out trees that cannot be written.** A trait's members, an
  `impl`'s members, and a capability's methods have a type each, so an `impl`
  cannot hold a law. Only a trait's method may have no body; a top-level
  function and an `impl`'s method always have one. A `with` update names at
  least one field.
- **Every part that can fail to parse has an `Error` case:** definitions,
  members, statements, arms, clauses, parameters, generic parameters,
  fields, updates, expressions, patterns, and types. A part that did not parse becomes an
  `Error` node with the span it covered, and the rest of the tree is built
  around it.
- **Each item records its base and its source text.** A file is its `use`
  lines and its definitions, each an `item` with the absolute offset of its
  first token, the bytes from its first token to the end of its last, and
  whether a blank line came before it.

### Strings

A string literal in the tree has its optional tag as a `path`, so
`database::SqlQuery"..."` is one node, its texts with their values, and its
interpolations as expressions. The parser joins a module path to the tagged
string after it, which the lexer leaves as separate tokens.

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
  itself. The parser builds the tree as if every pair had a precedence, then
  checks each operator against its operands. A combination without one gets
  an error that can quote both operands and give the exact parentheses.

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
bitwise levels, which Truss does not define, is Rust's, the reading C, Go,
Rust, and Swift most often share. Then `Operators` walks every expression,
checks each operation against each of its operands, and reports:

| Written | Error and fixes |
|---|---|
| `flags & mask == 0` | Bitwise operators combine only with themselves. Fixes, Rust's reading first: `(flags & mask) == 0`, `flags & (mask == 0)` |
| `a << b + 1` | The fixes are `a << (b + 1)`, the reading of C and Rust, and `(a << b) + 1`, the reading of Go and Swift |
| `a & b \| c` | Every language reads it the same, so one fix: `(a & b) \| c` |
| `a && b \|\| c` | `&&` and `\|\|` cannot be mixed. Fixes: `(a && b) \|\| c`, then `a && (b \|\| c)` |
| `a < b < c` | Comparisons do not chain. When `b` is a name or a literal, the fix is `a < b && b < c`, Python's reading; otherwise there is no fix |
| `a ==> b ==> c` | `==>` does not chain. Fixes: `a ==> (b ==> c)`, Dafny's reading, then `(a ==> b) ==> c` |
| `0..10..20` | Ranges do not chain. No fix |

When the readings of other languages disagree, the diagnostic offers each as
a separate fix, so an agent picks the one it meant instead of trusting a
table it may misremember. The readings come from a table of how tightly
Rust, C, Go, and Swift bind each operator.

- **Each fix inserts only parentheses,** except the one for a chained
  comparison, so applying it never changes anything else.
- **A fix leaves no new combination behind.** A reading that changes which
  operator applies last can give an operator that the one around the whole
  expression cannot take, as `a & (b == c)` would inside `&& d`. That fix
  puts the whole expression in parentheses too: `(a & (b == c)) && d`.
- **A reading that cannot be written is not offered.** In `x is P & y`, the
  other reading would put `& y` inside the pattern, which has no grouping
  parentheses, so the only fix is `(x is P) & y`.
- **Each error points at the operator** that cannot take its operand, such
  as the `==` in `flags & mask == 0`, or the second `<` in `a < b < c`.
- **Every combination is reported,** so a chain such as `a < b < c < d` gets
  one error for each `<` after the first. Applying any one fix removes its
  error and leaves the others as they were.

### The forms at the lowest level

- **`return` and `echo`** take an expression at the lowest level. A `{` right
  after `return` starts the value only when no `NEWLINE` comes between them,
  which the lexer already decides: `return` can end a statement and `{` can
  begin one, so a line break between them is a `NEWLINE`.
- **Quantifiers** may also be the last operand of `&&`, `||`, or `==>`.
- **The parser finds these forms where an operand begins,** like any
  operand, and parses each one's body at the lowest level, so the body takes
  everything up to the end of the expression. `Operators` then reports one
  anywhere else, such as `count + echo x` or `count + forall ...`, with a fix
  that puts it in parentheses.
- **`if`, `match`, `provide`, blocks, and lambdas** are primaries, so they
  combine with operators like any other operand.

### Brackets after an expression

Brackets after an expression hold a list of items, each an expression or an
associated-type constraint. Inside them, and only there, a range may leave
out its start or its end: the parser passes a flag to the range level that
allows a missing operand when the next token is `]` or `,`. A range with a
missing start or end anywhere else is an error that says open-ended ranges
are only for brackets.

- **Brackets hold at least one item,** so `items[]` is an error.
- **A range that leaves out an end is alone in its brackets,** as the
  grammar says, so `items[1.., 4]` is an error.
- **A collection literal is a list or a map, not both.** Each element is
  parsed with an optional `: value`, and then they must agree, so
  `[1, "a": 2]` is one error at the first element that does not.
- **`for i in 0.. {}` is reported at the `..`.** The grammar reads the `{}`
  as the end of the range, which leaves the loop without a body. When a `for`
  loop's collection is a range that ends with a block and no body follows,
  the error is the open-ended range.

### Statements

A statement is chosen by its first token: `let`, `var`, `for`, `while`,
`parallel`, `proof`, `assert`, and `yield` each start their own form, and any
other token starts an expression, which may be followed by `=` or a compound
assignment. A `match` arm's body uses the same function.

- **`let ... else`.** After parsing the expression of a `let` or `var`, an
  `else` starts the `else` block. If the expression ends with `}`, as an
  `if` or `match` does, that is an error, with a fix that puts the
  expression in parentheses. This is the rule GRAMMAR.md checks after
  parsing.
- **Bodies on the next line.** The function that expects a body skips one
  `NEWLINE` before its `{`. It is called only where a body must come: after a
  signature and its clauses, a loop header, an `if` or `while` condition,
  `match` values, `provide` implementations, and a lambda's parameters.

## Definitions

Each definition is chosen by its first token, after an optional `public`,
`public opaque`, or `internal`. The rules that the grammar leaves to a check
are checked as the definition is parsed, where the tokens and their spans are
at hand:

- `opaque` only before `type`, with a fix that removes it
- no visibility on an `impl`, a test, or a law's proof, with a fix that
  removes it
- `self` only as a method's first parameter. A method is written
  `fn Type.name`, or is in a trait or an `impl`; a capability declares its
  methods without `self`.
- `uses` and `decreases` at most once
- no function named `old`
- no `lends own`: a part a `lends` method lends stays with `self`, and a fix
  removes the `own`
- a body for every function outside a trait or a capability. A missing one
  gets the fix `{ todo }`, the body of unwritten code, indented as its
  signature is.

### Cost clauses

The words of a `cost` clause are names to the lexer. The parser reads
`cost [amortized] resource bound`, where `amortized`, `time`,
`allocations`, `allocated_bytes`, `calls`, `O`, and `finite` must be spelled
exactly. `Cost_word` spells each word once, and the parser compares names
against that table, never against a string written elsewhere. A misspelling gets a fix when one word is close, such as `allocation`
for `allocations`, and parsing goes on as if that word had been written, so
the rest of the clause is checked too. `finite` for a resource other than
`time` is an error, and parsing goes on. `cost potential expression` is
accepted only on a type.
Inside a bound, `time(...)`, `calls(...)`, `log(...)`, and `power(...)` parse
as ordinary calls; name resolution gives them their meaning, as GRAMMAR.md
says.

## Checks on a whole definition

`Check` walks a definition's tree once with a small context: whether it is
inside a specification, a test, a proof, a loop, a lambda, a `parallel`
branch, and a method that yields or lends. It reports:

- `forall`, `exists`, and `==>` outside specifications. Specifications are
  `requires`, `ensures`, `invariant`, `decreases`, `cost`, laws, theorems, and
  `proof` blocks.
- `assert` outside tests, theorems, and proofs, including in a lambda there,
  and `proof` blocks outside function bodies
- `yield` outside a method whose signature `yields` or `lends`
- `break` and `continue` outside a loop, or inside a lambda in that loop
- `return`, `break`, `continue`, and `?` that would leave a `parallel` block,
  and `break`, `return`, and `?` in a `parallel for`
- `echo` inside a specification, which never runs
- a parameter named `result`

These need only the one definition's tree, so they belong to the parse stage
and are cached with it. They are a separate walk, not part of each parsing
function, so the parsing code does not thread a context through every call,
and each rule can be tested on its own. The walk handles only the nodes that
change the context, such as a lambda, a loop, or a `proof` block, and
leaves every other node to `Syntax_walk`'s one-level walk of a node's
expressions and statements, so a construct added to the tree is checked by
every rule without `Check` listing it.

## Errors and recovery

### Diagnostics

Diagnostics use the shared `Diagnostic` type from LEXER.md, with codes such
as `parser.unexpected_token` and `parser.needs_parentheses`. Each habit from
another language has a code of its own, such as `parser.increment`, so tools
and agents can match on it. Every diagnostic is an error. Messages are
written in sentences, as the lexer's are, which `Diagnostic.t` states for
every stage. When the parser knows what was meant, it gives an exact fix;
otherwise the message says what it expected, such as "Expected `=>` after
the patterns of a `match` arm, found a line break."

The expected tokens come from the parsing function that failed, which knows
what could come next. A generated parser can list them too, but a
hand-written one can phrase them in terms of the construct being parsed,
which is what an agent needs to act.

### Recovery

Brackets are always balanced, which gives the parser exact places to stop
after an error:

- **Inside brackets,** an error in an item skips to the next comma of the
  list, jumping over any brackets nested in it, and the items after the
  comma parse normally, so three bad arguments give three errors. The parser
  keeps the index of each opener's closer, computed once per definition, so
  each jump over a nested group is one step, not a search.
- **In a block, a trait, an `impl`, a capability, or a `match`,** an error
  skips to the next `NEWLINE` at the same depth, or to the closing `}`. The
  statement, member, or arm becomes an `Error` node, and the ones after it
  parse normally.
- **In a signature,** an error in a clause skips to the next clause keyword
  or to the body's `{` at the definition's own depth. A broken `requires`
  still leaves the body parsed.
- **At the top level,** an error ends the definition. The next one starts
  fresh, because `Split` already found it.

To avoid cascades:

- One error is reported per `Error` node. Errors are not reported inside a
  region that was skipped.
- A zero-width closer that the lexer inserted (see
  [LEXER.md](LEXER.md#brackets)) already has its error, so the parser does not
  report what is missing before it. Once a statement, member, or arm has
  consumed such a closer, what follows in it is not what the author wrote,
  so no more syntax errors are reported in it. This belongs to the one item:
  the items of a block inside it start afresh, and the item around the block
  is as it was before the block, unless the block's own `}` is one the lexer
  inserted.
- An empty interpolation already has the lexer's error, so the parser
  reports nothing for it, and nothing missing at the end of one that a line
  break cut off.
- A file reports at most 200 diagnostics, as in the lexer.

### Syntax from other languages

SYNTAX.md's rule is that each common habit gets its own error and an exact
fix. The lexer handles the habits it can fix from the tokens alone. The rest
need the tokens around them, so the parsing functions recognize each one at
the point where the ordinary grammar has already rejected a token, which
means a recognizer can never change what valid code means. Each then calls
`Habits`, which holds every message and fix in one place, and parsing goes on
as if the code had been fixed.

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
| `items.map { it.name }` | A statement that ends with a name or a member, followed on its line by a block that uses `it`, in its code or in its interpolations | `items.map(fn(item) { item.name })`, renaming every `it`, and naming the parameter with the singular of the collection's name where that is plain to work out, as `item` for `items` and `entry` for `entries`, and otherwise `element` |
| `x as Int64` | The reserved word `as` after an expression, with a type after it on the same line | `Int64.from(x)`, then `Int64.try_from(x)`, for a conversion that can lose information, as most casts can |
| `0.0 =>` in a pattern | A float literal where a pattern begins | None; the message says to match with a guard, as in `value if value == 0.0` |
| `loop {`, `const`, `static` | A `Reserved` token where a statement or a definition starts | `while true {`, `let` |
| `where` and the other reserved words | A `Reserved` token anywhere else | None; the message says the word is reserved |
| `elif` | The name `elif` starting a statement right after an `if` | `else if` |

Habits that are names, such as `null`, `nil`, and a second argument without a
label, depend on what names mean, so name resolution and type checking
report them (see [TYPECHECKER.md](TYPECHECKER.md)). These are
added once the compiler works:

| Written *Later* | Fix |
|---|---|
| `(a, b)` as an expression | "Truss has no tuples", pointing to a record |
| `pair.0` | "Truss has no tuples" |
| `Shape.Circle(radius)` in a pattern | `Circle(radius)` |
| `Shape::Circle` | `Shape.Circle` |
| `fn first<T>(...)`, `List<String>` in a type | `fn first[T](...)`, `List[String]` |
| `fn(x: Int64) { ... }` | `fn(x) { ... }`, since lambdas have no annotations |
| `println!(...)`, `vec![...]` | "Truss has no macros", with `Console.print_line(...)` and `[...]` |
| `!response is Ok(_)` | `!(response is Ok(_))`, because `!` binds tighter than `is` |
| `a ?? b`, `a ?: b` | `a.unwrap_or(b)` |

## Interfaces to other stages

- **The lexer** gives the parser one token array per file. The parser reads
  the source bytes only through spans, to build fixes and to keep each
  definition's source text.
- **Name resolution** gets one tree per definition and annotates its nodes.
  It decides `Bracket`, `Binding_or_constant`, and `Name` nodes. Type
  checking then reports bare arguments that name no parameter. Both are
  designed in [TYPECHECKER.md](TYPECHECKER.md).
- **A broken definition keeps what the parser read,** so that a mistake in
  one definition does not make every use of its name an error elsewhere:
  - a definition whose header did not parse is a `Definition_error` with its
    keyword and its name, when those were read
  - any other keeps its whole tree, with an `Error` node for each part that
    did not parse. A function whose body is missing keeps its signature,
    with an `Error` statement for the body.
  - its signature is as written when all of its diagnostics lie in its
    body, which is the usual case

  Nodes built for a habit, as if its fix had been applied, lie in the same
  signature or body as the habit's diagnostic, so a later stage that skips
  a signature or a body with a diagnostic never reports an error on code
  the parser made up.
  TYPECHECKER.md decides how resolution registers a broken definition and
  which of its parts it checks.
- **Hashing** walks the tree and ignores spans, `Parenthesized` nodes, blank
  lines, and how literals were written, as DESIGN.md's hash format says.
- **`truss fmt`** prints the tree, taking literals from the definition's
  source text and keeping a blank line where one was. A file with any parse
  error is left unchanged.
- **The language server** maps a position to a node through the spans, after
  adding each definition's base.
- **Incremental work.** The background process re-lexes a changed file, and
  `Parser.split` finds its pieces. A definition whose source text is
  unchanged keeps its tree and its diagnostics, which are the same because
  both are relative to the definition. Only the definitions whose text
  changed are parsed again, with `Parser.definition`.

## Testing

The tests follow IMPLEMENTATION.md's rules for testing: each states one fact
about a small input, and there are no golden files.

- **Focused tests** in `stage0/test/parser_tests.ml`, grouped by section of
  this document. A test gives a small input and asserts its tree, printed
  compactly by `Syntax_print`, or its one diagnostic: the code, where it
  starts, and the exact text each fix produces, which must parse cleanly.
- **The documents' examples parse cleanly.** Each ```` ```truss ```` block in
  a Markdown document at the root of the repository is a test of its own.
  Many blocks mix definitions with statements, or show a signature with no
  body to focus on it, so these tests split a block into pieces the way a
  file is split, and parse each as a `use` line, a definition, a signature
  without a body, or a statement. `Parser.example_definition` and
  `Parser.example_statement` parse the last three, and exist only for these
  tests and the tools that use the examples. Telling the kinds of piece
  apart is the job of `Reference.Snippet`, in the test-only `Reference`
  library.
- **Both parsers agree on the documents.** The `Reference` library is a
  parser built by Menhir from `grammar/truss.mly`, only for tests and tools.
  It parses each piece of each example with the grammar's entry point for its
  kind, and must accept every piece the hand-written parser accepts. A
  disagreement points at a bug in one of them, or at a difference between
  the code and GRAMMAR.md.
- **The documents agree with the code.** A test checks GRAMMAR.md's list of
  words the parser recognizes by spelling against the parser's own list.
- **Moving a definition changes nothing.** Adding lines above a definition
  gives an identical tree and identical diagnostics for it.
- **The fuzzer**, `stage0/tools/fuzz`, is run by hand. It also checks that
  mutated examples never make the parser raise, that every tree's spans are
  in bounds and inside the node around them, that every fix removes its
  diagnostic and adds no other, and that both parsers accept and reject the
  same mutated pieces. A lexer's fix is judged by the lexer's diagnostics
  alone, since closing a bracket can bring back a parser error the inserted
  closer was hiding. The reference grammar cannot judge everything: it
  accepts any name where a cost word goes, and reads a string as one token,
  so a piece whose error is in a `cost` clause or is about an interpolation
  is not compared, nor is one holding a closer the lexer inserted. Each
  problem the fuzzer finds becomes a focused test.
- **The benchmark**, `stage0/tools/benchmark`, measures how fast files lex
  and parse.
