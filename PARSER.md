# Truss Parser

This document designs the stage0 parser. It implements the syntactic grammar
in [GRAMMAR.md](GRAMMAR.md), reads the tokens described in
[LEXER.md](LEXER.md), and follows the rules in [SYNTAX.md](SYNTAX.md) and
[DESIGN.md](DESIGN.md). Where this design departs from those documents, it
says so. Nothing is built yet.

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

| OCaml module | Job |
|---|---|
| `Syntax` | The tree types, shared by every later stage |
| `Split` | Finds the `use` lines and each definition's token slice |
| `Cursor` | Reads a token slice: the current token, lookahead, and `NEWLINE` helpers |
| `Parse_type`, `Parse_pattern`, `Parse_expression`, `Parse_definition` | Recursive descent, one module per part of the grammar |
| `Operators` | The operator table and the check for combinations that need parentheses |
| `Habits` | Recognizers and fixes for syntax from other languages |
| `Check` | Rules that need the whole tree of a definition |
| `Syntax_print` | Prints a tree as an S-expression for tests, and as Truss for round trips |
| `Parser` | The entry point: `Parser.parse : Source.t -> Token.t array -> Syntax.file * Diagnostic.t list` |

The parser is one dune library that depends on `Token`, `Source`, and
`Diagnostic`. `Syntax` is its own library, so that name resolution, the
formatter, and the language server depend on the tree without depending on
the parser.

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
  the tree gives it to every later stage for free. Diagnostics add the base
  back, since tools and editors work in file offsets.
- **The definition keeps its source text,** the bytes from its first token to
  the end of its last token. `truss fmt` prints each literal from its span, as
  LEXER.md describes, and the spans are relative to this text.
- **Interpolations are parsed from their own token arrays.** Each one is
  parsed as an expression by a fresh `Cursor` over the interpolation's tokens,
  as LEXER.md planned. The spans of those tokens are absolute, and are made
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
| A map literal against a list literal | Parse the first element, then look for `:` |
| A trait method with its body on the next line, against the next member | `NEWLINE` then `{` |
| A function name against a method name in a definition | `UPPER`, or `LOWER` then `::`, starts a type head |
| A range with no start in brackets, `items[..3]` | `..` or `..=` right after `[` |

Each parsing function consumes at least one token or returns, so parsing
always ends. Nesting is limited to 256 levels of brackets and blocks, so
hostile input cannot overflow the stack. Like the lexer's limit of 32 nested
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

The tree types follow GRAMMAR.md closely. A sketch of the main ones:

```ocaml
type span = { start : int; stop : int }   (* relative to the definition's base *)
type name = { text : string; span : span }
type path = { modules : name list; last : name }   (* standard::json::parse *)

type expression = { kind : expression_kind; span : span }
and expression_kind =
  | Integer of Z.t
  | Float of { significand : Z.t; exponent : Z.t }
  | String of string_literal                (* tagged or not *)
  | True | False | Todo | Unreachable | Break | Continue
  | Self_value | Self_type
  | Name of path                            (* items, json::parse, Point, geometry::Shape *)
  | Member of expression * name             (* config.port, Shape.Circle, Self.Key *)
  | Bracket of expression * bracket_item list   (* an index or type arguments *)
  | Call of expression * argument list
  | Try of expression                       (* ? *)
  | With of expression * update list
  | Prefix of prefix * expression           (* - ! ~ *)
  | Mode of mode * expression               (* mut own *)
  | Any of expression
  | Binary of binary * expression * expression   (* includes ==> *)
  | Is of expression * pattern
  | Range of { start : expression option; stop : expression option; inclusive : bool }
  | Quantifier of { kind : quantifier; binder : binder; body : expression }
  | Echo of expression
  | Return of expression option
  | Parenthesized of expression
  | List of expression list
  | Map of (expression * expression) list   (* [:] is Map [] *)
  | Lambda of { parameters : pattern list; body : block }
  | If of { condition : expression; then_ : block; else_ : else_branch option }
  | Match of { scrutinees : expression list; arms : arm list }
  | Provide of { implementations : expression list; body : block }
  | Block of block
  | Error                                   (* a part that did not parse *)

and argument = { label : name option; value : expression }
and bracket_item =
  | Item of expression                      (* 0, String, ..3 *)
  | Constraint of name * type_expression    (* Element = Int64 *)
```

- **Constructs that parse the same are one node.** `Bracket` is an index or
  type arguments, `Name` is a variable, a constant, a function, a type, or a
  variant, and `Member` is a field, a variant under its type, an associated
  type, or the start of a method call. Name resolution and type checking
  annotate these nodes; they never rebuild them.
- **Types inside expressions are expressions.** In
  `List[String].with_capacity(64)`, `List[String]` is a `Bracket` over two
  `Name`s. Name resolution reads it as a type. Type positions, such as
  annotations and signatures, have their own `type_expression` nodes.
- **Patterns have one node for a bare name.** `Binding_or_constant of name`
  is decided by name resolution, as the grammar says. Range ends are their
  own `Constant` nodes, since a name there can only be a constant.
- **Clauses are typed, not generic.** A function's clauses are kept as a
  list in the order written, since the order of clauses of one kind matters,
  but each is a specific constructor: `Uses`, `Requires`, `Ensures`,
  `Decreases`, or `Cost` with a parsed resource and bound. The hash sorts them
  by kind and keeps the order within each kind.
- **Every definition, statement, member, arm, expression, pattern, and type
  has an `Error` case.** A part that did not parse becomes an `Error` node with
  the span it covered, and the rest of the tree is built around it.

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
Rust, and Swift most often share. Then `Operators.check` walks each
`Binary`, `Range`, and `Is` node, and reports:

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
table it may misremember. Each fix inserts only parentheses, so applying it
never changes anything else.

### The forms at the lowest level

- **`return` and `echo`** take an expression at the lowest level. A `{` right
  after `return` starts the value only when no `NEWLINE` comes between them,
  which the lexer already decides: `return` can end a statement and `{` can
  begin one, so a line break between them is a `NEWLINE`.
- **Quantifiers** may also be the last operand of `&&`, `||`, or `==>`. When
  the operand parser finds `forall` or `exists`, it parses the binder and the
  body at the lowest level, and the body takes everything up to the end of
  the expression. `Operators.check` then reports a quantifier anywhere else,
  such as `count + forall ...`, with a fix that puts it in parentheses.
- **`if`, `match`, `provide`, blocks, and lambdas** are primaries, so they
  combine with operators like any other operand.

### Brackets after an expression

Brackets after an expression hold a list of items, each an expression or an
associated-type constraint. Inside them, and only there, a range may leave
out its start or its end: the parser passes a flag to the range level that
allows a missing operand when the next token is `]` or `,`. A range with a
missing end anywhere else is an error that says open-ended ranges are only
for brackets.

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
`public opaque`, or `internal`. The rules that the grammar leaves to a check,
such as `opaque` only before `type`, `self` only as a method's first
parameter, `uses` and `decreases` at most once, and `finite` only for `time`,
are checked as the definition is parsed, where the tokens and their spans are
at hand.

### Cost clauses

The words of a `cost` clause are names to the lexer. The parser reads
`cost [amortized] resource bound`, where `amortized`, `time`,
`allocations`, `allocated_bytes`, `calls`, `O`, and `finite` must be spelled
exactly. A misspelling gets a fix when one word is close, such as `allocation`
for `allocations`. `cost potential expression` is accepted only on a type.
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
- `assert` outside tests, theorems, and proofs, and `proof` blocks outside
  function bodies
- `yield` outside a method whose signature `yields` or `lends`
- `break` and `continue` outside a loop, or inside a lambda in that loop
- `return`, `break`, `continue`, and `?` that would leave a `parallel` block,
  and `break`, `return`, and `?` in a `parallel for`
- `echo` inside a proof

These need only the one definition's tree, so they belong to the parse stage
and are cached with it. They are a separate walk, not part of each parsing
function, so the parsing code does not thread a context through every call,
and each rule can be tested on its own.

## Errors and recovery

### Diagnostics

Diagnostics use the shared `Diagnostic` type from LEXER.md, with codes such
as `parser.unexpected_token` and `parser.needs_parentheses`. Every diagnostic
is an error. When the parser knows what was meant, it gives an exact fix;
otherwise the message says what it expected, such as "expected `=>` after
the patterns of a `match` arm".

The expected tokens come from the parsing function that failed, which knows
what could come next. A generated parser can list them too, but a
hand-written one can phrase them in terms of the construct being parsed,
which is what an agent needs to act.

### Recovery

Brackets are always balanced, which gives the parser exact places to stop
after an error:

- **Inside brackets,** an error skips to the matching closer. The parser keeps
  the index of each opener's closer, computed once per definition, so this is
  a jump, not a search.
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
  report what is missing before it.
- A file reports at most 200 diagnostics, as in the lexer.

### Syntax from other languages

SYNTAX.md's rule is that each common habit gets its own error and an exact
fix. The lexer handles the habits it can fix from the tokens alone. The rest
need the tokens around them, so `Habits` recognizes them where the parser
fails. A recognizer is tried only after the ordinary grammar has rejected a
token, so it can never change what valid code means.

The first version handles the habits SYNTAX.md lists that reach the parser:

| Written | Recognized by | Fix |
|---|---|---|
| `i++`, `i--` | A `Foreign` token after an expression | `i += 1`, `i -= 1` |
| `--x` | A `Foreign` token before an expression | `-(-x)` |
| `A => 1,` | `,` after a `match` arm's body | Remove the `,` |
| `x ? a : b` | `?` followed by an expression and `:` | `if x { a } else { b }` |
| `let mut x` | `mut` right after `let` | `var x` |
| `&x`, `&mut x` | `&` where an expression must begin | `x`, `mut x` |
| `\|x\| x + 1` | `\|` where an expression must begin | `fn(x) { x + 1 }` |
| `Point { x: 1.0, y: 2.0 }` | An `UPPER` name, then `{`, a name, and `:`, on one line | `Point(x: 1.0, y: 2.0)` |
| `parse::<Int64>(text)` | `::` followed by `<` | `parse[Int64](text)` |
| `items.map { it.name }` | A call with no parentheses, followed by a block that uses `it` | `items.map(fn(item) { item.name })` |
| `x as Int64` | The reserved word `as` after an expression | `Int64.from(x)` |
| `loop {`, `const`, `static`, `where`, and the other reserved words | A `Reserved` token | A fix for each, such as `while true {` for `loop` |
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
- **Hashing** walks the tree and ignores spans, `Parenthesized` nodes, blank
  lines, and how literals were written, as DESIGN.md's hash format says.
- **`truss fmt`** prints the tree, taking literals from the definition's
  source text and keeping a blank line where one was. A file with any parse
  error is left unchanged.
- **The language server** maps a position to a node through the spans, after
  adding each definition's base.
- **Incremental work.** The background process re-lexes a changed file, and
  `Split` finds its definitions. A definition whose source text is unchanged
  keeps its tree, which is the same tree because spans are relative. Only the
  definitions whose text changed are parsed again.

## Testing

- **Golden tests.** Small `.truss` files, each with its tree as an
  S-expression from `Syntax_print` and its diagnostics, compared with dune's
  `diff` actions, as for the lexer.
- **The documents as a corpus.** Every ```` ```truss ```` block in
  SYNTAX.md, DESIGN.md, and GRAMMAR.md must parse with no diagnostics. Many
  blocks mix definitions with statements, or show a signature with no body to
  focus on it, so the corpus test parses each block with a snippet entry
  point that accepts definitions, signatures without bodies, and statements.
  That entry point exists only for this test.
- **Both parsers.** The corpus, and corpus files with random mutations, go to
  both the hand-written parser and a parser built by Menhir from
  `grammar/truss.mly`. Any file one accepts and the other rejects points at a
  bug in one of them, or a disagreement between the code and GRAMMAR.md.
  The Menhir parser is built only for tests, with the latest Menhir release.
- **Round trips.** Printing a tree as Truss and parsing the output gives the
  same tree, apart from spans. This printer is the start of `truss fmt`.
- **Fixes work.** Every fix in the test corpus is applied, the result is
  parsed again, and the diagnostic must be gone with no new one in its place.
  Where a diagnostic offers several fixes, each is tried.
- **Robustness.** Random token sequences and mutated corpus files never raise
  an exception, always finish, and always give a tree whose spans are in
  bounds and in order.
- **Moving a definition changes nothing.** Adding lines above a definition
  gives an identical tree for it.
