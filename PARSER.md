# Truss Parser

This document describes the stage0 parser, in [`stage0/`](stage0). It
implements the syntactic grammar of [SPECIFICATION.md](SPECIFICATION.md) and
reads the tokens of [LEXER.md](LEXER.md). It takes one file's token array
and returns a syntax tree for each definition and a list of diagnostics. It
always returns a tree, even for a file with errors, so later stages can check
every definition that did parse.

The parser does not resolve names. `name[...]` is one node whether it is an
index or type arguments, and a bare name in a pattern is one node whether it
is a constant or a binding; name resolution decides without changing the
tree's shape (see
[SPECIFICATION.md](SPECIFICATION.md#constructs-resolved-after-parsing)).

**A definition's tree is a function of that definition's tokens.** A
definition that only moved has the same tree as before, so no result computed
from it is computed again. The parsing functions cannot break this: a cursor
holds only the definition's tokens, its base, and its own source text, so a
fix or a message can quote only the definition's bytes.

## Structure

```text
token array ──▶ Split ──one token slice per definition──▶ Parse ──▶ Check ──▶ tree
                  │                                         │          │
                  └──────────────────▶ diagnostics ◀────────┴──────────┘
```

### Splitting a file into definitions

The lexer guarantees balanced brackets, so definitions are found without
parsing them. A `NEWLINE` at bracket depth 0 ends a `use` line or a
definition, unless the next token is `{`, which starts a body on a line of
its own. No definition starts with `{`, so the rule never splits one in two.
A piece that cannot start a definition, such as a statement at the top
level, is still a piece, with one error, and the definitions around it are
unaffected.

### Methods inside a definition

A method declared in a trait, an `impl`, or a capability is a separate
definition. The container's parser records each method's token range by the
splitting rule and skips it, and each method is parsed from its own tokens.
So a method has its own base, text, and node ids, and an edit to one method
changes neither the other methods' trees nor the container's. A method
records its container, and has its container's visibility.

### Parsing one definition

- **Spans are relative to the definition.** The definition records its base,
  the absolute offset of its first token. Adding a line above a definition
  changes only its base, so its tree, and everything computed from it, is
  unchanged.
- **Its diagnostics are relative too,** with a type of their own, so they
  cannot be shown before `Parser.placed` adds the base. The one diagnostic
  that depends on the rest of the file, a `use` line after a definition, is
  reported by `Parser.parse`.
- **Interpolations are parsed from their own token arrays,** with the same
  base.

### Recursive descent with no backtracking

The parser is hand-written recursive descent, for its error messages. A
second parser, built by Menhir from `grammar/truss.mly` for tests and tools
only, is the reference: both must accept every piece of every example in the
documents, and accept and reject the same mutated pieces.

Every type and pattern position is determined by the token before it, so the
parser always knows which sub-grammar it is in. It never backtracks, and its
lookahead is at most three tokens, as for `[:]`. A map literal against a list
literal is decided by parsing each element with an optional `: value` and
checking that they agree. Each parsing function consumes a token or returns,
so parsing terminates.

### Limits on nesting

- **Nesting is limited to 256 levels,** counted at each expression, type,
  pattern, block, and prefix operator, so hostile input cannot make the
  parser, or a later stage that walks the tree, recurse without bound.
- **A chain is limited to 10,000 links,** such as the operands of `a + b + c`,
  which each nest the tree one level without passing through the nesting
  count.

## The syntax tree

### An abstract syntax tree, not a lossless one

Languages with comments need a lossless tree, because comments can appear
anywhere and the formatter must keep them. Truss has no comments, and
`truss fmt` decides all whitespace, so the tree records only what the
formatter needs beyond the constructs: each literal's spelling, through its
span; whether a blank line preceded each statement, member, arm, and
definition; and parentheses, as `Parenthesized` nodes. Trailing commas, the
optional first `|`, and line breaks are layout.

### Shape

The tree types are in
[`stage0/parser/syntax/syntax.mli`](stage0/parser/syntax/syntax.mli).

- **Constructs with the same syntax are one node.** `Bracket` is an index or
  type arguments, and `Name` a variable, a function, a type, or a variant.
  Later stages record their results in tables keyed by node id, and never
  rebuild the tree.
- **Every node has an id,** unique within its definition and assigned from one
  counter after its children. The same tokens produce the same ids, so a
  definition that only moved keeps them, and a later stage stores its results
  in a dense table indexed by id. A node the parser extends, as when a
  trailing lambda joins an expression, keeps its id.
- **Types inside expressions are expressions.** `List[String]` in
  `List[String].with_capacity(64)` is a `Bracket` over two `Name`s.
- **Clauses keep source order,** since the order within a kind matters.
- **An operation records its operator's span,** so an error about a
  combination points at the operator.
- **Types make invalid trees unrepresentable.** An `impl` cannot hold a law,
  and a function always has a body.
- **Every part that can fail to parse has an `Error` case,** with the span it
  covered, and the rest of the tree is built as usual.

## Operators that need parentheses

A parser can enforce a partial order of precedence by encoding it in the
grammar, as `truss.mly` does, but then `flags & mask == 0` is a syntax error
at the `==`, before the parser has the operands a good fix needs. So the
parser uses a total order, Rust's where Truss defines none, and `Operators`
then checks each operation against its operands.

- **Each grouping is a separate fix.** Where languages group a combination
  differently, the diagnostic offers each grouping, so an agent chooses the
  one it meant and does not rely on a table it may misremember. The
  groupings come from a table of the precedence that Rust, C, Go, and Swift
  give each operator.
- **A fix inserts only parentheses,** except for a chained comparison, and
  introduces no new combination that needs them.
- **A grouping that has no syntax is not offered,** as the one that would put
  `& y` inside the pattern of `x is P & y`.
- **Every combination is reported,** and applying one fix leaves the other
  errors unchanged.

`return`, `echo`, and quantifiers are parsed wherever an operand begins, with
their bodies at the lowest level, and `Operators` reports one used as an
operand elsewhere, with a fix that adds parentheses.

## Brackets and statements

- A range may omit an end only directly in brackets: the parser passes a flag
  to the range level that allows a missing operand before `]` or `,`.
- `for i in 0.. {}` is reported at the `..`: the grammar takes the `{}` as
  the range's end, which leaves the loop without a body.
- A statement is chosen by its first token. The function that expects a body
  skips one `NEWLINE` before its `{`, and is called only where a body must
  follow.
- A rule the grammar leaves to a check, such as `opaque` only before `type`,
  is checked while the definition is parsed, where the tokens are available
  for fixes.

### Cost clauses

`Cost_word` spells each word of a `cost` clause once, and the parser compares
names against that table. A misspelling gets a fix when exactly one word is
within an edit distance of 2, and the parser continues with that word.

## Checks on a whole definition

`Check` walks a definition's tree once with a small context, such as whether
the node is in a specification, a test, a loop, a lambda, or a `parallel`
branch, and reports the placement rules of SPECIFICATION.md that need only
that tree, such as `assert` outside tests and proofs. They are a separate
pass, so the parsing code threads no context and each rule is tested on its
own. The pass handles only the nodes that change the context, and delegates
every other node to `Syntax_walk`'s traversal, so a construct added to the
tree is checked without a change to `Check`.

`==>` and quantifiers over a type are reported only in tests, constants, and
defaults: a function whose signature mentions a type of specifications has a
body that is a specification, and only the type checker knows the types.

## Errors and recovery

Diagnostics use the lexer's `Diagnostic` type. A diagnostic has an exact fix
when the parser can infer the intended code, and otherwise states the tokens
expected in terms of the construct, which an agent can act on.

Brackets are always balanced, so recovery has exact synchronization points:

- **In brackets,** an error skips to the next comma at the same depth, so
  three invalid arguments give three errors. Each opener's closer is
  computed once per definition, so stepping over a nested group is one step.
- **In a block, a trait, an `impl`, a capability, or a `match`,** an error
  skips to the next `NEWLINE` at the same depth, or the closing `}`.
- **In a signature,** an error skips to the next clause keyword or the body's
  `{`, so a `requires` that does not parse leaves the body parsed.
- **At the top level,** an error ends the definition, and `Split` has
  already found the next one.

To avoid cascades, one error is reported per `Error` node, and none for
skipped tokens. A closer the lexer inserted already has its error, so once an
item has consumed one, the rest of that item reports no syntax errors.

### Habits of other languages

Habits made of valid tokens, such as `|x| x + 1` or `Point { x: 1.0 }`, are
recognized by the parsing functions at the point where the grammar has
already rejected a token, so a recognizer never changes the meaning of valid
code. Each calls `Habits`, which holds every message and fix, and the parser
builds the tree of the fixed code and continues. Habits that are names, such
as `null`, depend on name resolution, which reports them.

## Interfaces to other stages

- **Name resolution** records the referent of each name in a table keyed by
  node id (see [TYPECHECKER.md](TYPECHECKER.md)).
- **A definition with a syntax error keeps the parts that parsed,** so an
  error in one definition does not make every use of its name an error. A
  definition whose header did not parse is a `Definition_error` with its
  keyword and name, when those parsed. Every definition lists in `recovered`
  the spans where the parser recovered: each `Error` node, each inserted
  closer it consumed, and each diagnostic whose code means the source is not
  valid Truss. A part of the definition matches its source text exactly when
  no recovery lies in its span. Which codes are recoveries is one exhaustive
  match in `Cursor`, so a new code cannot be added without deciding.
- **The code database** parses a whole file when its text changes. A
  definition whose tree equals the one before invalidates nothing computed
  from it.

## Not built

- **Parsing only the definitions whose text changed.** A definition's tree and
  relative diagnostics are functions of its tokens, so they could be cached by
  its text. The tokens have absolute spans, so reuse would need a copy of
  each slice with relative spans. Nothing needs it yet.
