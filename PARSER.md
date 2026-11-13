# Truss Parser

The stage0 parser implements the syntactic grammar of
[SPECIFICATION.md](SPECIFICATION.md) over the tokens of
[LEXER.md](LEXER.md). It takes one file's token array and returns a syntax
tree for each definition and a list of diagnostics. It always returns a
tree, even for a file with errors, so later stages can check every
definition that did parse.

The parser does not resolve names. `name[...]` is one node whether it is an
index or type arguments. Name resolution decides without changing the
tree's shape (see
[SPECIFICATION.md](SPECIFICATION.md#constructs-resolved-after-parsing)).

**A definition's tree is a function of that definition's tokens.** Spans and
node ids are relative to the definition, so a definition that only moved has
the same tree as before, and nothing computed from it is computed again.

## Structure

```text
token array ──▶ Split ──one token slice per definition──▶ Parse ──▶ Check ──▶ tree
                  │                                         │          │
                  └──────────────────▶ diagnostics ◀────────┴──────────┘
```

- **Split** finds definitions without parsing them, since the lexer
  guarantees balanced brackets: a `NEWLINE` at depth 0 ends a definition
  unless the next token is `{`. A method inside a trait, an `impl`, or a
  capability is a definition of its own, so an edit to one method changes no
  other tree.
- **Parse** is hand-written recursive descent, for its error messages. It
  never backtracks: every type and pattern position is determined by the
  token before it. A Menhir grammar, `grammar/truss.mly`, is the reference
  that tests compare it against.
- **Check** walks a definition's tree once and reports the placement rules
  that need only that tree, such as `assert` outside tests and proofs, so
  the parsing functions thread no context.

**Nesting is limited** to 256 levels and a chain such as `a + b + c` to 10,000
links, so hostile input cannot make the parser, or a later stage that walks
the tree, recurse without bound.

## An abstract syntax tree, not a lossless one

Languages with comments need a lossless tree, because comments can appear
anywhere and the formatter must keep them. Truss has no comments, and
`truss fmt` decides all whitespace, so the tree records only what the
formatter needs beyond the constructs: each literal's spelling, blank lines
between items, and parentheses.

- **Constructs with the same syntax are one node,** such as `Bracket` for an
  index or type arguments. Later stages record their decisions in tables
  keyed by node id and never rebuild the tree.
- **Every part that can fail to parse has an `Error` case,** and the rest of
  the tree is built as usual.

## Operators that need parentheses

A grammar can encode a partial order of precedence, as `truss.mly` does, but
then `flags & mask == 0` is a syntax error at the `==`, before the parser
has the operands a good fix needs. So the parser parses with a total order
and then checks each operation against its operands. Where languages group a
combination differently, the diagnostic offers each grouping as a separate
fix, so an agent chooses the one it meant rather than relying on a table it
may misremember.

## Errors and recovery

A diagnostic has an exact fix when the parser can infer the intended code,
and otherwise states the tokens expected in terms of the construct.

Brackets are always balanced, so recovery has exact synchronization points:
the next comma in brackets, the next `NEWLINE` in a block, the next clause
keyword in a signature, and the next definition at the top level. One error
is reported per `Error` node, and none for skipped tokens, so one mistake
gives one error.

Habits made of valid tokens, such as `|x| x + 1` or `Point { x: 1.0 }`, are
recognized only where the grammar has already rejected a token, so a
recognizer never changes the meaning of valid code. The parser builds the
tree of the fixed code and continues.

## Interfaces to other stages

- **Name resolution** records the referent of each name in a table keyed by
  node id (see [TYPECHECKER.md](TYPECHECKER.md)).
- **A definition with a syntax error keeps the parts that parsed,** and
  lists the spans where the parser recovered. A part whose span holds no
  recovery matches its source exactly, so the type checker can check it, and
  an error in one definition does not make every use of its name an error.
- **The code database** parses a whole file when its text changes. A
  definition whose tree equals the one before invalidates nothing.

## Not built

- Parsing only the definitions whose text changed.
