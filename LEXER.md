# Truss Lexer

This document describes the stage0 lexer, in [`stage0/`](stage0). It
implements the lexical grammar in [GRAMMAR.md](GRAMMAR.md), and the rules in
[SYNTAX.md](SYNTAX.md) and [DESIGN.md](DESIGN.md) behind it.

## What the lexer does

The lexer takes the bytes of one source file and returns an array of tokens and
a list of diagnostics. It always returns tokens, even for a broken file, so
that later stages can report more than the first error.

The lexer:

- checks the source text: UTF-8, the byte order mark, line breaks, and
  forbidden characters
- splits it into tokens: names, keywords, numbers, strings with their
  interpolations already lexed, and punctuation
- checks each name on its own: ASCII and the case rules
- decides which line breaks are `NEWLINE` tokens, and matches brackets
- recognizes habits from other languages and reports each with an exact fix

It does not:

- know the grammar, beyond brackets and strings
- decide what `name[...]` means, or what type a literal has
- round float literals. The type checker does that once it knows the type.

**The lexer is a pure function of one file's text.** It gets no feedback from
the parser and has no modes beyond brackets and strings. This is what lets the
line-break rule be explained by tokens alone, as DESIGN.md promises. It makes
lexing results cacheable by the file's hash, and it lets the lexer be ported
directly when the compiler is rewritten in Truss. For the same reason the lexer
has no contextual keywords: the words of `cost` clauses, `result`, and `old`
are ordinary names to it, and the parser recognizes them by their spelling.

## Structure

```text
bytes ──▶ Scanner ──one raw token at a time──▶ Layout ──▶ token array
             │                                    │
             └────────────▶ diagnostics ◀─────────┘
```

The **scanner** turns bytes into raw tokens. Each raw token records whether a
line break came before it. **Layout** inserts `NEWLINE` tokens and matches
brackets. The two are separate stages of one pipeline, not two passes over
the file:

- **Layout pulls from the scanner.** The scanner's interface is
  `Scanner.next : Scanner.t -> raw_token`. Layout keeps the previous token and
  the bracket stack, which is all the line-break rule needs, and asks for the
  next raw token only when it is needed. No array of raw tokens is ever built,
  and the bytes are read once.
- **The lexer's output is one array of final tokens.** Layout appends to it as
  it goes. The parser receives the whole array rather than pulling tokens
  through the pipeline, because it is the one buffer the later stages share:
  the parser's error recovery looks ahead to the next definition, `truss fmt`
  and the language server reuse the tokens, and an interpolation's tokens are
  already a nested array. Building it costs one array of tokens per file,
  which is small next to the syntax tree built from it.
- **Only a broken file is read twice.** If brackets are still open at the end
  of the file, the lexer runs again with bracket recovery turned on (see
  [Brackets](#brackets)). Valid files never pay for this.

Keeping the stages apart still pays even though they run together. The
line-break rule is a small function of two adjacent tokens and the bracket
stack, which can be tested and explained on its own, and the scanner needs no
lookahead across lines.

| OCaml module | Job |
|---|---|
| `Unicode` | Character properties, from tables generated for the pinned Unicode version |
| `Source` | A file's path and bytes, and a table of line starts for turning offsets into lines and columns |
| `Diagnostic` | Errors with spans and fixes, shared by every stage of the compiler |
| `Token` | The token types, and the lists of keywords and punctuation |
| `Scanner` | Bytes to raw tokens |
| `Layout` | `NEWLINE` tokens and bracket matching |
| `Lexer` | The entry point: `Lexer.lex : Source.t -> Token.t array * Diagnostic.t list` |

Each module is its own dune library under `stage0/`, so the parser depends
only on `Token` and `Lexer`, and the formatter and language server can reuse
`Source` and `Diagnostic`. The scanner's library holds:

| Module | Job |
|---|---|
| `Cursor` | The scanner's state and byte-level helpers |
| `Source_text` | UTF-8, forbidden characters, line breaks, and removing trivia |
| `Trivia` | Comments, `;`, and characters Truss does not use |
| `Strings` | Ordinary and raw strings, escapes, interpolations, and character literals |
| `Names`, `Numbers` | The checks on one name or one number literal |
| `Scanner` | The loop that finds the next token, and punctuation |

The scanner's loop looks at each position once and decides there whether
it holds trivia or the start of a token, so no second place has to agree
with it. It stops at every line break: between tokens, the line break is
trivia, and in an interpolation it is an error. Each scanner for a
construct that must end on its line, such as an interpolation or an
ordinary string, returns whether it was `Closed` or `Cut_off` by an error
already reported, and an enclosing construct that must end on its line
then ends too, without another error. The dune
project is at the repository root, so that tests can read the documents.
`stage0/bin/truss_lex.ml` builds `truss-lex`, which prints a file's
diagnostics, as JSON with `--json`, and its tokens with `--tokens`.

The scanner uses Layout too: it lays out each interpolation's tokens as it
reads them, as [Interpolation](#interpolation) asks, so `Layout` defines the
input both of its uses take.

### Hand-written, not generated

A hand-written scanner fits better than one generated by a tool such as
sedlex:

- **The hard parts are not regular.** Each raw string chooses its own
  delimiter length. Interpolations nest strings to any depth. A raw string's
  indentation is known only once its closing delimiter is found. And most
  errors need an exact fix. In sedlex all of these become hand-written code
  around the generated matcher anyway.
- **The Unicode version must be the language's.** sedlex's identifier classes
  come from whatever Unicode version that sedlex release was built with.
  Truss needs the version the language pins.
- **It ports to Truss.** The lexer will be rewritten in Truss to bootstrap the
  compiler. A scanner written as an index moving over a byte string ports
  line by line. A sedlex specification does not.
- **One fewer dependency, and no ppx.**

The cost is a few hundred more lines than a sedlex specification. They are in
the part of the compiler that is easiest to test exhaustively.

## Source text

### Decoding

- The scanner keeps an index into the file's bytes. An ASCII byte, which is
  nearly every byte in practice, is handled directly. A byte of 0x80 or
  above starts a UTF-8 sequence, which is decoded strictly. Overlong forms,
  encoded surrogates, values above U+10FFFF, and truncated sequences are
  errors.
- Each maximal run of invalid bytes is one error, and is skipped.
- A byte order mark at offset 0 is skipped. Anywhere else U+FEFF is a
  default-ignorable character, so it is forbidden.

### Line breaks

- A line feed is a line break. A carriage return followed by a line feed is
  one line break, and its span covers both bytes.
- A carriage return on its own is an error. The fix replaces it with a line
  feed, and the scanner treats it as a line break so that the lines after it
  lex normally.
- The source is never rewritten. Every offset points into the original
  bytes, so a file with carriage returns reports the same positions an editor
  shows.
- Inside a raw string, every line break becomes a line feed in the string's
  value.

### Forbidden characters

The forbidden characters are those listed in GRAMMAR.md: the characters with
the `Bidi_Control` property, control characters other than tab, line feed, and
a carriage return before a line feed, and every other
`Default_Ignorable_Code_Point` except U+200C, U+200D, and the variation
selectors. The characters left legal can still carry hidden data in a string,
as DESIGN.md says. Truss does not restrict where they go, since no other
language does and the rules would have to know every emoji and script.

- The scanner checks every character as it reads it, in code and in strings
  alike.
- A run of consecutive forbidden characters is one error. The message names
  each one by code point and name, such as "U+202E RIGHT-TO-LEFT OVERRIDE",
  and says why it is forbidden. The `Unicode` module keeps names only for the
  characters such messages can mention.
- In code, the fix deletes the characters. In an ordinary string, the fix
  replaces each one with its `\u{...}` escape. A raw string has no escapes, so
  its message suggests an ordinary string, with no automatic fix.
- Otherwise the scanner skips the characters, so lexing goes on as if they
  were not there.

### Positions

- A span is a pair of byte offsets into the file: the start, included, and
  the end, excluded.
- Lines and columns are worked out only when a diagnostic is shown, from the
  table of line starts. Lines count from 1, and columns count Unicode scalar
  values from 1. JSON diagnostics also carry byte offsets, and fixes are
  always byte ranges. The language server converts to whatever column
  encoding its client asks for.
- Spans are absolute within the file. Positions relative to a definition (see
  [DESIGN.md](DESIGN.md#incremental-builds)) are the job of the stage that
  splits a file into definitions. The lexer does not know where definitions
  start.

## Tokens

```ocaml
type span = private { start : int; stop : int }   (* made only by Source.span *)

type token = {
  kind : kind;
  span : span;
  line_break_before : bool;   (* a line break between this token and the one before *)
  blank_line_before : bool;   (* two or more *)
}

and kind =
  | Upper of string                   (* Point, UInt8, O *)
  | Lower of string                   (* items, time, result *)
  | Underscore
  | Keyword of keyword
  | Reserved of reserved              (* as, async, loop, ... *)
  | Integer of Z.t
  | Float of Decimal.t                (* significand × 10^exponent, exactly *)
  | String of string_literal
  | Punctuation of punctuation
  | Foreign of foreign                (* ++, --, and others the parser reports *)
  | Newline
  | End_of_file

and string_literal = {
  tag : (string * span) option;
  form : form;
  first : text;
  rest : (interpolation * text) array;
}

and form = Ordinary | Raw of { quotes : int; dollars : int; multi_line : bool }
and text = { value : string; span : span }
and interpolation = { tokens : token array; span : span }
```

- **Literals keep their value.** A literal's spelling is always the source
  text under its span, which is what `truss fmt` prints back. Hashes use
  values, so `0xFF` and `255` hash the same, and so do a raw string and an
  ordinary string with the same text.
- **Integers are Zarith integers of any size.** Whether one fits its type is
  decided by the type checker.
- **Floats are kept exact.** A float literal takes its type from context.
  Rounding a decimal to `Float64` and then to `Float32` can give a different
  answer from rounding it straight to `Float32`. So the lexer keeps the exact
  decimal value, and the type checker rounds once, to the type it decides.
  The significand has its trailing zeros removed, so `1.50` and `1.5` have
  the same value.
- **A string's texts and interpolations alternate,** starting and ending
  with a text, which is the shape of a `Template`: `"a${x}b"` has `first`
  `"a"` and `rest` `[(x, "b")]`, and `"${x}"` has two empty texts. The type
  allows no other shape. This holds for untagged strings too.
- **Types rule out what must not happen.** A span is built only by
  `Source.span`, which checks `start <= stop`. `Decimal.make` removes
  trailing zeros, and is the only way to build a float's value. Brackets are
  `Open` and `Close` of a `bracket`, so matching them is comparing two
  values.
- **An interpolation is a nested token array,** already laid out. The parser
  parses each one as an expression from its own array. This matches
  GRAMMAR.md's single `STRING` token, keeps the outer token stream flat, and
  confines an error inside an interpolation to that interpolation.
- **A tag is only the name.** In `database::SqlQuery"..."`, `database` and
  `::` are ordinary tokens before the string, and the parser joins them.
- **`line_break_before` drives the layout pass.** `blank_line_before` lets
  `truss fmt` keep blank lines, which it does, collapsing a run of them to
  one, as Go, Rust, and Gleam do. Hashes ignore both.
- **`keyword`, `reserved`, `punctuation`, and `foreign` have one constructor
  per item,** each built from a single list in `Token`. A test reads the
  keyword and punctuation blocks in GRAMMAR.md and checks them against these
  lists, so the documents and the code cannot drift apart.

## Names and keywords

### Scanning

- A name is ASCII letters, digits, and `_`, starting with a letter. The
  scanner reads a word as Unicode defines one, an `XID_Start` character and
  then `XID_Continue` characters, so that `café` is one name with one error,
  not the name `caf` followed by a stray character.
- `_` on its own is `Underscore`. `_` followed by name characters is an
  error, since names cannot start with `_`. The fix removes the leading
  underscores.
- A name is looked up in the keyword table.
- A reserved word becomes a `Reserved` token, and the **parser** reports it.
  A good fix depends on the construct around it: `x as Int64` becomes
  `Int64.from(x)`, and `loop {` becomes `while true {`.

### Classification and checks

A name that is not a keyword is an `Upper` name if its first letter is
uppercase, and a `Lower` name otherwise. It is then checked:

1. **ASCII.** A letter outside ASCII is an error that names it. There is no
   fix, since no spelling can be chosen for the author.
2. **Case rules.** An `Upper` name contains no `_`. A `Lower` name contains no
   uppercase letter, does not start or end with `_`, and has no `__`.
   Each violation gets a fix that rewrites the name into the right form:

   | Written | Fix |
   |---|---|
   | `userName` | `user_name` |
   | `MAX_SIZE` | `max_size`. All capitals with `_` is a constant from another language. |
   | `Http_Client` | `HttpClient` |
   | `count_`, `user__name` | `count`, `user_name` |

   Every use of a misspelled name gets the same fix, so applying every fix in a
   file renames the name consistently. Renaming a definition across files is
   the rename tool's job.

Each check depends only on the name, so each spelling is checked once per
file.

## Numbers

### Scanning

A number is scanned wide and then checked, so that `3u8`, `0xFG`, `1_`, and
`0b102` each become one token with one precise error, instead of a number
followed by a stray name:

1. Read the maximal run of ASCII letters, digits, and `_` that starts at the
   digit.
2. If that run is only decimal digits and `_`, and it is followed by `.` and a
   digit, read the fraction the same way.
3. If the run so far ends in `e` and is followed by `+` or `-` and a digit,
   read the sign and the digits after it as the exponent.
4. Check the whole text against GRAMMAR.md's rules for numbers, and compute
   the value from the digits with the `_`s removed.

So `1..2` is `1`, `..`, `2`; `1.max(2)` is `1`, `.`, `max`, ...; and `1.0.max`
is `1.0`, `.`, `max`.

### Errors

| Written | Error and fix |
|---|---|
| `3u8`, `1.5f`, `10i64`, `100L` | Literals have no type suffixes. The fix writes `3`, and the message shows how context gives the type: `let small: UInt8 = 3`. |
| `0X1F`, `0B1`, `0O7`, `1E9` | Prefixes and exponents are lowercase: `0x1F`, `0b1`, `0o7`, `1e9`. |
| `0x`, `0b`, `1e` | The digits are missing. |
| `0b102`, `0o8`, `0xFG` | The error points at the digit the base does not allow. |
| `1__000`, `1_`, `0x_FF` | `_` goes only between digits. The fix removes the stray `_`. |
| `0755`, `007`, `00` | A leading zero. When every digit is 0 to 7, the fixes write `0o755` or `755`. Otherwise the fix drops the zeros. Digits after the `.` and in an exponent may start with zeros. |
| `1.` *Later* | The fix writes `1.0`. This applies when nothing that could follow a `.` comes after it. |
| `.5` *Later* | The fix writes `0.5`. This applies when the `.` follows a token that cannot end an expression. |
| `0x1p3`, `0x1.8` *Later* | Truss has no hexadecimal floats. Write a decimal float. |
| `1'000` *Later* | The fix writes `1_000`. |

Rows marked *Later* are extra help for habits from other languages, added once
the compiler works (see [Diagnostics](#diagnostics)). Until then those inputs
get the plain error that the grammar implies.

When a number has an error, the token keeps the value of its valid prefix, or
0, so parsing can go on.

## Strings

### Where a string starts

- A run of `"`: one quote starts an ordinary string, exactly two make the
  empty string `""`, and three or more open a raw string with that many
  quotes.
- A run of `$` must be followed by three or more quotes, which open a raw
  string with that many `$`s. Any other `$` outside a string is an error.
- An `Upper` name followed directly by `"` or `$` is the tag of a tagged
  string. A keyword is never a tag: `return"x"` is `return` followed by a
  string.
- `'a'` is a character literal from another language, and SYNTAX.md gives
  its fix, `Character"a"`. The lexer emits the tagged string, so parsing goes
  on.

*Later:* string prefixes from other languages. A `Lower` name followed
directly by `"` or `'` would be reported with a fix, and the string lexed as
if it had no prefix. Until then `f"..."` lexes as the name `f` followed by a
string, which the parser rejects.

| Written | From | Fix |
|---|---|---|
| `f"Hello {name}"` | Python | `"Hello ${name}"` |
| `r"\d+"`, `r#"\d+"#` | Python, Rust | `"""\d+"""` |
| `b'a'` | Rust, Python | `UInt8"a"` |
| `b"bytes"` | Rust, Python | No fix. The message points to `text.bytes()`. |
| `$"Hello {name}"`, `@"C:\logs"` | C# | `"Hello ${name}"`, `"""C:\logs"""` |
| `` `Hello ${name}` `` | JavaScript | `"Hello ${name}"`, or a raw string if it spans lines |
| `'abc'` | Python, JavaScript | `"abc"` |
| `'a` with no closing quote | Rust lifetimes | No fix. Truss has no lifetimes. |

### Ordinary strings

The scanner reads characters up to the closing `"`. A `\` starts an escape. A
`${` starts an interpolation, and any other `$` is text. A line break or the end of the file before the closing `"`
makes the string unterminated: the error's fix inserts `"` at the end of the
line, and the string ends there. Ordinary strings fit on one line, so this
recovery is almost always right.

The value is the text in UTF-8, with escapes applied. Any other `\` sequence
is an error. *Later:* escapes from other languages get exact fixes:

| Written | Fix |
|---|---|
| `\x41` | `\u{41}` |
| `\u00E9`, `\U0001F600` | `\u{00E9}`, `\u{1F600}` (leading zeros dropped to fit six digits) |
| `\'` | `'` |
| `\a`, `\b`, `\f`, `\v`, `\e` | `\u{7}`, `\u{8}`, `\u{C}`, `\u{B}`, `\u{1B}` |
| `\(name)` | Swift interpolation: `${name}` |
| `\` at the end of a line | No fix. The message suggests a raw string. |
| `\u{D800}`, `\u{110000}`, `\u{}`, `\u{1234567}` | Not a Unicode scalar value, so no fix. |

### Raw strings

For a raw string opened with *q* quotes and *n* dollar signs:

1. **One line or several.** If only spaces and tabs come between the opening
   delimiter and the end of its line, the string spans several lines, and that
   whitespace is ignored (`truss fmt` removes it). Otherwise it is a one-line
   string, and its text starts right after the delimiter.
2. **The body.** In each line, a run of exactly *q* quotes closes the string.
   A run of more than *q* quotes is an error: at the start of a line, after
   whitespace, it still closes the string, and after text it stays text. A
   shorter run is text. A run of
   *k* `$`s followed by `{` starts an interpolation when *k* is at least
   *m* = max(*n*, 1). Then the first *k* − *m* `$`s are text. Everything else
   is text.
3. **A one-line string** must close on its line. A one-line string cannot
   start with `"`, because the opening run takes in every quote, and it cannot
   end with `"`, because the closing run would be too long. GRAMMAR.md states
   both rules, and they follow from the rule for runs.
4. **A multi-line string** must close on a line that holds only whitespace
   before the closing delimiter. That whitespace is the indentation. A closing
   delimiter after other text on its line is an error, and the fix moves it to
   a line of its own.
5. **Removing the indentation.** Once the closing line is found, each body
   line is checked:
   - A line that starts with the indentation has it removed.
   - A line that holds only whitespace and does not start with the indentation
     becomes an empty line, since nothing visible can be lost.
   - Any other line is an error. The error points at the first character that
     differs from the indentation and shows tabs and spaces visibly. The fix
     replaces the line's leading whitespace with the indentation, since the
     usual cause is a tab among spaces or the reverse.
   - The check looks at the text before any interpolation on the line, so an
     interpolation cannot start inside the indentation.
   - The line breaks just after the opening delimiter and just before the
     closing line are not part of the value. Every other line break is a line
     feed.
6. **An unterminated string** runs to the end of the file, with one error at
   its opening delimiter and no fix, as in Rust, Python, and Go. The scanner
   does not guess where the string was meant to end and lex the rest as code:
   errors in the code after it are reported once the string is closed. Like
   Rust, which points at a likely terminator, the error has a note at the
   line where the string seems to end: the first non-blank line indented less
   than the line holding the opening delimiter, or the first line where a
   definition starts in column 0.

The span of a text piece covers its source, including indentation that the
value leaves out.

### Interpolation

- At the start of an interpolation, the scanner reads tokens recursively until
  the `}` that matches it, counting `{` and `}`. Strings inside are scanned
  recursively too, so a `}` in a nested string does not count.
- A line break inside an interpolation is an error. The message suggests moving
  the expression into a `let`. The interpolation and its string end there.
- An empty interpolation, `${}` or `${ }`, is an error.
- Interpolations may nest at most 32 deep. This keeps hostile input from
  driving the recursion arbitrarily deep, and no real code comes near it.
- The tokens inside are laid out on their own. With no line breaks, they never
  contain a `NEWLINE`, but their brackets are still matched.

### Tagged strings

`Regex"..."`, `SqlQuery"""..."""`, and `Shell$$"""..."""` are strings with
`tag` set. `Character"a"` and `UInt8"\n"` are ordinary tagged strings to the
lexer. The type checker checks that each holds exactly one character.

## Punctuation

The scanner takes the longest match from GRAMMAR.md's list of punctuation, with
a small decision on the first one or two bytes. There are no generic
longest-match tables.

### Rejected sequences

The first version handles the sequences SYNTAX.md lists: comments, `;`,
`===`, `!==`, `'`, `` ` ``, `@`, `++`, and `--`. Rows marked *Later* are extra
help for other habits. None of them changes what the language accepts, since
each sequence is already an error. Habits fall into two groups:

- **Local fixes.** The fix depends only on the sequence itself. The lexer
  reports it, and applies the fix to its own output, so parsing goes on as if
  the code had been fixed.
- **Fixes that need context.** The lexer emits a `Foreign` token, which no
  grammar rule accepts. The parser reports it, because the fix depends on the
  expression around it: `i++` becomes `i += 1`.

| Written | Group | What the lexer emits | Fix |
|---|---|---|---|
| `// ...`, `/// ...`, `# ...` | local | Nothing, up to the end of the line | Remove the comment |
| `/* ... */`, nested | local | Nothing. If the comment spans lines, the next token counts as starting a new line. | Remove the comment. An unterminated one runs to the end of the file and has no fix. |
| `#[derive(...)]`, `#![...]` *Later* | local | Nothing, up to the end of the line | "Truss has no attributes", pointing to `derives` |
| `;` | local | At the end of a line, nothing. Mid-line, the next token counts as starting a new line. | Remove the `;`, or replace it with a line break |
| `===`, `!==` | local | `==`, `!=` | `==`, `!=`. A longer run, such as `====`, is not this habit, and lexes as `==`s. |
| `<>` *Later* | local | `!=` | `!=` |
| `...` *Later* | local | `..=` between two operands, otherwise `todo` | `..=`, or `todo` for a placeholder body |
| `..<` *Later* | local | `..` | `..` |
| `@`, `` ` `` | local | Nothing | "Not used in Truss" |
| Look-alike punctuation *Later* | local | The ASCII token | The ASCII character |
| `++`, `--` | context | `Foreign` | `i += 1`, `i -= 1`, `-(-x)` |
| `**` *Later* | context | `Foreign` | No fix. Truss has no power operator. |
| `:=` *Later* | context | `Foreign` | `let name = value` |
| `\|>` *Later* | context | `Foreign` | Write the call: `function(value)` |

- **Comments.** The fix deletes from the start of the comment, together with
  the whitespace before it, to the end of the line. A line left empty is
  deleted entirely. The message says where the comment's content belongs: in a
  name, a contract, or a test.
- **Removing trivia.** Comments, `;`, and forbidden characters in code all
  lex as whitespace, and their fixes are built by one function. It removes the
  text and the whitespace around it, or the whole line if nothing else is on
  it. Between two tokens it leaves a space, or a line break with the line's
  indentation where the removed text acted as one, so that the tokens stay
  apart: removing a character from `""`, a character, and `"` must not make
  `"""`.
- **`'`.** A character literal from another language, `'a'` or `'\n'`,
  becomes the tagged string `Character"a"`, with a fix. Any other `'` is an
  error without a fix, and is skipped.
- **Look-alike punctuation** (*Later*) is a small, hand-picked table: curly quotes
  `“ ” ‘ ’` become `"` and `'`; fullwidth `（ ） ［ ］ ｛ ｝ ， ： ； ＝` become
  their ASCII forms; no-break and other Unicode spaces become a space; `–` and
  `—` become `-`; `≤ ≥ ≠ → ⇒` become `<= >= != -> =>`; and `∀ ∃` become
  `forall` and `exists`. These come from pasted documents, input methods, and
  habits from Lean and Agda. A curly-quoted `“text”` lexes as a string.
- **`...` in documentation.** `...` lexes as `..` and `.`, which the parser
  rejects, so the examples in the documents write `todo` for code that is
  left out, as SYNTAX.md recommends for unwritten bodies.
- **Parser-level habits.** Some foreign habits, such as `|x| x + 1`, `&x`,
  `x ? a : b`, `Shape::Circle`, and `a ?? b`, are made of valid tokens. The
  parser reports them, not the lexer.

## Layout

### NEWLINE tokens

GRAMMAR.md's rule, which is Scala's: inside `(` or `[`, line breaks are
ignored. Elsewhere, a line break becomes a `NEWLINE` when the token before it
can end a statement and the token after it can begin one. Several line breaks
give at most one `NEWLINE`.

```text
stack = []
for each raw token t:
  if t.line_break_before
     and top(stack) is neither "(" nor "["
     and previous token can end a statement
     and t can begin a statement:
    emit NEWLINE
  update the bracket stack for t (see below)
  emit t
at the end: if the last token can end a statement, emit NEWLINE; then END_OF_FILE
```

- The `NEWLINE`'s span is the first line break after the token before it,
  which is where a fix such as "move `-` to the end of the line before" edits.
- The two sets are functions over token kinds in `Layout`. A test checks them
  against GRAMMAR.md.
- A closing `}` cannot begin a statement, so no `NEWLINE` comes before one.
  The parser still skips a `NEWLINE` before a `{` that must open a body.
- Each interpolation's tokens are a separate array with their own stack. An
  interpolation cut off by an error the scanner already reported, such as a
  line break, closes its open brackets without another error.
- GRAMMAR.md leaves out the foreign tokens `++` and `--`, which no rule
  accepts. Layout treats them as able both to end and to begin a statement,
  so that `i++` stays on a line of its own for the parser to report.

### Brackets

The layout pass matches `(`, `[`, and `{`, and always gives the parser balanced
brackets:

- **A closer that matches the top of the stack** pops it.
- **A closer that matches an opener deeper in the stack** means the openers
  above it were never closed. Each unclosed opener gets an error, with a note
  at the closer. Zero-width closers are inserted for them at the closer's
  position, and then the matching opener is popped.
- **A closer that matches nothing** is an error, and is dropped.
- **Openers still open at the end of the file** make the lexer run again. In
  that run, a
  definition keyword in column 0 (`fn`, `type`, `trait`, `impl`,
  `capability`, `let`, `test`, `theorem`, `proof`, `use`, `public`,
  `internal`) closes every open bracket. `truss fmt` starts every definition
  in column 0, so a missing `}` in one definition cannot swallow the
  definitions after it. The error points at the innermost unclosed opener,
  and its fix closes every open bracket. Only a broken file runs again, so
  valid code is never affected, however it is laid out.
- **A file that ends inside an unterminated comment or raw string** has its
  open brackets closed without another error. They are part of what the
  comment or string swallowed, and closing it is the fix that matters. An
  interpolation cut off by an error closes its brackets the same way.

Inserted closers are zero-width, so the parser can tell them apart and avoid
reporting the same mistake again.

**Where a fix puts a missing closer.** The token stream shows where a bracket
was found unclosed, which is often far from where it was meant to close, as
in `let x = [1, 2` followed by `g(x)`. As rustc does, the indentation decides
instead. Among the elements directly inside the bracket, where an element is
a token or a whole nested group, the closer goes after the last one on a line
indented more than the opener's line, or else after the last one on the
opener's line. So `[1, 2` becomes `[1, 2]`, a closer never lands inside a
nested group or inside a comment that ends the line, and a `}` goes on a line
of its own at the opener's indentation. When the bracket's last element is a
string cut off at the end of its line, the string probably swallowed the
closer, and the bracket gets no fix: closing the string is the fix that
matters.

## Diagnostics

```ocaml
type edit = { span : span; replacement : string }
type fix = { title : string; edits : edit list }

type t = {
  code : Code.t;                  (* Lexer of lexer, and a group for each later stage;
                                     Code.name gives "lexer.unterminated_string" *)
  message : string;
  span : span;
  notes : (span * string) list;
  fixes : fix list;               (* alternatives; most have one *)
}
```

- Every diagnostic is an error. Truss has no warnings.
- The first version gives exact fixes for the habits SYNTAX.md lists, and a
  plain error for any other invalid input. The fixes marked *Later* in this
  document are added once the compiler works.
- Codes are stable, descriptive names, so tools and agents match on codes, not
  on message text.
- A diagnostic may offer alternative fixes, as `0755` does.
- Applying any fix must remove its diagnostic without adding another from the
  lexer. Each fix has a focused test, and the fuzzer checks this for a
  mistake inserted into each document example. Fixes are not checked while
  lexing: that could only show that a fix lexes cleanly, not that it is
  what the author meant, and it made every change to the lexer keep a subtle
  argument true. A fix offered for an error that only arises where two
  recoveries meet may leave an error behind; lexing again shows it.
- An error with no exact fix gets none, even where a guess would usually be
  right: an agent applies fixes without reading them, so a wrong fix is
  worse than none. A closer that matches nothing has no fix, since an extra
  `}` is as often a missing `{`.
- A file lists at most 200 diagnostics, then gives a count of the rest, so a
  binary file opened by mistake gives a short report. The lexer keeps every
  diagnostic, and `Diagnostic.shown` applies the limit when they are
  listed.
- Messages never copy bytes that are not valid UTF-8; they describe them,
  as in "the byte 0xFF", and JSON output is always valid UTF-8.

## Unicode data

- **One Unicode version, named by the language version.** All tables come
  from that version's data files. Stage0 starts from Unicode 18.0.0, the
  latest when the tables were first generated.
- **A generator in `stage0/tools/unicode/`** downloads the UCD data files of
  that version, checks each against a SHA-256 hash recorded in
  `sources.txt`, and writes `stage0/unicode/unicode_tables.ml`.
  `regenerate.sh` runs the whole process. Only the generated module, the list of source
  URLs, and their hashes are checked in, which keeps the repository small and
  the output reproducible. Building the compiler never downloads anything;
  only regenerating the tables does.
- **Tables** are sorted arrays of code point ranges, searched by binary search,
  with a 128-entry table for ASCII.
- **Properties used:** `XID_Start` and `XID_Continue`, to find words, and
  `Default_Ignorable_Code_Point` (`DerivedCoreProperties.txt`);
  `Bidi_Control` and `Variation_Selector` (`PropList.txt`); and the general
  category `Cc` (`DerivedGeneralCategory.txt`). The forbidden characters are
  combined into one table when the tables are generated.
- **Names of characters** in messages come from `UnicodeData.txt`, or from
  `NameAliases.txt` for control characters, which `UnicodeData.txt` calls
  `<control>`. Only the forbidden characters' names are kept.
- **Conformance.** After writing the tables, `regenerate.sh` checks each
  property against the data file it came from, for every code point. The
  data files are not checked in, so this runs only when the tables change.
- The only library the lexer needs is Zarith.

## Interfaces to other stages

- **The parser** gets one token array per file. Brackets are balanced, there
  are nested arrays for interpolations, and `NEWLINE` tokens follow the
  line-break rule. It reports `Reserved` and `Foreign` tokens, whose fixes need
  context. It never reads the source bytes, except through spans to build
  fixes.
- **The Menhir reference grammar** gets the same tokens through a small
  conversion. Each string becomes a single `STRING` or `TAGGED`, so Menhir
  does not check interpolations, which are ordinary expressions anyway.
- **`truss fmt`** prints literals from their spans, and reads
  `blank_line_before`.
- **Hashing** uses literal values, never spellings or positions.
- **Incremental work.** The lexer works on whole files, and the background
  process lexes again only the files that changed. Lexing is linear in the
  file's size and takes far less time than any later stage, so lexing a file
  does not threaten the O(change) goal. Lexing one definition at a time could
  be added later if it were ever needed. Outside strings and brackets, the
  lexer's state at a definition keyword in column 0 is empty, so tokens before
  and after an edit could be reused.

## Testing

The tests follow IMPLEMENTATION.md's rules for testing: each states one
fact about a small input.

- **Focused tests** in `stage0/test/lexer_tests.ml`, grouped by section of
  this document. A test gives an input and asserts its tokens, shown
  compactly, or its one diagnostic: the code, where it starts, and the exact
  text each fix produces, which must lex cleanly.
- **The documents agree with the code.** Tests read the keyword lists, the
  punctuation list, and the line-break sets from GRAMMAR.md and compare them
  with `Token` and `Layout`.
- **The documents' examples lex cleanly.** Each ` ```truss ` block in a
  Markdown document at the root of the repository is a test of its own, so a
  new document is covered without being listed.
- **The fuzzer**, `stage0/tools/fuzz`, is run by hand. It checks that no
  input raises or gives spans out of bounds or out of order, that for one
  mistake inserted into a document example every fix removes its error and
  adds no other, and that valid tokens round-trip. Each problem it finds becomes a
  focused test.
- **The benchmark**, `stage0/tools/benchmark`, measures throughput on given
  files.
- **Unicode conformance** runs with `regenerate.sh` (see
  [Unicode data](#unicode-data)).
- **Both parsers.** Tokens from the corpus go to the Menhir reference as well as
  the hand-written parser, as IMPLEMENTATION.md plans.

## Left out on purpose

The lexer does not do these, because no other language does and each has a
cost:

- **More rules for invisible characters in strings,** such as limiting where
  joiners and variation selectors go, forbidding U+2028 and U+2029, or
  requiring strings in NFC.
- **Rejecting `"$name"`.** A `$` interpolates only before `{`, so `$name` is
  text, as in JavaScript.
- **Contextual keywords for `test`, `proof`, `law`, `theorem`, and
  `capability`.** They stay reserved, so that the line-break rule can be
  decided from the tokens alone.
