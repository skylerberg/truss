# Truss Lexer

This document designs the stage0 lexer. It implements the lexical grammar in
[GRAMMAR.md](GRAMMAR.md), and the rules in [SYNTAX.md](SYNTAX.md) and
[DESIGN.md](DESIGN.md) behind it. Where this design departs from those
documents, it says so. The changes this design made to those documents are
listed at the end. Nothing is built yet.

## What the lexer does

The lexer takes the bytes of one source file and returns an array of tokens and
a list of diagnostics. It always returns tokens, even for a broken file, so
that later stages can report more than the first error.

The lexer:

- checks the source text: UTF-8, the byte order mark, line breaks, and
  forbidden characters
- splits it into tokens: names, keywords, numbers, strings with their
  interpolations already lexed, and punctuation
- checks each name on its own: case rules, normalization, allowed characters,
  and scripts
- decides which line breaks are `NEWLINE` tokens, and matches brackets
- recognizes habits from other languages and reports each with an exact fix

It does not:

- know the grammar, beyond brackets and strings
- check names against each other. Confusable names are found by a later stage
  that sees every name visible in a package.
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

Each module is its own dune library, so the parser depends only on `Token` and
`Lexer`, and the formatter and language server can reuse `Source` and
`Diagnostic`.

### Hand-written, not generated

IMPLEMENTATION.md suggested sedlex. A hand-written scanner fits better:

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
type span = { start : int; stop : int }

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
  | Float of { significand : Z.t; exponent : Z.t }   (* significand × 10^exponent, exactly *)
  | String of string_literal
  | Punctuation of punctuation
  | Foreign of foreign                (* ++, --, and others the parser reports *)
  | Newline
  | End_of_file

and string_literal = {
  tag : (string * span) option;
  form : form;
  texts : text array;                 (* always one more than interpolations *)
  interpolations : interpolation array;
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
- **A string's texts and interpolations alternate.** `texts` always has one
  more entry than `interpolations`, which is the shape of a `Template`:
  `"a${x}b"` has the texts `"a"` and `"b"`, and `"${x}"` has two empty texts.
  This holds for untagged strings too.
- **An interpolation is a nested token array,** already laid out. The parser
  parses each one as an expression from its own array. This matches
  GRAMMAR.md's single `STRING` token, keeps the outer token stream flat, and
  confines an error inside an interpolation to that interpolation.
- **A tag is only the name.** In `database::SqlQuery"..."`, `database` and
  `::` are ordinary tokens before the string, and the parser joins them.
- **`line_break_before` drives the layout pass.** `blank_line_before` lets
  `truss fmt` keep a blank line between statements, if the formatter is
  meant to keep them. Hashes ignore both.
- **`keyword`, `reserved`, `punctuation`, and `foreign` have one constructor
  per item,** each built from a single list in `Token`. A test reads the
  keyword and punctuation blocks in GRAMMAR.md and checks them against these
  lists, so the documents and the code cannot drift apart.

## Names and keywords

### Scanning

- A name starts with an `XID_Start` character and continues with
  `XID_Continue` characters. `_` is `XID_Continue` but not `XID_Start`.
- `_` on its own is `Underscore`. `_` followed by name characters is an
  error, since names cannot start with `_`. The fix removes the leading
  underscores.
- A name made only of ASCII is looked up in the keyword table. Keywords are
  ASCII, so other names skip the lookup.
- A reserved word becomes a `Reserved` token, and the **parser** reports it.
  A good fix depends on the construct around it: `x as Int64` becomes
  `Int64.from(x)`, and `loop {` becomes `while true {`.

### Classification and checks

A name that is not a keyword is an `Upper` name if its first character has the
general category `Lu` or `Lt`, and a `Lower` name otherwise. It is then
checked:

1. **Case rules.** An `Upper` name contains no `_`. A `Lower` name contains no
   `Lu` or `Lt` character, does not start or end with `_`, and has no `__`.
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
2. **Normalization Form C.** If every character has `NFC_Quick_Check=Yes`, the
   name is already in NFC. Otherwise the scanner normalizes it and compares.
   The fix replaces the name with its NFC form.
3. **Allowed characters.** Every character must have
   `Identifier_Status=Allowed` under
   [UTS #39](https://www.unicode.org/reports/tr39/). ZWJ and ZWNJ are not
   `XID_Continue`, so a name stops before one, and the error says that joiners
   are not supported in names yet.
4. **Scripts.** The name must meet UTS #39's Moderately Restrictive level,
   worked out from `Script_Extensions` as section 5.2 describes. The message
   names the scripts it found.

A name that is all ASCII needs only the case rules, so the other checks cost
nothing in ordinary code. Each check depends only on the name, which is why it
belongs in the lexer and not in a later stage. The `Unicode` module also
provides UTS #39's `skeleton` function, for the later check of names across a
package. That check compares only pairs in which at least one name contains a
character outside ASCII, so a package of ASCII names never runs it.

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
   A run of more than *q* quotes is an error. A shorter run is text. A run of
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
     differs from the indentation and shows tabs and spaces visibly. There is
     no automatic fix, since the intended indentation is not clear.
   - The check looks at the text before any interpolation on the line, so an
     interpolation cannot start inside the indentation.
   - The line breaks just after the opening delimiter and just before the
     closing line are not part of the value. Every other line break is a line
     feed.
6. **An unterminated string** swallows the rest of the file unless the
   scanner guesses where it ends. It ends the string before the first
   non-blank line that is indented less than the line holding the opening
   delimiter, or before the first line that starts with a definition keyword
   in column 0. The error offers a fix that inserts the closing delimiter
   there.

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
| `/* ... */`, nested | local | Nothing. If the comment spans lines, the next token counts as starting a new line. | Remove the comment |
| `#[derive(...)]`, `#![...]` *Later* | local | Nothing, up to the end of the line | "Truss has no attributes", pointing to `derives` |
| `;` | local | At the end of a line, nothing. Mid-line, the next token counts as starting a new line. | Remove the `;`, or replace it with a line break |
| `===`, `!==` | local | `==`, `!=` | `==`, `!=` |
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
- **Look-alike punctuation** (*Later*) is a small, hand-picked table: curly quotes
  `“ ” ‘ ’` become `"` and `'`; fullwidth `（ ） ［ ］ ｛ ｝ ， ： ； ＝` become
  their ASCII forms; no-break and other Unicode spaces become a space; `–` and
  `—` become `-`; `≤ ≥ ≠ → ⇒` become `<= >= != -> =>`; and `∀ ∃` become
  `forall` and `exists`. These come from pasted documents, input methods, and
  habits from Lean and Agda. A curly-quoted `“text”` lexes as a string.
- **`...` in documentation.** The examples in SYNTAX.md and DESIGN.md use
  `{ ... }` as a placeholder. It lexes as `..` and `.`, which the parser
  rejects, so the examples should use `{ todo }`, as SYNTAX.md already
  recommends for unwritten bodies, before they become a parser test corpus.
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
- Each interpolation's tokens are a separate array with their own stack.

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
  definitions after it. The error points at the innermost unclosed opener, and
  its fix inserts the closer before that line. Only a broken file runs again,
  so valid code is never affected, however it is laid out.

Inserted closers are zero-width, so the parser can tell them apart and avoid
reporting the same mistake again.

## Diagnostics

```ocaml
type edit = { span : span; replacement : string }
type fix = { title : string; edits : edit list }

type t = {
  code : string;                  (* stable, such as "lexer.unterminated_string" *)
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
  lexer. A test applies every fix across the test corpus and lexes the result
  again.
- A file lists at most 200 diagnostics, then gives a count of the rest, so a
  binary file opened by mistake gives a short report.

## Unicode data

- **One Unicode version, named by the language version.** All tables come
  from that version's data files. Stage0 starts from the latest Unicode
  version at the time the tables are first generated.
- **A generator in `tools/`** downloads the UCD and UTS #39 data files of that
  version, checks each against a SHA-256 hash recorded in the repository, and
  writes `unicode_tables.ml`. Only the generated module, the list of source
  URLs, and their hashes are checked in, which keeps the repository small and
  the output reproducible. Building the compiler never downloads anything;
  only regenerating the tables does.
- **Tables** are sorted arrays of code point ranges, searched by binary search,
  with a 128-entry table for ASCII.
- **Properties used:** `XID_Start` and `XID_Continue`, `Default_Ignorable_Code_Point`
  (`DerivedCoreProperties.txt`); `Bidi_Control` and `Variation_Selector`
  (`PropList.txt`); the general categories `Lu`, `Lt`, and `Cc`
  (`DerivedGeneralCategory.txt`); `NFC_Quick_Check`
  (`DerivedNormalizationProps.txt`); `Script` and `Script_Extensions`;
  `Identifier_Status` (`IdentifierStatus.txt`) and `confusables.txt` from UTS
  #39.
- **NFC is implemented directly** from the decompositions, combining classes,
  and composition exclusions in `UnicodeData.txt` and
  `CompositionExclusions.txt`. It is a few hundred lines, and the UCD's own
  `NormalizationTest.txt` serves as its conformance test.
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

- **Golden tests.** Small `.truss` files, each with the expected tokens and
  diagnostics, compared using dune's `diff` actions. This needs no test
  library.
- **The documents as a corpus.** Every ` ```truss ` block in SYNTAX.md,
  DESIGN.md, and GRAMMAR.md must lex with no diagnostics. This keeps the
  examples honest, and is one more reason to replace the `...` placeholders
  with `todo`.
- **The documents agree with the code.** Tests read the keyword lists, the
  punctuation list, and the line-break sets from GRAMMAR.md and compare them
  with `Token` and `Layout`.
- **Fixes work.** Every fix in the corpus is applied, and the result is lexed
  again (see [Diagnostics](#diagnostics)).
- **Round trips.** Random sequences of valid tokens, printed with spaces in
  between, lex back to the same tokens.
- **Robustness.** Random bytes, and corpus files with random mutations, never
  raise an exception, always finish, and always produce spans that are in
  bounds and in order. A fuzzer such as AFL can drive this later.
- **Unicode conformance.** `NormalizationTest.txt` for NFC, and spot checks of
  each generated table against the data file it came from.
- **Both parsers.** Tokens from the corpus go to the Menhir reference as well as
  the hand-written parser, as IMPLEMENTATION.md plans.

## Language changes made for the lexer

Designing the lexer led to these changes in SYNTAX.md, GRAMMAR.md, and
DESIGN.md. The test for each was that another language already does it, or
that it costs almost nothing; Truss does not lead the way on rules like these.

- **The cost words are names to the lexer** (P1), as contextual keywords are in
  C#, Kotlin, Swift, and Rust. This also fixed two bugs: the documents listed
  the words differently, and `cost time finite` at the end of a line could
  never end it.
- **Each language version pins a Unicode version** (P2), as Java does.
- **Decimal literals have no leading zeros** (P3), as in Python 3 and
  JavaScript's strict mode.
- **Names use only UTS #39's allowed characters, and two ASCII names are never
  compared for confusability** (P4), as in Rust.
- **The line-break rule is Scala's** (P7): a `NEWLINE` comes exactly where the
  token before can end a statement and the token after can begin one.
- **Raw-string whitespace is fully specified:** spaces after an opening `"""`
  are ignored, and any whitespace-only line that does not start with the
  indentation is empty.

Considered and left out, because no other language does them and each has a
cost: checking names for mixed numbering systems and for look-alikes of
keywords; allowing ZWJ and ZWNJ in names, which was deferred; limiting where
joiners and variation selectors may appear in strings, forbidding U+2028 and
U+2029, and requiring string literals in NFC (P5); rejecting `"$name"` (P6);
and making `test`, `proof`, `law`, `theorem`, and `capability` contextual
keywords (P8).
