# Truss Lexer

This document describes the stage0 lexer, in [`stage0/`](stage0), which
implements the lexical grammar of [SPECIFICATION.md](SPECIFICATION.md). It
takes the bytes of one file and returns an array of tokens and a list of
diagnostics. It always returns tokens, even for a file with errors, so later
stages can report more than the first error.

**The lexer is a pure function of one file's text.** It gets no feedback from
the parser and has no modes beyond brackets and strings. So the line-break
rule depends on tokens alone, a file's tokens can be cached by its text, and
the lexer can be ported directly when the compiler is rewritten in Truss. For
the same reason it has no contextual keywords: the words of `cost` clauses
are names to it.

The lexer does not know the grammar beyond brackets and strings, does not
decide `name[...]`, and does not round float literals: the type checker
rounds once, to the type it infers.

## Structure

```text
bytes ──▶ Scanner ──one raw token at a time──▶ Layout ──▶ token array
             │                                    │
             └────────────▶ diagnostics ◀─────────┘
```

- **The scanner** turns bytes into raw tokens, each marked with whether a line
  break came before it. Its loop decides once at each position whether it
  holds trivia or the start of a token. A construct that must end on its
  line, such as an ordinary string or an interpolation, returns `Closed` or
  `Unterminated`; an unterminated one makes every enclosing such construct
  unterminated too, with no further error.
- **Layout** inserts `NEWLINE` tokens and matches brackets. It pulls one raw
  token at a time, and its state is the previous token and the bracket
  stack, so the bytes are read once and no array of raw tokens is built.
- **The output is one array of final tokens,** not a stream, because the
  parser's recovery looks ahead to the next definition, and `truss fmt` and
  the language server reuse the tokens.
- **Only a file with an unclosed bracket is lexed twice,** the second time
  with bracket recovery (see [Brackets](#brackets)).

The two stages are separate modules because the line-break rule is a small
function of two adjacent tokens and the stack, tested without the scanner.
The scanner lays out each interpolation's tokens with Layout as it reads
them.

### Hand-written, not generated

- **Much of the lexical grammar is not regular.** A raw string chooses its
  delimiter length, interpolations nest strings to any depth, and a raw
  string's indentation is known only at its closing delimiter. A generated
  matcher would need all of that written by hand around it.
- **The Unicode version must be the language's,** not the one a generator
  release was built with.
- **It can be ported to Truss** line by line, as an index moving over bytes.

## Tokens

- **A literal token holds its value,** and its spelling is the source under
  its span, which `truss fmt` prints unchanged.
- **Integers have any size.** Whether one fits its type is the type checker's
  decision.
- **Floats are exact decimals.** Rounding to `Float64` and then `Float32` can
  differ from rounding to `Float32` directly, so the type checker rounds once.
- **A string's texts and interpolations alternate,** starting and ending with
  a text, the shape of a `Template`. Each interpolation is a nested token
  array, already laid out, which the parser parses on its own, so an error
  inside an interpolation stays there.
- **A tag is only the name.** A module path before it is ordinary tokens.
- **`blank_line_before`** lets `truss fmt` keep blank lines, collapsing a run
  to one.
- **Each list of keywords, reserved words, punctuation, and foreign tokens is
  spelled once,** in `Token`, and a test checks them against
  SPECIFICATION.md.
- **Spans are byte offsets into the original file,** which is never
  rewritten, so a file with carriage returns reports the positions an editor
  shows. Lines and columns are computed only when a diagnostic is shown.
  Positions relative to a definition are the job of the stage that splits a
  file into definitions.

## Source text

- An ASCII byte is handled directly; a byte of 0x80 or above starts a UTF-8
  sequence, decoded strictly. Each maximal run of invalid bytes is one error.
- A lone carriage return is an error whose fix writes a line feed, and the
  scanner treats it as a line break so the lines after it lex normally.
- A run of forbidden characters is one error that names each by code point
  and name. In code its fix deletes them, and in an ordinary string it
  escapes them. The scanner then lexes as if they were absent.

## Names and numbers

- **The scanner reads a word as Unicode defines one,** so `café` is one name
  with one error, not `caf` and a stray character.
- **A name that breaks the case rules gets a fix that rewrites it,** and every
  use of the misspelled name gets the same fix, so applying a file's fixes
  renames it consistently.
- **A reserved word becomes a `Reserved` token,** which the parser reports,
  because its fix depends on the construct around it.
- **A number is the longest run of name characters that starts with a
  digit,** read whole and then validated, so `3u8`, `0xFG`, and `1_` are each
  one token with one precise error. A number with an error has the value of
  its valid prefix, so the parser can continue. A literal's value is computed
  in time linear in its length.

## Strings

- **Ordinary strings fit on one line,** so an unterminated one ends at the
  line break, with a fix that closes it there, which is almost always right.
- **An unterminated raw string runs to the end of the file,** with one error
  at its opening delimiter and no fix, and a note at the line where it seems
  to end. The scanner does not guess an end and lex the rest as code.
- **Indentation is checked once the closing line is found.** A line that does
  not start with the indentation is an error pointing at the first character
  that differs, with a fix that writes the indentation, since the usual cause
  is a tab among spaces.
- **Interpolations nest at most 32 deep,** which bounds the recursion on
  hostile input.
- **A quote that touches a name is not a delimiter,** so `it's` has an
  apostrophe.

## Habits of other languages

Sequences of other languages that are not Truss tokens fall in two groups:

- **Local fixes,** where the fix depends only on the sequence, such as a
  comment, `;`, or `===`. The lexer reports it and emits the tokens of the
  fixed code, so the parser sees no error.
- **Fixes that need context,** such as `i++`. The lexer emits a `Foreign`
  token, which no grammar rule accepts, and the parser reports it. Layout
  treats a `Foreign` token as able to end and begin a statement, so `i++` on
  its own line is a statement of its own.

Comments, `;`, and forbidden characters in code all lex as whitespace, and
their fixes are built by one function. It removes the text and the
whitespace around it, or the whole line, and leaves a space or a line break
between two tokens so they stay separate: removing a character from `""`, a
character, and `"` must not make `"""`.

Some habits, such as `|x| x + 1`, are made of valid tokens, and the parser
reports them.

## Layout

### NEWLINE tokens

- A `NEWLINE`'s span is the first line break after the token before it,
  where a fix such as "move `-` to the end of the line before" edits.
- The sets of tokens that can end and begin a statement are functions over
  token kinds in `Layout`, and a test checks them against SPECIFICATION.md.
- Each interpolation's tokens have their own bracket stack.

### Brackets

Layout's output always has balanced brackets:

- **A closer that matches an opener deeper in the stack** means the openers
  above it were never closed. Each gets an error, and zero-width closers are
  inserted at the closer's position. The parser can tell them apart, so it
  reports the mistake once.
- **A closer that matches no open bracket** is an error, and is dropped.
  Layout counts the open brackets of each kind, so it finds one without
  searching the stack.
- **Openers still open at the end of the file** make the lexer run again, and
  in that run a definition keyword in column 0 closes every open bracket.
  `truss fmt` starts every definition in column 0, so a missing `}` in one
  definition cannot swallow the definitions after it. Only a file with an
  unclosed bracket is lexed twice, so layout never affects valid code's
  tokens.
- **A file that ends inside an unterminated comment or raw string** has its
  brackets closed with no other error: their closers are probably inside it.

**A missing closer is placed by indentation,** as rustc does, since the token
stream shows where a bracket was found unclosed, often far from where it was
meant to close. Among the elements directly inside the bracket, the closer
goes after the last one on a line indented more than the opener's, or else
after the last one on the opener's line. It is never placed inside a nested
group or a comment, and a `}` gets a line of its own. A bracket whose last
element is an unterminated string gets no fix, since the string probably
holds the closer. Each closed opener records its closer's index, so placing
every missing closer takes linear time.

## Diagnostics

- **Every diagnostic is an error,** with a stable descriptive code that tools
  match on.
- **A fix removes its diagnostic without adding another from the lexer.** Each
  fix has a test, and the fuzzer checks it for a mistake inserted into each
  document example. Fixes are not checked while lexing, which could show only
  that a fix lexes, not that it matches the author's intent.
- **An error with no exact fix gets none,** because an agent applies fixes
  without reading them, so a wrong fix is worse than none. A closer that
  matches nothing has no fix, since an extra `}` is as often a missing `{`.
- **A file lists at most 200 diagnostics,** so a binary file opened by mistake
  gives a short report. `Diagnostic.shown` applies the limit.
- **Messages never copy invalid UTF-8;** they describe the bytes.

## Unicode data

- **A generator in `stage0/tools/unicode/`** downloads the Unicode Character
  Database of the language's version, checks each file against a hash in
  `sources.txt`, and writes `stage0/unicode/unicode_tables.ml`. Only the
  generated module and the hashes are checked in, and building never
  downloads anything.
- **Tables are sorted arrays of code point ranges,** searched by binary
  search, with a table for ASCII.
- **`regenerate.sh` checks every property against its data file,** for every
  code point, when the tables change.
- Character names are kept only for the forbidden characters, which messages
  name.

## Interfaces to other stages

- **The parser** gets one token array per file, with balanced brackets,
  nested arrays for interpolations, and the `NEWLINE`s of the line-break
  rule. It reads the source only through spans, to build fixes.
- **The Menhir reference grammar** gets the same tokens, with each string as
  one `STRING` or `TAGGED`.
- **The code database** lexes again only the files that changed. Lexing is
  linear in a file's size, so whole files do not threaten O(change).

## Deliberately excluded

- **More rules for invisible characters in strings,** such as limiting where
  joiners go or requiring NFC, which would need the data of every script.
- **Rejecting `"$name"`.** A `$` interpolates only before `{`.
- **Contextual keywords for `test`, `proof`, `law`, `theorem`, and
  `capability`,** so the line-break rule is decided from tokens alone.

## Not built

- **Rarer forms of strings from other languages,** such as C#'s `$@"..."`, a
  JavaScript template literal that spans lines, Python's `b"""..."""`, and
  the fullwidth semicolon. Each is already an error, with the error of the
  nearest form that is built.
- **Lexing one definition at a time.** Outside strings and brackets, the
  lexer's state at a definition keyword in column 0 is empty, so tokens
  before and after an edit could be reused. Nothing needs it yet.
