# Truss Lexer

The stage0 lexer implements the lexical grammar of
[SPECIFICATION.md](SPECIFICATION.md). It takes the bytes of one file and
returns an array of tokens and a list of diagnostics. It always returns
tokens, even for a file with errors, so later stages can report more than
the first error.

**The lexer is a pure function of one file's text.** It gets no feedback from
the parser, has no modes beyond brackets and strings, and has no contextual
keywords. So the line-break rule depends on tokens alone, and a file's tokens
can be cached by its text.

## Structure

```text
bytes ──▶ Scanner ──one raw token at a time──▶ Layout ──▶ token array
             │                                    │
             └────────────▶ diagnostics ◀─────────┘
```

- **The scanner** turns bytes into raw tokens, each marked with whether a
  line break came before it.
- **Layout** inserts `NEWLINE` tokens by the line-break rule and matches
  brackets. The rule is a function of two adjacent tokens and the bracket
  stack, so it is tested without the scanner.
- **The output is an array, not a stream,** because the parser's recovery
  looks ahead to the next definition.

**The lexer is written by hand.** Much of the lexical grammar is not regular:
a raw string chooses its delimiter length, interpolations nest strings to any
depth, and a raw string's indentation is known only at its closing delimiter.
The Unicode version must also be the language's, not a generator's.

**Literals are not rounded or range-checked here.** Integers have any size and
floats are exact decimals. Rounding to `Float64` and then to `Float32` can
differ from rounding to `Float32` directly, so the type checker rounds once,
to the type it infers.

## Habits of other languages

Sequences from other languages that are not Truss tokens fall in two groups:

- **Local fixes,** where the fix depends only on the sequence, such as a
  comment, `;`, or `===`. The lexer reports it and emits the tokens of the
  fixed code, so the parser sees no error.
- **Fixes that need context,** such as `i++`. The lexer emits a `Foreign`
  token, which no grammar rule accepts, and the parser reports it.

Some habits, such as `|x| x + 1`, are made of valid tokens, and the parser
reports them.

## Recovering from unclosed brackets

Layout's output always has balanced brackets, so the parser never sees an
unbalanced file.

- **A closer that matches an opener deeper in the stack** closes the openers
  above it, each with an error.
- **A closer that matches no opener** is an error, and is dropped.
- **Openers still open at the end of the file** make the lexer run again,
  and in that run a definition keyword in column 0 closes every open
  bracket. `truss fmt` starts every definition in column 0, so a missing `}`
  in one definition cannot swallow the definitions after it. Valid code is
  lexed once.
- **A missing closer is placed by indentation,** as rustc does, since the
  point where the stream shows a bracket unclosed is often far from where
  it was meant to close.

## Diagnostics

- **Every diagnostic is an error,** with a stable code that tools match on.
- **An error with no exact fix gets none.** An agent applies fixes without
  reading them, so a wrong fix is worse than none. A closer that matches
  nothing has no fix, since an extra `}` is as often a missing `{`.
- **Interpolations nest at most 32 deep,** which bounds the recursion on
  hostile input.

## Deliberately excluded

- **More rules for invisible characters in strings,** such as limiting where
  joiners go or requiring NFC, which would need the data of every script.
- **Rejecting `"$name"`.** A `$` interpolates only before `{`.
- **Contextual keywords for `test`, `proof`, `law`, `theorem`, and
  `capability`,** so the line-break rule is decided from tokens alone.

## Not built

- Rarer string forms from other languages, such as C#'s `$@"..."`; each is
  already an error.
- Lexing one definition at a time.
