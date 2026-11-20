# Experiments

This directory is an experiment: it evaluates Truss by reimplementing parts
of the compiler in Truss and comparing the result with stage0. Nothing here
is part of the compiler, and nothing depends on it.

The first part reimplemented is the front end: stage0's lexer and parser,
with their diagnostics and fixes.

| Path | Contents |
|---|---|
| `frontend/` | A Truss package: the lexer, the parser with its precedence and context checks, and a printer of the syntax tree in the format of `stage0/test/syntax_print` |
| `compare/` | An OCaml executable that prints stage0's syntax tree, tokens, and timings in the same formats as `frontend` |
| `compare.sh` | Builds both and compares their output on every `.truss` file in the repository |
| `tools/benchmark.py` | The standard benchmark of the two implementations |
| `tools/` | Generators for the Unicode tables of `frontend` and for mutated copies of the corpus |

Both executables take the same commands:

| Command | Output |
|---|---|
| `print FILE...` | The syntax tree of each file, then its diagnostics with their notes and fixes |
| `tokens FILE...` | The tokens of each file, with their spans, then the lexer's diagnostics |
| `time ROUNDS FILE...` | For each file, the best time in nanoseconds of lexing it and of parsing its tokens over `ROUNDS` runs, then the sums |

`./compare.sh print` and `./compare.sh tokens` report whether the two
implementations agree on the whole corpus. To compare them on broken input,
`tools/mutate_corpus.py` writes mutated copies of the corpus and a list of
them to pass to both executables.

## Benchmark

`python3 -I experimental/tools/benchmark.py remote liquid` copies this
checkout to a directory on `liquid` that it deletes afterwards, builds and
measures there under `flock ~/benchmark/truss.lock`, and reports here. The
measuring takes about a minute:

| Measurement | What a change in it says |
|---|---|
| The corpus, five rounds of both programs, each file at its best of three, split into files under 2 KB and the rest | Throughput, and the overhead of each call to `lex` and `parse` |
| The worst-case inputs of `stage0/tools/benchmark`, at 20,000 repetitions, and 200,000 for the three about numbers | The error paths, and whether one of them became quadratic |
| The deepest chain of `else if` the port parses before its stack overflows | The size of the port's stack frames |
| The syntax trees and diagnostics of the corpus, compared | Whether the port still agrees with stage0 |

Each run is saved under `~/.cache/truss-frontend-benchmark/LABEL/`, and the
report compares it with the label's previous run, or with the result that
`--baseline` names. stage0 is timed in the same run as a control: unless a
change edits stage0's lexer or parser, its change says how much the machine
moved, and the ratio of the two cancels that drift. `local` measures this
machine instead, whose load varies too much for a small change to show.
