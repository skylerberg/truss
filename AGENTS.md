# Instructions for agents

## Writing

These rules apply to everything written in this repository: identifiers,
code comments, error messages, documents, commit messages, and pull request
descriptions.

The reader is a compiler engineer, human or agent. Write what you would say
to one aloud. Clear writing here means precise terms and direct sentences.
It does not mean everyday vocabulary.

1. **Use the standard term.** If compilers, type systems, or programming
   languages have a name for a thing, use the name. Do not describe the
   thing instead. A reader can look up a term. A description has to be
   decoded every time it appears.

   | Do not write | Write |
   |---|---|
   | what a match matches | the scrutinee |
   | what a call calls | the callee |
   | the function the lambda is written in | the enclosing function |
   | the view leaves the function | the view escapes |
   | what ends with the function | a value whose lifetime ends at return |
   | the two may be the same elements | the two may alias |
   | show them apart | prove them disjoint |
   | two tasks wait for each other's turn | deadlock |
   | given a value again | reinitialized |
   | worked out from | derived from, inferred from |
   | whatever its type parameters stand for | for every instantiation |
   | code that does not run | unreachable code |

2. **Keep Truss's own terms.** `view`, `own`, `mut`, `lends`, `yields`,
   `uses`, `provide`, capability, and cursor mean what DESIGN.md and
   SYNTAX.md define. Do not coin more terms. If a new concept needs a name,
   define the name once, where the concept is introduced.

3. **Name the failure that a rule prevents.** Write "this prevents a use
   after free", "a data race", "a deadlock", or "a dangling view". Do not
   only restate the rule in the checker's terms.

4. **State the change with its verb.** A commit title and the first
   sentence of a pull request start with Fix, Add, Remove, Rename, Reject,
   Allow, Move, or Split, followed by the thing changed under its real name.
   - Write "Reject match guards that mutate the scrutinee", not "Lend what
     a match matches while a guard is evaluated".
   - Write "Renamed `a` to `b`", not "`a` is `b`".

5. **Put one idea in a sentence, subject first.** If a sentence has two
   "what …" or "that …" clauses, find the term that replaces one of them.
   Give every pronoun an antecedent in the same sentence or the one before.

6. **Use a table for a mapping.** Renames, before-and-after behavior, and
   comparisons of options are tables. A heading is a label, such as
   "Renamed diagnostic codes", not a sentence.

7. **Name an identifier after what it is.** Prefer the standard noun:
   `scrutinee`, `callee`, `enclosing_loops`, `scope_end`, `may_alias`.
   A diagnostic code names the error: `ownership.data_race`, not
   `ownership.parallel_conflict`. A boolean reads as a predicate:
   `is_zero_size`, `has_break`, `may_fork`, not `zero_size` or `at_once`.

   Do not use a placeholder name. A placeholder says that a value was
   produced, not what the value is, so it fits every binding and spreads
   from one function to the next. These are placeholders:

   | Placeholder | Name the value instead |
   |---|---|
   | `found` | `place`, `matches`, `index`, `has_break` |
   | `made` | `fresh`, `outlined`, `call` |
   | `taken` | `arguments`, `arity`, `consumed` |
   | `kept` | `retained`, `prefix_length` |
   | `given` | `supplied_options`, `call_facts` |
   | `within` | `with_scope`, `is_inside`, `in_range`, `parent` |
   | `around`, `turns`, `go`, `aux` | the noun or verb for what it is, such as `scope_depth` or `scan` |

   A word on this list is fine as part of a longer name that says what the
   value is, such as `found_type` against `expected_type`.

8. **Do not copy the style of existing text.** Much of this repository
   describes around standard terms in everyday words. Fix that text; do not
   match it. When you edit a file, fix the vague names and roundabout
   sentences in the part you touch.

Before you commit, reread what you wrote against rules 1 to 7.

## OCaml

Give every module an `.mli` that exports only what other modules use. The
compiler reports an unused value, type, constructor, or field only when the
interface hides it, so a module without an interface hides dead code. The
entry module of an executable needs none: dune gives it an empty one.

## Testing

CI is the full gate. It runs every test suite and every proof of the
standard library on the pull request merged with `main`. Do not repeat it
on the development machine, which every session shares.

Before you push, run only:

1. `dune build`, and `dune build @fmt` if OCaml changed.
2. The test suites of the libraries that the change edits: for a change in
   `stage0/parser/parser`, the parser's suites. Run a suite as its executable,
   such as `stage0/test/parser_tests.exe`.
3. For a change under `standard/`, the check and the proofs of the modules
   that the change edits, and their tests.

Then push. If CI reports a failure, fix it and push again.

- Do not run `dune build @runtest`, `dune test`, or the proofs of the whole
  standard library.
- A change that only alters what compiles, such as a moved module or an
  edited `dune` file, needs the build and nothing else.
- A change to documents alone needs no local check.
- CI runs on Linux only. Run a changed sequence of system calls in a loop
  on the development machine as well.
