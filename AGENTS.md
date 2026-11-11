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
   Avoid names that make sense only after reading the body: `around`,
   `taken`, `within`, `found`, `made`, `turns`. A diagnostic code names the
   error: `ownership.data_race`, not `ownership.parallel_conflict`.

8. **Do not copy the style of existing text.** Much of this repository
   describes around standard terms in everyday words. Fix that text; do not
   match it. When you edit a file, fix the vague names and roundabout
   sentences in the part you touch.

Before you commit, reread what you wrote against rules 1 to 7.
