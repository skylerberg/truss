# Central diagnostics

Every diagnostic the compiler reports is defined in one catalog. A pass
reports a typed value from the catalog and never builds diagnostic text.
One renderer resolves the value's nodes to spans, its quotes to source
text, and its fixes to text edits.

## Goals

1. Audit every diagnostic the compiler can report from one place.
2. Read every diagnostic without reading the compiler's source.
3. Make a pass that builds diagnostic text fail to compile, not merely
   stand out in review.

## The compiler today

The survey ran over `origin/main` after #1250.

| Measure | Count |
|---|---|
| Diagnostic codes | 254: lexer 37, parser 56, resolve 16, types 85, patterns 4, usage 6, ownership 16, capabilities 7, prover 18, package 9 |
| Sentence literals that diagnostics are built from | 766, of which 459 have `%` holes |
| Literals no code is written near | 158, mostly fragments joined into a message elsewhere |
| Fixes built after parsing | 50, and 6 lists of spelling fixes, in 24 files |
| Fixes built in the lexer and the parser | 39, in 14 files |
| Files that quote source text into a message | 19 |

Every message is a `string` that its call site builds. The wording of one
diagnostic is often spread over several functions: the prover joins
"` may not hold.`" to a quote and a context clause, and the capability
check builds sentences from `add_alternative` and `show_exceptions`. A
reader reconstructs a message by following the code that assembles it.

A diagnostic holds `Source.Definition_span.t` spans, so every pass
resolves its own origins to spans and reads text to quote it:

| Repeated mechanism | Copies |
|---|---|
| A `report` wrapper over `Diagnostic.make` | 8: `Resolve.Walk`, `Interface.Checking`, `Infer.State`, `Infer.Patterns`, `Infer.Capabilities`, `Ownership.Context`, `Usage`, `Package_checks` |
| Origin to span | `Interface.Elaborator.read_span`, `Resolve.Walk.read_span`, `Infer.State.read_span`, `Infer.Form.read_span`, `Infer.Patterns.read_span`, `Prover.resolve_location` |
| Quote source into a message | `Infer.State.quote_span`, `Infer.Form.quote`, `Facts.quote_home`, `Ownership.Context.show`, and the rest of the 19 files |
| Deferred quotes, resolved when the diagnostic is shown | The prover's `Obligation.piece` and `Prover.render` only |

Because a stored diagnostic holds spans, a reformat inside a definition
re-runs every unit that has a diagnostic there:
`Store.mark_position_holders_stale` selects them, so a reformat re-runs
type inference to move an error's span.

## The catalog

Each code becomes a constructor whose payload holds the facts the message
needs. A family is a module with its type and one function that describes
each value:

```ocaml
type t =
  | Unused_variable of { binding : node; constant : Path.t option }
  | Self_comparison of { comparison : node; operator : Language.Comparison.t; is_float : bool }
  | ...

val describe : t -> description
```

A `description` gives the code, the severity, the location, the message,
the notes, and the fixes. A message is a list of pieces: text written in
the catalog, a quote of a node, or a printed value such as a type or a
path. Every sentence of every diagnostic is written in a `describe`, and
nowhere else.

| Payload field | Rendered as |
|---|---|
| `node` | The node's span, as a location, or its source text, as a quote |
| `Path.t`, `Types.ty`, `Types.capability`, `Types.condition` | The printer of that type, called by the catalog |
| A name, such as a field or a label | The name, in backquotes |
| `code` | Truss code printed by a pass's printer, such as the prover's rendering of a proof goal |
| A count, a keyword, a mode | Written by the catalog |

`code` is the one field that holds text a pass produced. It is for printed
Truss code only, so a search for `code` fields lists everything left to
review.

The catalog has four libraries in one directory, `stage0/diagnostics`:

| Library | Families | Depends on |
|---|---|---|
| `description` | None: the generic description types and the renderer for file spans | `diagnostic`, `source` |
| `syntax_catalog` | `Lexing`, `Parsing` | `description`, `token`, `language` |
| `project_catalog` | The manifest, lock file, selection, and layout problems | `path`, `grant` |
| `catalog` | Every family after parsing | `description`, `types`, `core`, `path` |

The lexer and the manifest parser keep their light dependencies, and an
audit reads one directory.

## The renderer

The renderer is the only code that reads a definition's tree, spans, and
text for a diagnostic. It turns a description into the
`Diagnostic.in_definition` that the database stores today, and it owns
every layout decision: indentation, separators, and where a brace goes.

The database renders a unit's descriptions when the unit runs, with the
unit's name lookups, so it stores rendered diagnostics as before.
Storing descriptions, and rendering them when the database lists
diagnostics, is the step that lets a reformat change no stored fact; it
is not done.

A node is an origin in the definition being checked, the definition
itself, or an origin in another definition. The prover quotes a callee's
clause through the last, and the renderer reads that definition's text
for the quote. A location or an edit is always in the definition being
checked.

The lexer and the parser report before a tree exists. Their payloads hold
spans in place of nodes. The parser sees only tokens, so its payloads hold
code spelled from tokens, and `Description.render_spans` renders them
without source text.

## Fixes

A fix is a title, written in `describe`, and a list of edits on nodes.
Every fix built after parsing falls into these edits:

| Edit | Uses today | Reads text today |
|---|---|---|
| Replace a node with code | Write `UInt64`, `None`, `_`, a view type, `generic X`, a constant's path, the checked method; every spelling fix | No |
| Insert code before a node | `mut `, `own `, `indirect `, `let _ = `, a label | No |
| Insert code after a node | `.copy()`, `(..)`, `.method()`, ` when C` | No |
| Delete from one node boundary to another | A mode keyword, a label, a parameter default | One deletes `start + 4` bytes for `mut ` |
| Remove an entry of a list with its separator | A derived trait, a `RunForever`, a pattern alternative | Yes |
| Remove whole lines | An unused `use`, unreachable statements, an unreachable arm | Yes: line starts, indentation, a trailing newline |
| Add lines after a node, at its indentation | The missing arms of a `match` | Yes |
| Add a clause to a signature, or a capability to `uses` | The prover's `requires` and `uses Panic` | Yes |

Every edit that reads text today becomes a layout decision in the
renderer. The survey found no fix that needs an edit outside this table.
The lexer and the parser keep span edits, which they build from tokens.

## Enforcement

- A pass reports a catalog value. Only `Description.render_with` calls
  `Diagnostic.make` with a message; removing the parameter is not done.
- An edit names nodes, so a pass has no span to compute. The lexer and
  the parser build span edits from tokens, and a fix's title comes from
  the catalog through its `action`.
- A pass reads spans only for what is not a diagnostic: inference's
  capture and ordering checks, the prover's `todo` holes, and the
  elaborator's syntax errors. Removing `read_spans` from the passes'
  lookups is not done.

What remains for review is the `code` fields and the printers that fill
them.

## The catalog tool

`stage0/tools/diagnostic_catalog` renders every diagnostic as Markdown,
grouped by family. It is run by hand; its output is not checked in, and CI
does not run it.

```ocaml
val list_examples : Diagnostic.Code.usage -> t list
```

The usage, package, resolve, patterns, capabilities, and ownership
families give examples with an exhaustive match over their codes. The
types family is shared by `Typing` and `Inference`, so those two, the
prover, and the syntax families list one example for each constructor
and for each alternative of an enumerated field, and `list_examples`
selects a code's examples by their description. The tool walks
`Diagnostic.Code.all` and ends with the codes that have no example.

The tool renders a quoted node as a placeholder named by the field, such
as `‹binding›`: an example's node is `Build.example "binding"`.

## Conversion

One pull request converts everything, and the old mechanisms go in it:

1. Add the payload pieces, `description`, the node edits, and the
   renderer. Store descriptions in the database, and render them where
   diagnostics are listed.
2. Convert one family at a time: its codes become catalog constructors,
   and its call sites report them. Delete the pass's `report` wrapper,
   `read_span`, quoting, and edit helpers as its last call site goes.
3. Remove the message parameter of `Diagnostic.make`, and remove
   `read_text` and `read_spans` from the passes' lookups.
4. Add the catalog tool.

## Decisions

| Question | Decision |
|---|---|
| Do payloads hold `Types.ty` and `Path.t`, or text printed by the pass? | Typed values. The catalog calls every printer, and the only text a pass produces is `code`. |
| Does the tool render examples, or the messages that the test fixtures produce? | Examples. Each constructor has one, and the tool lists the codes that have none; fixtures miss every code no test reaches. |
| Do manifest, lock file, and registry problems, which are `Project.problem` strings today, join the catalog? | Yes, as a family with no nodes. They are shown beside diagnostics, and an audit should see them. |
| Does a compiler bug's message join the catalog? | No. A bug's message is for the compiler's authors, and it names an internal state. |
