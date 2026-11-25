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

## The compiler before the catalog

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
needs. A family is two modules. An interface-only module, such as
`usage.mli`, defines the payload types once, and passes construct them:

```ocaml
type t =
  | Unused_variable of { binding : Core.origin; constant : Path.t option }
  | Self_comparison of { comparison : Core.origin; operator : Language.Comparison.t; is_float : bool }
  | ...
```

A description module, such as `usage_description.ml`, describes each
value:

```ocaml
val describe : Usage.t -> Nodes.description
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

The project family's types are `Project_catalog.Problem`. The lexer and
the manifest parser keep their light dependencies, and an audit reads one
directory: every sentence of a family is in its description module.

## The renderer

The renderer is the only code that reads a definition's tree, spans, and
text for a diagnostic. It turns a description into a `Diagnostic.t`, and
it owns every layout decision: indentation, separators, and where a brace
goes.

A pass returns catalog values, `Catalog.diagnostic` after parsing and
`Syntax_catalog.Syntax_diagnostic.t` before, and the database stores them
as they are. The database renders a value when it lists diagnostics, with
the definition's current spans and text. No unit reads spans or text to
report a diagnostic, so a reformat changes no stored fact and reruns no
check. A prover verdict stores its site and its failure the same way.

A node is an origin in the definition being checked, the definition
itself, or an origin in another definition. The prover quotes a callee's
clause through the last, and the renderer reads that definition's text
for the quote. An edit is always in the definition being checked, and so
is a location, except the note that points at a cited clause in the same
file; a clause in another file is cited by its path and line.

The lexer and the parser report before a tree exists. Their payloads hold
spans in place of nodes, and the listing renders them with the file's
text.

## Fixes

A fix is a title, written in `describe`, and a list of edits on nodes.
Every fix built after parsing falls into these edits:

| Edit | Uses | Read text before the catalog |
|---|---|---|
| Replace a node with code | Write `UInt64`, `None`, `_`, a view type, `generic X`, a constant's path, the checked method; every spelling fix | No |
| Insert code before a node | `mut `, `own `, `indirect `, `let _ = `, a label | No |
| Insert code after a node | `.copy()`, `(..)`, `.method()`, ` when C` | No |
| Delete from one node boundary to another | A mode keyword, a label, a parameter default | One deletes `start + 4` bytes for `mut ` |
| Remove an entry of a list with its separator | A derived trait, a `RunForever`, a pattern alternative | Yes |
| Remove whole lines | An unused `use`, unreachable statements, an unreachable arm | Yes: line starts, indentation, a trailing newline |
| Add lines after a node, at its indentation | The missing arms of a `match` | Yes |
| Add a clause to a signature, or a capability to `uses` | The prover's `requires` and `uses Panic` | Yes |

Every edit that read text became a layout decision in the renderer. The
survey found no fix that needs an edit outside this table. The lexer's and
the parser's edits name spans, since they report before a tree exists, and
their description modules write the code.

## Enforcement

- A pass returns catalog values, and the database stores them. No pass
  has a channel for a rendered diagnostic.
- A rendered diagnostic and its fixes are private records, and
  `Diagnostic.make` is gone. Their one constructor,
  `Diagnostic.For_rendering`, is for the description library;
  `.github/scripts/for_rendering.sh` rejects its use anywhere else but
  tests and tools.
- The parser, resolution, the interface checks, and inference do not
  depend on the `diagnostic` library. The lexer reads its own rendered
  fixes to recover, and the prover reads diagnostic codes to tell panic
  obligations from the rest; neither can build a rendered diagnostic.
- An edit names nodes, so a pass has no span to compute. The parser's
  problems carry the spans that their fixes need, and
  `Parsing_description` writes the code. The lexer's fixes are a typed
  edit vocabulary; only code that the lexer computes, such as a number's
  spelling, a rename, or a copied indentation, is a `Spelled` string.
- The passes' lookups, `Resolve.Names.lookups`, offer no spans, no text,
  and no offset of a definition in its file. A pass sees the order and
  nesting of nodes, `Source.Node_order`, the parts that hold a syntax
  error, and a definition's file and index in it. The renderer, the
  driver's commands, and code generation read spans and text through
  `Resolve.Names.source`.
- Two readers of source text remain, for text in the compiled program,
  not in a diagnostic: code generation, which writes a site's position
  and an assertion's text into a panic, and the derived `Deserialize`,
  which names a broken invariant in its error through
  `Infer.Lookups.read_clause_text`.

What remains for review is the `code` fields, the `Spelled` edits, and
the printers that fill them.

## Conversion

One pull request converts everything, and the old mechanisms go in it:

1. Add the payload pieces, `description`, the node edits, and the
   renderer. Store catalog values in the database, and render them where
   diagnostics are listed.
2. Convert one family at a time: its codes become catalog constructors,
   and its call sites report them. Delete the pass's `report` wrapper,
   `read_span`, quoting, and edit helpers as its last call site goes.
3. Remove `Diagnostic.make`, and remove `read_text` and `read_spans`
   from the passes' lookups.

## Decisions

| Question | Decision |
|---|---|
| Do payloads hold `Types.ty` and `Path.t`, or text printed by the pass? | Typed values. The catalog calls every printer, and the only text a pass produces is `code`. |
| Does a tool render every diagnostic from examples? | No. Examples for every constructor took about 5,300 lines, more than the sentences they render. The description modules are the audit. |
| Do manifest, lock file, and registry problems, which are `Project.problem` strings today, join the catalog? | Yes, as a family with no nodes. They are shown beside diagnostics, and an audit should see them. |
| Does a compiler bug's message join the catalog? | No. A bug's message is for the compiler's authors, and it names an internal state. |
