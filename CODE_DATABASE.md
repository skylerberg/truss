# The Code Database

This document holds the design of stage0's code database. The database is
the mechanism behind [Incremental Everything](GOALS.md#incremental-everything):
it stores the compiler's knowledge of a project as facts, so that a change
costs work in proportion to the change, and so that an agent or a tool can
ask which definitions a change impacts.

## Properties

| Property | Meaning | How the design holds it |
|---|---|---|
| A change costs O(change) | Building, checking, proving, and answering a question do work in proportion to the rows that changed and the rows that depend on them, never to the project. | A reader depends on the smallest fact it reads. A fact that did not change stops propagation. No stage and no tool walks a package to answer a local question. |
| A question is a query | A tool's question is answered by selecting rows. A new question needs a query, not a new traversal with an index of its own. | Identity, placement, state, dependencies, diagnostics, and each fact with a reader of its own are columns and rows. |
| The database is a function of the files | Two databases built from the same files hold the same rows. | Every id is a function of the key it names. Two databases, such as two agents' worktrees, compare by set difference. |
| The compiler stays an ordinary compiler | A pass is a pure function from values to values. | One orchestrator owns the database. No pass sees a table, and no read starts a computation. |

## Roles

| Role | Owns | Never |
|---|---|---|
| Pass | One step of compilation: text to a syntax tree, a tree to core form and MIR, MIR to C. It takes its input as values, and takes read-only lookups for the inputs it discovers as it runs, such as the interface of a name it meets. | Sees SQL, a table, or the orchestrator. Starts another computation. |
| Orchestrator | The order of the stages, the stale rows, and each stage's recipe: select the stale rows, gather each one's input, call the pass, split its result into rows, and mark the readers of the rows that changed. It supplies the lookups and records each read. | Holds a language rule. |
| Store | The schema and every SQL statement, each under a name. | Knows a pass or a stage. |

A lookup reads a settled row. A read of a stale row, or of a row of a later
stage, is a compiler bug, as it is today. A tool queries only after
propagation.

A unit whose pass raises a compiler bug stays stale, and the orchestrator
drains the units that do not read it. A unit that reads the broken unit's
row raises the same bug. A unit whose pass raises any other exception, such
as a stack overflow, stays stale as well. That exception ends the command,
and the next command computes the unit again.

## Rules for the schema

| Rule | Reason |
|---|---|
| A table describes an entity or relates two entities, and its key is that entity's id. | A table keyed by an id that only another table can decode is the old hash table under another name. |
| A fact gets a column or a table of its own when some reader needs it without its neighbors. | Each boundary between facts is where recomputation can stop. A reader that takes a whole checked body for one boolean is recomputed by every edit of that body. |
| A marshaled value holds only a value that a pass reads whole: a syntax tree, a typed form, a MIR graph, lowered code. | A marshaled value hides its contents from queries, from agents, and from a later compiler written in Truss. |
| A language rule is a pure function in its pass, over rows that the orchestrator selects. SQL selects rows and keeps the orchestrator's books. | A rule written in a query is split from the rest of the language's rules and cannot be tested without a database. |
| A stage that needs one fact from many definitions reads those facts as one selected set, and depends on the set. | The stage is recomputed when the set changes, not when any body changes. |

## Entities and identity

| Entity | Key | Notes |
|---|---|---|
| Package | Its name | |
| Dependency | A package and a package it depends on | Holds the capabilities that the manifest grants. |
| Module | Package and name | The unit of declaring. |
| File | Package, module, and name | Holds the source text. |
| Definition | Module, path, and ordinal | Everything a path can name: a function, type, trait, capability, constant, theorem, method, impl, test, or law proof. |
| Item | The lowered instance: a definition with its ground type and capability arguments, or a generated table, drop, or entry | The unit of lowered code and of a test's key. |

| Decision | Reason |
|---|---|
| An id is the first 63 bits of the BLAKE2 digest of the key's canonical encoding, stored as the table's integer primary key. | The id is the same in a project's database, in a dependency's file, and after a rebuild, so a row of one database refers to a row of another with no table between them, and two databases compare row for row. A sequence number would need a mapping wherever one database names another's definition. The costs are eight bytes for an id where a sequence number takes three, and rows that land on pages in digest order. A collision within one database fails the insert as a compiler bug. |
| A definition the compiler supplies has a row: a method an impl inherits from its trait's default, and a method or impl that `derives` generates. Its `origin` says which, and `supplied_from` names the definition it comes from. | Call edges, generated MIR, and recursion groups belong to these definitions. Without rows they would need a table of bare paths, which is glue. The methods an impl inherits are then a query. |
| A module's top-level names are `entry` rows, written from the syntax alone, apart from `definition` rows. | Declaring a module's definitions resolves the owner of a method and the trait of an impl, which reads the top-level names of other modules. Those names must exist before any module is declared. |

## Tables

### Sources and names

```sql
package    (name)
dependency (id, package, dependency, capabilities)
module     (id, package, name)
file       (id, package, module, name, text)
entry      (module, name, position, kind, visibility, is_generic)
definition (id, package, module, path, ordinal, name, owner, kind, visibility,
            is_generic, origin, supplied_from, container, file, position,
            base, stop, text_hash)
syntax     (definition, tree, spans, syntax_errors)
import     (file, name, module)
impl       (definition, package, trait, type)
law_proof  (definition, package, trait, law, type)
```

| Fact | Where it is | Replaces |
|---|---|---|
| A definition's kind, visibility, container, and place | Columns of its `definition` row | The `declaration`, `place`, `container`, and `contained` name parts |
| A definition's text | The bytes of `file.text` from `base` to `stop`. `text_hash` is their hash, so a changed text is found without a second copy. | The `text` name part |
| The members of a type named `n` | The `definition` rows with that `owner` and `name`, by an index | The `members` name part |
| The declarations of a file, a module, or a package | The `definition` rows of that file, module, or package, in order | Three name parts that each held the whole list |
| The impls of a trait, or of a type | `impl` rows, by an index on each column | The impl index and its two views |
| A definition's syntax tree, its spans, and its syntax errors | Three columns of `syntax` | One tree in the file's parsed value and a second in the namespace |

No syntax tree of a whole file is stored. Parsing is cheap and pure, so the
orchestrator parses a file's text again when it declares the file's module
and when it checks the file's imports.

The built-in types and operations are `entry` rows of the intrinsic module,
written when the standard package is added.

### Facts of one definition

Each table's key is the definition's id. `state` is `value`, `failed`, or
`blocked`. A fact that a pass reads by a path alone, with no module and
ordinal, is keyed by the id of the path, which `definition.path` holds:
`type_facts`, `constant_value`, `derived_interface`, `generated_mir`,
`call_node`, and `recursion_group`. Such a fact is in the database of the
package that declares the definition. A method written on a type of another
package is an error, and its path names the other package, so a read by path
that finds no row there reads the project's database.

```sql
resolved        (definition, section, state, names, brackets, holes)
trait_header    (definition, state, value)
header          (definition, state, value)
interface       (definition, state, value, named, scope)
derived_interface (definition, state, value)
signature_check (definition, state)
type_facts      (definition, state, generics, copyable, plain, view, holds_function, contains)
constant_value  (definition, state, value)
contract        (definition, state, form)
body            (definition, state, form, tables, requires_run_forever,
                 places_without_keyword, mode_keywords)
body_mir        (definition, state, graph)
contract_mir    (definition, state, graph)
generated_mir   (definition, state, body, contract)
call_node       (definition, state, kind, callees)
recursion_group (definition, state, representative, members)
usage_check     (definition, state)
ownership       (definition, state, must_be_disjoint)
proof           (definition, state, value)
hole            (definition, position, home, start, stop)
verdict         (definition, position, code, start, stop, shows, proven, trusts_compiled_code,
                 failure, cited, cited_start, cited_stop)
```

One row can hold several facts. A group of columns that some reader takes
without the others is a fact of its own: a reader's edge names the group,
the reader's query selects only those columns, and a write marks the readers
of the groups whose columns changed.

| Fact | Reader that needs only it |
|---|---|
| `interface.value` | Every other definition that names this one. `named` and `scope` are read only to check the definition's own signature, contract, and body. |
| `body.form` | Build MIR |
| `body.tables` | The usage check, `explain` |
| `body.requires_run_forever` | The prover |
| `body.places_without_keyword`, `mode_keywords` | The ownership check |
| `syntax.syntax_errors` | Every stage that asks whether a part of a definition is broken |
| `hole` | `holes`, which reads no proof |
| `verdict` | The editor's proof states, and an agent that asks which obligations are not proven |

### Facts of a file, a package, and an item

```sql
grant          (dependency, state, capabilities, unknown)
dependency_use (package, state, unused)
item           (id, definition, key)
lowered        (item, state, code, is_evaluated, sites)
test_key       (item, state, key)
evaluation     (item, state, value)
unit           (item, profile, state, text_hash)
```

A build lists its linked items by `lowered.is_evaluated` and `lowered.sites`,
and reads the `code` of none of them. `unit.text_hash` is the hash of the text
of the item's translation unit in a build of that profile, and it names the
unit's object in the user's cache.

### Diagnostics

```sql
diagnostic (stage, definition, file, position, severity, code, start, stop,
            message, detail)
```

A stage writes a diagnostic's row with the fact that reports it. A
definition's diagnostic holds spans relative to the definition, so a
definition that moves in its file keeps its rows. A listing joins
`definition` for the file and the base.

### Edges and work

```sql
edge  (source_kind, source, target_kind, target, name, markers)
stale (stage, id)
```

One table holds every edge. An edge's source is a unit of a stage: the
stage and the id of its entity. Its target is a fact of an entity, an
entity that the unit's text names, or a selection. `markers` is the set of
reasons the edge exists, and a unit's edges are replaced together when the
unit is computed.

| Marker | Meaning | Followed by |
|---|---|---|
| `reads` | The unit read the target, so a change to the target marks the unit stale. | The orchestrator |
| `references` | The unit's code names the target: a definition, an import of its file, or a package. Resolve adds the names it resolves. Check body adds the functions and constants its typed form uses, the methods and member constants that its code names through a value's type, and the packages it uses. | `rename`, a search for references, and the checks for unused imports, dependencies, functions, and constants |
| `calls` | The unit's MIR calls the target. | Group recursion, lowering's check of calls, `graph` |
| `implements` | The unit is a method of an impl, and the target is the trait's method that it implements. A caller of the trait's method may reach every such method of the packages it can see. If the impl's interface is broken, the target is the trait, and every caller of the trait's methods is blocked. | Group recursion, `graph` |
| `instantiates`, `grows` | The unit is a generic function, and its typed form calls a generic function of its package with type arguments; `grows` when an argument holds the caller's own parameter inside a larger type. | The check for instantiation cycles |
| `claims` | The unit makes the target item a root of lowering: a test, a `main`, an evaluation that a proof needs. | Lower |

| Target | Names | Example |
|---|---|---|
| A fact | A group of columns and an entity's id | The `value` of a definition's `interface` |
| A lookup over the names | A lookup, the id of its scope, and a name | The entry `name` of a module; the members `name` of an owner; the impls of a trait for a type; the declarations of a file |
| An entity | A definition's path, or a file and the name of one of its imports | The target of a `references` edge |
| A selection | A set of edges or of rows, and the id of the entity that scopes it | The `references` edges into the imports of a file; the `resolved` rows of a file that hold no value; the `references` edges from the bodies of a package to its definitions; the bodies of a package that hold no value |

A change marks the units whose `reads` edge names a fact that changed, a
lookup whose rows changed in the columns it reads, or a selection that
gained or lost a member. A lookup of a name that is not declared is an edge
like any other, so declaring the name later marks its reader.

No table holds the place of each reference. `rename` follows the
`references` edges into a definition to find the definitions that name it,
and `Inspect.References` finds the spans in those definitions alone.

## Stages

The orchestrator runs the stages in this order. Each row is one recipe.

| Stage | Unit | Pass | Input | Rows written |
|---|---|---|---|---|
| Parse | File | `Parser.parse_source` | The file's text | `entry`, parse diagnostics |
| Declare | Module | The declaring half of `Resolve.Namespace` | The parsed files of the module; lookups of entries, modules, and dependencies | `definition`, `syntax`, `import`, `impl`, with a row for each derived impl |
| Supply | Impl | The trait's methods that the impl does not write | Name lookups | A `definition` row for each method the impl inherits or derives |
| Claim roots | Test, or a package's `main` | `Lowering.make_root` | The definition's path | `claims` edges to the items that run it |
| Resolve | Definition | `Resolve.resolve`, which walks the definition once | The definition's tree; name lookups | A `resolved` row for each section, `references` edges |
| Resolve grants | Dependency | `Interface.Grants.resolve_grant` | The capabilities the manifest grants; name lookups | `grant` |
| Check imports | File | `Resolve.list_file_diagnostics` | The file's text; the imports that a `references` edge names; whether a `resolved` row of the file holds no value | Diagnostics |
| Read trait headers | Trait | `Resolve.make_trait_header` | The tree and its resolved names | `trait_header` |
| Evaluate constants | Constant | `Interface.Constants.evaluate_constant` | The trees and resolved names of the constants it names | `constant_value` |
| Elaborate headers | Trait, impl, or capability | `Interface.Elaborator.elaborate_header` | The tree and resolved names; trait headers, constant values, grants | `header` |
| Elaborate | Definition | `Interface.Elaborator.elaborate_definition` | The tree and resolved names; headers | `interface` |
| Derive interfaces | Derived impl | `Interface.Impls.derive_interface` | Interfaces | `derived_interface` |
| Compute type facts | Type, with the types of its recursion | `Interface.Properties.compute_component_facts` | Interfaces; the type facts of the types its fields name | `type_facts` |
| Check signatures | Definition | `Interface.Check.list_diagnostics` | Interfaces, type facts | `signature_check`, diagnostics |
| Infer | Definition | `Infer.check_contract`, `Infer.check_body` | The tree, resolved names, and interface; lookups of interfaces and contracts | `contract`, `body`, `body_fact`, `references` edges |
| Build MIR | Definition | `Mir.make_body_part`, `Mir.make_contract_part` | The body's and contract's forms | `body_mir`, `contract_mir` |
| Generate MIR | Derived method | `Infer.derive_form` | Interfaces and contracts | `generated_mir` |
| List calls | Definition, with the supplied methods | `Mir.Call_edges.list_path_edges`, `Mir.Call_edges.find_implemented_declaration` | MIR and interfaces | `call_node`, `calls` and `implements` edges |
| Group recursion | The definitions whose `calls` or `implements` edges changed, and their groups | Strongly connected components | The definitions that both reach and are reached by a changed one, and the edges among them | `recursion_group` |
| Check bodies | Definition | `Usage.check`, `Ownership.check` | The body's tables, its MIR, and its ownership modes | `usage_check`, `ownership` |
| Check an impl, a type | Definition | `Package_checks.run` with `Sealed`, `Impl`, or `Type` | Interfaces | Diagnostics |
| Check instantiations | Package | `Package_checks.run` with `Instantiations` | The `instantiates` edges of the package's bodies | Diagnostics |
| Check tests | Package | `Package_checks.run` with `Tests` | The package's declarations | Diagnostics |
| Check unexported | Package | `Package_checks.run` with `Unexported` | The `references` edges from the package's bodies to its definitions | Diagnostics |
| Check dependencies | Package | `Package_checks.run` with `Dependencies` | The packages that the package's bodies reference | `dependency_use` |
| Prove | Definition | `Prover.prove` | MIR, contracts, `ownership`, `recursion_group`, `body.requires_run_forever` | `proof`, `hole`, the prover's warnings, `claims` edges to the items of its evaluations |
| Decide | Definition | `Prover.pose`, the solver, `Prover.list_states` | The proof, the results of running its evaluations, and the solver's answers | `verdict` |
| Lower | Item | `Lowering.lower`, `Lowering.check_calls` | MIR and interfaces; the callees of the item's definition and of each callee | `lowered`, `references` edges to the items its code names |
| Key tests | Item, with the items of its reference cycle | `Lowering.derive_test_keys` | `lowered`, and the test keys of the items it references | `test_key` |
| Evaluate | Evaluated item | None: the command runs the item's evaluator, which is compiled code, and records the result | The item's `lowered` code, the test key of its evaluator, and the layout of its type | `evaluation`, `references` edges to the items that its value names |
| Render, once for each profile | Item | `Lowering.render_unit` | The item's `lowered` code, or the `evaluation` of an evaluated item, and the interfaces of the types that the unit defines. A development unit: the `lowered` code of each small callee that it copies. A release unit: the place of each definition whose lines it names, and that definition's file. | `unit` |

A unit reads facts of earlier stages. Where a unit reads a fact of its own
stage, the orchestrator orders that stage's units: packages in dependency
order, and the types of one package by the strongly connected components of
their fields' types, so that a type's facts are computed after the facts of
the types it holds.

An `item` row exists while a claimed item reaches it. A unit that gains a
`claims` or `references` edge to an item inserts the item's row and marks
its Lower and Key tests units stale. A unit that loses such an edge asks
whether any claimed item still reaches the target. A depth-first search
follows the `references` edges into the target backward, one referrer at a
time, and stops at the first claimed item. If none reaches the target, the
item's rows are deleted and the items it referenced are asked the same.

A command says how far to drain: `check` drains through Decide, and `test`
and `build` through Key tests, for the packages they name and the packages
those depend on. Saving a file drains through the checks of packages. Lower
and Key tests drain the items that the claims of those packages reach, and
Prove and Decide the definitions of the packages a command names, or of the
files an editor has open. A build drains Render of its profile for the items
that its roots reach.

A drain selects its units from the `stale` rows, so a stage with no stale row
costs one seek. A drain for packages joins the stale rows of a stage with
their entities and keeps the entities of those packages. Lower asks, for each
stale item, whether a claim reaches it: the same depth-first search follows
the `references` edges into the item backward, through settled units only,
and stops at the first settled claim of the command's packages. Lower then
continues from each unit it lowers to the stale items that the unit
references, and asks again about the stale items that remain until none is
reached. Key tests starts from its stale items and the items whose keys read
theirs. One statement lists the settled claims of the command's packages
among those items, and the drain keys the items that those claims reach
through settled units. An item that they do not reach stays stale. Render
takes its stale units from the query that lists the linked items. A drain for
an editor's files is the exception: it joins from the definitions of those
files, because the proofs of every other file can be stale.

Evaluate and Decide each take an input that no pass computes. A command
runs the evaluations that its Decide units or its program need, which are
compiled code, and records each result as the `evaluation` of its item.
Decide asks the solver about the queries of all its stale units at once, so
that the solver answers them in parallel, and then computes each unit from
the solver's answers. A Decide unit reads its proof, and the test key and
the `evaluation` of each item that the proof evaluates, so it is stale when
the proof changes, when the code that an evaluation runs changes, or when a
result changes. Where an evaluation has not run, Decide poses its queries
without the result. An evaluation can stop without a value: it reaches a
`todo`, it panics, or it reaches its limit of CPU time. A Decide unit that
read such a result stays stale, and the next command that needs the value
runs the evaluation again.

## Questions

| Question | Asked by | Answered from |
|---|---|---|
| The diagnostics of a file | Every command, the editor | `diagnostic` joined with `definition` on the file |
| Does a package have an error | `test`, `build` | `diagnostic` by package and severity |
| A definition's dependents and its dependencies | `graph`, a review of a change | `edge` with `reads`, by target or by source |
| The signatures a change impacts | An agent after an edit | The closure of `reads` edges from the rows that changed, kept to sources that are `interface` units |
| Where a definition is named | `rename`, the editor | `edge` with `references` into it, then `Inspect.References` on each source |
| Where a module is named | `rename` | `edge` with `reads` into the module's lookup: the definitions whose names were resolved through it, and the files whose `use` items name it. `Inspect.References` then runs on those definitions and on the definitions of those files. |
| The functions and constants nothing uses | Check packages | The `references` edges of the package, handed to the pure check |
| The holes and the obligations not yet proven | `holes`, an agent proving | `hole`, and `verdict` rows that are not proven |
| The tests a change can affect | `test` | The `test_key` rows whose key changed |
| A definition's callees and its recursion group | `graph`, lowering | `edge` with `calls`, `recursion_group` |
| The translation units of a program | `run`, `build`, `test`, a check that runs an evaluation | One recursive query over the `references` edges from the program's roots, joined with `lowered` and `unit`, which also says whether each item's Render unit is stale. From an evaluated item the query follows the edges of its evaluation, which name the items in its value, and not those of its lowered code, which name its evaluator. |
| The rows that differ between two databases | `upgrade`, two agents' worktrees | Each table of one attached database minus the same table of the other |

## Costs

| Operation | Work |
|---|---|
| Open a database | Open the file and attach the dependencies' files. Nothing is rebuilt. |
| A command with no change | The queries of its questions. |
| Edit one body | Parse the file. Declare its module, which rewrites the `syntax` row of the edited definition and the `base` of those after it. Run Resolve through Decide for that definition. Rewrite its fact rows that differ. A check of the package runs only if a fact it reads as a set changed. |
| Edit a signature, or add a definition | As above, and the units whose `reads` edges name the rows that changed. |
| Build from nothing | Every unit once. Each read is a statement and an unmarshal: there is no cache of decoded values. |
| A build with no change | One query lists the linked items. Each item's object is found in the user's cache by its stored hash. The sites of the linked items are rendered as one unit, and the objects are linked. |
| A build after an edit to one body | As above, and Lower through Render for the edited item, whose unit is compiled. In a development build the units of its callers are unchanged. In a release build the units of the other items of its file are rendered again, and compiled where a line they name moved. |
| Replace a dependency | Each table of the new file minus the old one, and the old one minus the new, gives the rows that differ. One statement marks the readers of the facts and the lookups that those rows back. Recursion groups are recomputed for the callers of the definitions whose `calls` or `implements` edges differ. |

## Further decisions

| Decision | Reason |
|---|---|
| A dependency's database is a SQLite file in the user's cache, attached read-only. Registry packages beyond the standard library share one merged file. | Every database of a machine shares one copy of the standard library. SQLite attaches ten files at most. |
| A package build records no `reads` edge and marks no reader. | A package's database is built once from nothing and never updated, so no unit of it runs a second time, and the build deleted its `reads` edges before it saved the file. Writing and then deleting them took 6.0 s of the 30 s that the standard library takes to build. The edges that the build's own checks select, `references`, `instantiates`, `calls`, and `implements`, are still written. |
| A change set is one transaction, and a trial is a copy of the database in memory. | A crash leaves the state before the change set or after it. A trial never writes the worktree's database. |
| The solver's answers stay in the user's cache, keyed by query, and a `verdict` row records the answer that an obligation got. | Worktrees and CI share answers. A command with no change reads verdicts and runs no part of the prover. |
| `Prover.decide` splits into `Prover.pose`, which gives a proof's queries, and `Prover.list_states`, which renders the solver's answers. Decide calls both. | Each half is a pure function, and the solver's run between them is the orchestrator's. |
| A proof's obligations stay in the `proof` value, and no `obligation` table holds them. | A query states the result of running each evaluation that it names, so it is known only when Decide runs, and Decide is the one reader of an obligation. The rows an editor or an agent reads are the `verdict` rows: a site, its message, and whether it is proven. |
| A `verdict` row holds its failure as a diagnostic relative to its definition, and the clause that the failure cites as a definition and a span in it. The listing places both in their files. | A diagnostic placed in a file would be stale after every edit above it. Placed by `definition.base` when it is listed, a verdict is computed again only when its proof or the spans it names change. |
| A fact is unchanged where its row holds the same bytes. | A pass is a function of its input, so it builds an equal value with the same sharing, and the value marshals to the same bytes. If a pass ever built an equal value with other sharing, the fact would count as changed, which costs a recomputation and leaves no stale read. A write therefore unmarshals no value to compare it, and a column may hold bytes that are no marshaled value. |
| An item whose layout needs a type defined as `todo` is lowered to that type's path, and a test key holds the paths of every such type that its item reaches. | `test`, `build`, and `holes` ask which types defined as `todo` a root reaches. The root's key answers, so no command walks the edges of the units that could not be lowered to find the types again. |
| A fact names the stage that writes it, and forgetting a unit removes the facts of its stage. | A recipe that lists its stage's facts a second time can forget a unit and leave the unit's row. |
| The call graphs and the references between items are `edge` rows, and no graph is held in memory between commands. | Opening a database rebuilds nothing, and `graph` reads the same rows as the orchestrator. |
| An object is named by the hash of its translation unit's text, and the hash is a fact. | A build that renders each unit to learn its object's name does work for every linked item, changed or not. With the hash stored, a build reads one row for each linked item, and asks for a unit's text only where the user's cache holds no object for it. One function renders the text for the stage and for that request, and the C compiler checks the text against the hash. The hash is still a hash of the text, so a read that Render did not record shows as a differing `unit` row when a propagated database is compared with one built from nothing. |
| A development unit holds no position. It names each site by a symbol, and one unit of the program defines every site with its file, line, and column. | An edit that moves a definition changes that one unit and no other. The sites of a program are the `sites` of its linked items. |
| A capability's symbol is a weak definition in each unit that names it. | The linker keeps one definition, so the symbol has one address in the program, and no unit lists the capabilities of every linked item. |
| A test key is a hash of the text of each item that its item reaches, with the names that the text links by. | A fragment is rendered once, and its hash is the hash of that text. Renaming a definition, or an edit that moves a site inside a definition, changes the keys of the tests that reach the definition, and they run once more. A key that survived both needed a second rendering of every fragment, with each name replaced by its position. |
| A development unit copies a small callee only where the callee's package is outside the project. | An edit to a small function of the project leaves its callers' units unchanged. When the project gains or loses a package, every development unit is rendered again. |
| A release unit names a file by its package and its path in the package. The C compiler's `-fdebug-prefix-map` puts the package's directory in the project in place of the package's name. | The line table of a release build names each file by its path in the project, which the workspace knows and the database does not. With the directory in the compiler's flags, it is part of the object's name, and a unit's text is a function of the database alone. |
| A release unit reads the whole text of each file whose lines it names. | A line number is a count of the lines above it. An edit to a file therefore renders again the release units of the file's items, and a unit whose lines did not move comes out unchanged. |
| The result of an evaluation is a fact of its item. | Decide and Render read it as they read any fact, so no command hands results to a stage, and the back end renders no unit of its own. The user's cache still holds each value under the key of its evaluator's code, so another worktree takes the value without running the evaluator. |
| A recursion group is found by two recursive queries: the definitions a changed definition reaches over `calls` and `implements` edges, intersected with the definitions that reach it. The strongly connected components of that set are computed in memory and written as `recursion_group` rows. | Every cycle through a changed definition lies inside that set, so no component is kept between commands. The two queries walk the changed definition's callees and callers inside SQLite, and only run when its `calls` or `implements` edges change. |
| The edge from a trait's method to a method that implements it is stored once, by the implementing method, in its own package's database. | Which impls a caller can reach depends on the packages the caller can see. With the edge stored by the implementer, each package's view is the edges of the databases it attaches, and no unit exists for each pair of a trait method and a calling package. |
| When a dependency's file is replaced, a differing row of `definition`, `entry`, `impl`, or another table of names marks the readers of every lookup that the row backs, under the row's own name: the entry `name` of its module, the members `member` of its owner. A differing fact row marks the readers of each of its facts. | The old file and the new one are attached together, so the rows that differ are one query for each table. Marking by row and name leaves a reader of one function untouched when another function of the same module changes. A lookup that reads only some columns of a differing row is recomputed once and found unchanged, which costs one unit and can never leave a stale read. |
| A statement that joins names its driving table first and joins with `CROSS JOIN`, which SQLite never reorders. | The store's statements have no statistics to plan from, and the planner's choice differs between versions of SQLite. A newer planner made the edge table the outer loop of a recursive step, so each step read every edge, and CI's jobs took ten times as long as the same work on a machine with an older SQLite. |
| A membership test on the rows of a join is written `+column IN (…)`, and a bare `column IN (…)` is written only where the list is to drive the index. | SQLite uses a list on a column that continues an index as part of the seek, once for each value of the list. The statement that lists the call edges among the definitions of a recursion scope tested each edge's target against the scope this way, so it sought the edge index once for each pair of definitions: 16 s of a 30 s build of the standard library, from one statement that returns 20 thousand rows. The unary plus keeps the test out of the seek. |
| A drain selects its units from the `stale` rows, and from the entities in its scope only for the files an editor has open. | A command with no change must cost the same at every project size. Selecting from the scope read every definition of the named files once for each stage, and walked every claimed item once for each level of the deepest chain of references. On 10,400 functions a command with no change took 438 ms, and an edit to one body took 729 ms, of which 17 ms was the edit's own work. A stale item that no settled claim reaches stays stale, and each command asks about it again. |
| A search for a claim that reaches an item goes depth first, and reads one referrer of an item at a time. | A breadth-first query read every referrer of an item before any referrer of those. For a function that every module calls, that is every caller, although a test claims the first caller's own caller. Removing a module of 26 functions took 4.6 s on 10,400 functions, of which 4.1 s was 83 such searches. Depth first, a search reaches a claimed item after as many steps as the chain to it is long. A search that finds no claim still visits every item that reaches its target. |
| A lookup's statement has an index on every column that it filters by. | A statement that filters a package's definitions by member name with an index on the package alone reads the whole package each time it runs. The count of statements does not show it. |
| A fact holds everything that its reader needs to use it. `type_facts` holds the type's generic parameters beside the conditions written over them. | A reader that must fetch a second fact to interpret the first makes every question cost both reads. Deciding whether a type is plain read the type's facts and then its whole interface for the parameters' names, at every operand of every body. |
| A reader finds the interface of a top-level definition, an impl, a test, or a law proof by the key that its path determines, and reads no declaration first. | An absent row whose unit is not stale means that the path is not declared, and a first write or a removal of the interface marks its readers. The declaration read cost one statement and one edge at every mention of a definition. |
| A trait's interface holds its transitive supertraits. | Testing a bound walked the supertraits of the bound's trait and read each one's interface, at every question about a type parameter. With the closure stored, the test reads one interface. |
| A pass reads its own definition's tree, spans, syntax errors, and imports, and the packages visible to its package, once, and passes the values to the functions that use them. | The lookups were free when they read hash tables, so each function fetched the tree where it needed it. Name resolution walked a definition three times, once for each section, and read its syntax in each walk. It read the definition's imports and the package's dependencies at every path. |
| A function that asks several questions of one row reads the row once. Overload resolution lists a type's members of a name once for the three receiver modes. The exhaustiveness check takes a type's constructors with their field types. | Each helper fetched the interface that it needed. A method call looked up the same members up to six times, and one step of the exhaustiveness check read a type's interface once for its constructors and twice more for each constructor's fields. |
| One `edge` table holds dependencies and the program's relations, with a set of markers on each edge. | A unit's edges are written and removed in one place, one index by target answers every question of the form "which units point at this", and a pair of units is stored once however many relations hold between them. |

## Marshaled values that remain

| Column | Read whole by |
|---|---|
| `syntax.tree`, `syntax.spans` | Resolve, Elaborate, Infer |
| `resolved.names`, `brackets`, `holes` | Elaborate, Infer, `explain` |
| `header.value`, `interface.value` | Every stage after Elaborate |
| `contract.form`, `body.form`, `body.tables` | Build MIR, Check bodies |
| `body_mir.graph`, `contract_mir.graph` | Check bodies, Prove, Lower |
| `proof.value` | Decide |
| `verdict.failure` | The listing of a file's proof diagnostics |
| `lowered.code` | Key tests, Render, and the trace of the code that a root reaches, for `holes` and for a release build's refusal of a `todo` |
| `evaluation.value` | Decide, Render |
| `definition.path`, `item.key` | The orchestrator, to give a pass the key it names |

## Checks of the build

| Claim | Evidence |
|---|---|
| A local change costs the same at every project size. | `database_tests` counts the statements and the virtual machine steps of an edit to one body, of lowering the code that the tests reach after that edit, and of proving and deciding one file, in four modules and in forty. `stage0/tools/database_benchmark` times the same edits at each size. |
| A command with no change computes nothing. | `database_tests`: deciding a file again decides no definition, and a database opened again recomputes no unit. `build_tests`: a development build and a release build of a program that was built before render no unit. |
| A command with no change selects its units in the same number of steps at every project size. | `database_tests` counts the steps of lowering the code that the tests reach, and of selecting the stale proofs of a package, in four modules and in forty. |
| A build renders the units of the items that an edit changes. | `database_tests`: after an edit to one body, listing the linked items of a program renders the development unit of that item alone, with as many statements in forty modules as in four and as many steps more than a listing that renders nothing, and the release units of that item's file and of no other. |
| A question costs the same at every project size. | `database_tests` counts the statements and the steps of listing a file's diagnostics, a definition's dependents and dependencies, and the definitions that name it, in four modules and in forty. |
| A propagated database equals one built from nothing. | `database_tests` compares every table after each of seventeen edits, and `stage0/tools/database_fuzz` compares them after random edits. |
| No pass sees the database. | No library under `stage0/type_checker`, `stage0/mir`, `stage0/prover`, or `stage0/codegen` depends on the store or the orchestrator, and the store depends on no pass. |

A count of statements does not see a statement that does more work than its rows. Four have: a lookup with no index on a filtered column, a join that a newer planner reordered, a membership test that drove an index seek, and a listing of a unit's edges that named no unit kind and so scanned the edge table. Each statement's count of virtual machine steps does see them: a seek is one step at any size of table, and a scan or a nested loop is a step for each row. `Sql` reads the count with `sqlite3_stmt_status`, through a stub that takes the statement handle from the first field of the binding's wrapper and checks it against the statement's text. `TRUSS_DATABASE_COUNTS=1` prints the steps and the time of each statement text beside its runs, and the tests that compare statements at two sizes compare steps as well: the larger project may run a tenth more.
