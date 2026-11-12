# Truss Code Database

This document describes stage0's code database: the part of the toolchain
that holds every definition being worked on and everything computed from
them, keeps those results current as files change, keeps each computed
result so that no state computes it twice, and answers dependency questions.
It follows [GOALS.md](GOALS.md) and the cost of a change that
[DESIGN.md](DESIGN.md) promises, and serves the stages described in
[TYPECHECKER.md](TYPECHECKER.md) and [CODEGEN.md](CODEGEN.md). The `truss`
command line, which [CLI.md](CLI.md) describes, is its client, and the only
program it serves: the database is a library, and every command and report
is the command line's.

GOALS.md asks that a change cost O(change), not O(project), for building,
testing, and verifying, and that agents can see exactly the effects of their
changes and where their work overlaps with other agents'. The database makes
both possible. It:

- holds the inputs of every project being worked on: its packages, their
  manifests, and the text of every module
- maintains each result a driver demanded, and every result that one
  reads, as inputs change, by pushing each change, one phase of the
  compiler at a time, to the readers of the values that really changed
- gives every result a fingerprint, and keeps each saved result as a fact
  under the key of its reads, so that another worktree, a commit, a
  branch gone back to, or a new process finds it instead of computing it
- writes each state as a difference over an earlier one, and opens a state
  by sharing the whole state it started from, so that a worktree, a commit,
  or a trial of a change costs only its changes
- keeps the results of expensive steps, such as a test run or a C compile,
  under a key built from exactly the input each one consumed
- answers questions about dependencies in terms of definitions: a
  definition's readers, a change's effects, the work each `todo` blocks, and
  where two worktrees' changes overlap
- runs as a background process for each project being worked on, so
  commands in different worktrees are answered at once

It does not:

- decide the meaning of code. The stages do, as queries the database runs.
- hold anything that cannot be rebuilt. Text files are the source of truth,
  as DESIGN.md says, so deleting the database loses only time.
- keep history. Version control does that. The database knows the state of
  each worktree now, and of the commits it was asked about.
- share results between machines yet. See [Not built](#not-built).

## Structure

The database is four layers, each behind one narrow interface:

```text
 command line   language server   agent tools
        \              |              /
         ▼             ▼             ▼
   ┌──────────────────────────────────────┐
   │ Database: a project's files as        │  data, by definition and part
   │ inputs, manifests, registry, git      │
   └──────────────────────────────────────┘
                     │ Session
   ┌──────────────────────────────────────┐
   │ Session: states by name, saving,      │
   │ trials, graph questions, the          │
   │ background process                    │
   └──────────────────────────────────────┘
                     │ Engine
   ┌──────────────────────────────────────┐
   │ Engine: states, phases, pushing       │◀── Query ── compiler stages
   │ changes, facts, artifacts             │
   └──────────────────────────────────────┘
                     │ Store
   ┌──────────────────────────────────────┐
   │ Store: values by hash, results by     │
   │ key, pointers                         │
   └──────────────────────────────────────┘
                     │
                ~/.cache/truss
```

| Interface | Library | Used by | Offers |
|---|---|---|---|
| `Query` | `query` | Compiler stages | Declaring phases, inputs, and queries, and reading them while a query runs |
| `Engine` | `engine` | `Session`, `Database`, and tests | Setting inputs, keeping results current, bases, writing and opening states, and walking the graph |
| `Store` | `store` | `Engine` and `Session` | Bytes by content hash, results by key, and pointers |
| `Session` | `session` | `Database` | States by name in the store, trials, graph questions about a state, and the background process |
| `Database` | `database` | The command line, and the tools on it | A session for each project's files, and answers about it as data |

`Query` and `Engine` are two views of one implementation, `Incremental`,
which nothing else names. These rules keep each interface narrow, so that
each layer can be replaced without touching the others:

- **Stages see only `Query`.** A stage never sees the engine, the store, the
  file system, worktrees, git, or another session.
- **`Session` knows no stage and no project.** It keeps states, and the data a
  client attaches to each. Manifests, packages, and commits are the
  client's concepts.
- **`Database` knows the project, and no stage beyond it.** It reads
  manifests and module files, and sets the packages and their modules' text.
  It does not depend on code generation or the prover.
- **A driver sets a stage's input through its session,** with
  `Database.set`, and that is the one way: the roots of code
  generation and the solver's answers are set so. A stage declares the
  input; the database needs no function for it. Inputs are the only way
  anything outside the stages reaches them.
- **A driver holds no engine.** The command line reads through a session's
  context, as a query would, and does not list the engine, the store, or
  the session layer. A trial, a commit, a published package, and the
  standard library's own state are each a session like any other.
- **A session's files are one abstraction.** A worktree's directory, a
  commit, and texts in memory each give the files' paths, a stamp for each
  that says whether it changed, and each one's text. A session is opened
  and kept current the same way whichever it has.
- **Answers name definitions, never engine nodes.** A graph question returns
  paths and parts, so a different engine can answer the same questions.
- **Each query's key and value types belong to the stage that declares
  them.** The database knows them only as values it can compare and save.
- **Code generation does not see the store.** A test run is handed functions
  that find and keep results by key, and the directory object files go in.
- **Whether a session runs in the background process or in the client's own
  process makes no difference to the client,** since the background process
  runs the client's own code.

## The engine

### The graph

An engine is one *state*: one set of inputs and the results computed from
them, which is a worktree as it is now, a commit, a merge of two branches,
or a change that is only being tried. Its graph has a *node* for each input
and for each query result, named by the input or query and its key. An *edge* runs from a
node to each node it read the last time it was computed, and the engine
keeps every edge in both directions:

- **Edges are learned, not declared.** A query reads through its context
  while it runs, and each read adds an edge. Truss's dependencies are not
  known before a query runs: a body depends on its name lookups' results,
  which depends on the names it uses.
- **A read that found nothing is an edge too.** Asking for the constants
  named `count` in a file, and finding none, depends on that answer. Adding
  such a constant later changes the answer, and so reaches the reader, as
  SPECIFICATION.md requires for patterns.
- **A change follows the edges in from readers.** The edges out name the
  dependencies to check when a result may have changed, and answer "why does this
  depend on that?"

### Phases

Every query has a *phase*, and reads only queries of its own phase and of
earlier ones. Reading a later phase is an error, raised at the read. The
database holds no list of phases: a phase is declared with the phases it
may read, as a query is declared with its phase, and the compiler declares
its own, in `Phases`, each after the one before:

| Phase | Its queries compute |
|---|---|
| Syntax | A file's tokens and trees, the names it defines, its imports, and which modules exist |
| Declarations | Each file's and package's declarations, a definition by name, a type's members by name, and each definition's tree |
| Resolution | The meaning of each name in a definition |
| Interfaces | Signatures, shapes, constants' values, and the `impl`s found for a type |
| Bodies | Checked bodies, moves and loans, patterns, and the other facts found in a body |
| Checks | The rules that span a package |
| Proofs | Each package's call graph, and each definition's obligations as the solver's queries, which PROVER.md describes |
| Verdicts | Whether each definition's obligations hold, from the solver's answers |
| Diagnostics | Every stage's diagnostics for a file |
| Lowering | Each instance's LIR |
| Linking | Each instance's own hash, and its references |
| Recursion | Which instances reach each other |
| Keys | The key of everything an instance can reach |

Phases let a change stop exactly where it stops mattering. When a
phase is brought up to date, every earlier phase is final, so the engine
knows which of the phase's results read something that *really* changed,
and touches no others.

### Bringing a state up to date

A clock orders changes. Each change takes the next time, and each node
records when its result last changed and when it was last found current.
Setting an input to a value equal to its old one does nothing. Otherwise:

1. The input takes its new value, and its readers are queued, each
   under its phase.
2. The engine takes the first phase with anything queued, and *marks* each
   queued result, and their readers within the phase. Marking sets a
   flag and nothing more.
3. Each marked result is then brought up to date. Its dependencies are
   brought up to date first, in the order it read them. If one of them changed after
   the result was last found current, the result is looked for as a fact
   and, failing that, computed again; the check stops at the first such
   read, since a later read may not be made at all once an earlier one gives
   a different answer. Otherwise the result is found current without being
   computed.
4. A result that comes out different queues its readers in later phases.
   A result that comes out the same queues nothing. This is early cutoff.
5. The engine continues to the next phase with anything queued, until none
   has.

So a change costs the readers of the values that really changed, plus,
within one phase, their readers. Editing a function's body computes its
tree, its resolved form, its interface, and its checked body again. The
interface comes out the same, so the callers' bodies, which are of a later
phase, are not marked at all, however many there are. The engine counts the results
it marks, finds current, computes, finds as facts, and copies, and tests
compare those counts for the same edit in a small package and a large one
(see [Checking the engine](#checking-the-engine)).

- **A result a driver demands becomes a root, and the engine maintains
  every necessary result.** A *root* is a result that a driver, such as a
  command, demanded through a session's context. A result is *necessary* if
  it is a root or a necessary result reads it, the term Jane Street's
  Incremental uses. Every later change that reaches a necessary result
  brings it up to date, so demanding a root again costs nothing.
- **An unnecessary result is not computed.** A result is computed when it
  is first demanded, by running its query, which demands its dependencies in
  turn.
- **A driver can observe a result without making it a root.** A read
  through `Engine.observer` computes the result if the state has none, and
  the result is collected again unless something else makes it necessary.
  Comparing two states, and finding a definition by name, observe: a
  question about a state does not change the results it maintains.
- **A read made outside any query first brings the engine up to date
  through the phase of its target,** so a driver never sees a result that
  a change has not reached yet. Later phases keep their queued results
  until something of theirs is read, or the state is written.
- **A result whose query raised a fatal exception,** such as a stack
  overflow, stays queued, so it is computed again and never written as
  current.
- **Results are recomputed, never patched.** A query is a function of its
  reads, so computing it again from the same reads gives the same value.
  The engine needs no knowledge of a query's semantics.

Jane Street's Incremental pushes changes in the order of each node's height
in the graph, and stops where a value is unchanged. Truss's phases are that
order, fixed by the compiler's structure and not computed for each node:
a query cannot come to read something above it, so heights never have to be
maintained, and a query never has to be stopped and started again. Within a
phase the engine marks the way Adapton does, and brings each marked result
up to date when it is needed. A build system that marks everything a change
can reach, as Bazel's Skyframe does, spends time on everything that could be
affected; one that checks each result's inputs when it is asked for, as
Salsa and Rust's incremental compiler do, spends time on everything that is
asked for.

### Bases

An engine holds its differences from its *bases*, which are frozen engines: an
input it sets, a result it computes, and a copy of each base result that a
change reached. Everything else it reads from the bases.

So a state costs only its changes. Ten worktrees of one project cost one
project and ten changes, starting a state costs nothing, and comparing two
states costs their differences, since everything neither holds is the same
in both. This turns fast inference into throughput: trying a change
is the basic thing an agent does, many agents try many changes at once, and
each trial is a state, cheap to start and independent of the others.
Roslyn's snapshots of a solution, Buck2's versioned graph, and git's trees
share structure between versions in the same way.

- **A base never changes.** Freezing an engine brings it up to date and
  makes it a base. Several engines over one base share it.
- **A base's result is copied when a change reaches it.** Setting an input a
  base holds gives the engine its own input in its place, and the base input's
  readers are copied into the engine, where it is marked and brought up
  to date like any result. The copy holds the same result and has the
  base result's dependencies, as the engine sees each.
- **A copy that comes out the same is the last one copied.** Only when a
  copy's result differs from the base's are the base's readers of it copied
  in turn. So an engine holds only the results its changes really reached.
- **A base is fixed, or an earlier state.** A fixed base holds a package
  whose sources never change, such as the standard library, and no engine
  replaces its inputs. Any other base is the state the engine started from.
- **An engine that nothing refers to is freed,** with everything it holds:
  each engine owns its nodes, and nothing else keeps them.

### Collecting unnecessary results

A result of the engine's own that is unnecessary is *collected*: removed
from the state, with each result that only it read. Collection waits until
no query is running, since a running query has read results that do not
yet count it as a reader. Three kinds of node are never collected:

- a root, until `Engine.unroot` makes it no longer one, as the database
  does for the diagnostics of a module that is removed
- an input that is set
- a copy of a base's result, since the base's readers may read it; copies
  go when the state is next written whole

So once a state is brought up to date, every result it holds is current. A
result that a change reached is brought up to date if it is necessary, and
collected otherwise, never left as it was: a state written with such a
result in it would be opened with that result taken for current.

A root in a base is copied into the engine when a driver demands it, so
that being a root is part of the engine's own state, and is written with
it.

### Cycles

A query that asks, directly or not, for its own result raises `Cycle` with
the queries on the cycle. Every query on the cycle has the cycle as its
result, whether or not it caught it, and so does every query that reads a
result that is a cycle, so that a result never depends on which query met
the cycle first. The reading that closed the cycle is an edge too, so that
removing the cycle reaches every query on it. TYPECHECKER.md designs the
stages so that ordinary code makes no cycle: constants that refer to each
other, the one real case, are found by the constant's own evaluation, which
keeps the constants on its way.

### Query declarations

A stage declares each query with its name, the types of its key and its
value, and the function that computes it, and says:

- **Its phase.** A query that left it out would not compile.
- **Whether its results' bytes are stored,** which makes each a fact that
  other states find. See [Which results are stored](#which-results-are-stored).
- **Whether a state that never held the result looks for it too.** See
  [Facts](#facts).
- **Its subject:** a definition and a part of it, such as the interface
  or the body of `app::main::double`. Graph questions are asked and answered
  by definition, and a result about no definition, such as a lookup by name,
  is passed through when answering them.

A query is declared when its module is initialized. A state that is opened
leaves out each result of a query that is not declared, with everything
that read it, since it could not be checked; so a query declared later, as
one inside a lazy value is until the value is first forced, would have its
readers computed again in every process. Once the database has opened its
store, declaring a query is an error.

Nothing a stage can call changes an input or names a session.

### Query requirements

The engine relies on these, and its tests and its audit check them:

- **A query is a pure function of the reads it makes through its context.** It
  reads no global state, no files, no clock, and no other session. Once the
  compiler is written in Truss, this is checked by the language: a query
  whose only capability is reading the database can do nothing else.
- **Its value is canonical:** no fresh numbering, no hash-table order, no
  timestamps. Early cutoff and
  fingerprints compare values, so an unstable value would defeat both.
- **Its value holds no functions,** unless the query gives its own equality.
  A value that holds a function has no bytes, so it is *opaque*: its
  fingerprint is a nonce, equal to no other computation's. It is never a
  fact, and its readers are computed again whenever it is.
- **It answers for any key.** A query may be asked for a result that nothing
  will read once the state is up to date, so it must give an answer, such as
  `None`, for a key that no longer names anything.
- **An exception is an outcome.** A query that raises keeps its exception
  like a value, so its readers see the same exception until something it read
  changes. An exception's fingerprint is the hash of its constructor's name
  and its arguments, so a result that raises as it did before stops a change
  like any result that comes out the same. Its bytes are never stored: a
  state opened later holds the fingerprint, and computes the result again
  when something needs the exception itself. Absence is better told with an
  option, and the stages do so.

## Inputs

An input is a file's text, and little else. A project's packages, the
module of each file, and the errors between its manifests are not
inputs: they are queries over the files, in `Project`, of the first phase.

| Input | Key | Value |
|---|---|---|
| A file's text | Its root and its path in it | The text |
| A root's files | The root | The paths of its manifests, lock file, and module files |
| The roots | The session | The roots whose packages are in the build without being selected: the project's and the standard library's |
| A file's stamp | Its path from the project's root | The evidence that the file has not changed: for a file on disk, its size, modification time, and inode; for a commit's or a trial's, the hash of its text |
| An unavailable package | The hash of its files | Why a registry package's files could not be had |
| The wanted keys | How instances are lowered | The tests and programs whose keys a driver is about to demand |
| A solver answer | A request's key | The answer |

A *root* is a tree of files: the project being worked on, the standard
library, or a registry package's files. The last two inputs are stages': a
stage declares an input, and a driver sets it through its session.

| Query | Result |
|---|---|
| `Project.layout`, of a root | The root's packages, each module file's module, and the errors in a manifest by itself |
| `Project.selection` | The registry packages of the build, those whose files are not inputs yet, the errors in the lock file, and the lock file the manifests give |
| `Project.build` | Where each package of the build is: its root and directory |
| `Project.package`, of a name | A package's dependencies, grants, `usize_bits`, and modules |
| `Project.module_text`, of a module | The text of the module's file |
| `Project.problems` | The errors in the project's manifests and lock file |

- **The stages read a package and a module's text as queries.** A stage
  cannot tell a project's package from a registry package or the standard
  library.
- **An edit to a module's text changes one input,** and no query of the
  project reads it but that module's text. A manifest that renames a
  package changes the layout, and each module's text is found under its new
  path with no file read again.
- **Nothing is derived by hand.** The database sets a file's text when its
  stamp changed and removes it when the file is gone. It keeps no list of
  packages or modules of its own, so there is none to bring in line.
- **Lexing and parsing are queries:** a file is lexed and split again when
  its text changes, and a definition whose tree comes out the same, as one
  that only moved does, changes nothing that read it.

## Fingerprints and facts

A query is a pure function of its reads, so its result is a *fact*: the
value, together with each dependency and its value at the time. A fact is kept by
content, not by place, so a state that reads the same finds it, whichever
worktree, branch, or process computed it. Bazel and Nix keep build steps
this way, and Unison keeps definitions this way; Truss keeps every saved
result of the compiler this way, so nothing is computed twice. The graph a
state holds says which facts are that state's. It is an index, which can be
rebuilt from the facts and the files.

### Fingerprints

A node's *fingerprint* is the BLAKE3 hash of its value's bytes. An input
that is set has one, and so has every result: a value's is the hash of its
bytes, an exception's the hash of its name and arguments, and an opaque
outcome's a nonce. An input that is not set has none, and is told apart
from one that is.

- **Every hash is BLAKE3,** written in stage0 from the specification and
  tested against the official test vectors, since `digestif`, the OCaml
  library at hand, has BLAKE2 and not BLAKE3.
- **Content is hashed in the default mode, and keys in the derive-key
  mode.** A value, a file's text, or an executable is named by its plain
  hash. A key made of fields writes them as a deterministic CBOR array and
  hashes that under a context, a constant string that names the kind of
  key, such as `truss 2026-11-12 store result`. CBOR prefixes every field
  with its length, so two lists of fields never share an encoding. The
  mode's flags make every key of one context disjoint from every plain hash
  and from every key of another context, so a value whose bytes spell a
  key's input is never read as that key's result. A changed key format
  takes a new context, and keys of the old format stop matching instead of
  being misread.
- **A fingerprint is computed when it is first needed:** when the state is
  written, or when a result that read the node is looked for as a fact.
- **A result that was not read back is compared by fingerprint.** A state
  opened from the store holds fingerprints, and reads a value only when
  something asks for it. A result computed again there is compared with the
  fingerprint it had, so nothing is read from the store only to be compared.
- **A value's bytes depend only on the value.** Stage0
  makes them with OCaml's marshaling, written without sharing. Marshaling
  otherwise records which parts of a value are one block in memory, and that
  differs between a value computed from results in memory and the same value
  computed from results read back from the store, each of which is read as
  blocks of its own. Bytes that differed so would give one value two
  fingerprints: a result computed again in a new process would look changed,
  and a fact would not be found by the state that needs it.
- **The bytes mean something only to the compiler that made them.** Writing
  an encoder for each of the stages' result types would cost thousands of
  lines that every change to a stage would have to keep up. Two equal values
  can still marshal differently where a value's form depends on how it was
  built, as a balanced tree's does, and the only cost is that a fact is not
  found. The compiler written in Truss will derive a canonical encoding for
  every result type, as it derives `Hash`.

### Facts

A saved result is kept as a *fact*: its fingerprint, under a key made of

- the computation's author, which in stage0 is the compiler's identity, the BLAKE3
  hash of its executable
- the query's name and the result's key
- each node the result read, in the order they were first read, with its
  fingerprint

A result that raised, or that is opaque, is no fact: there is no value to
give for it. A result that read an opaque result is none either, since that
read's fingerprint will not be met again.

- **A fact found is the result.** It was computed from reads with exactly
  these fingerprints, and a query is a function of its reads, so
  computing it now would make the same reads, in the same order, and give
  the same value. This holds whichever state the list of reads came from.
- **A marked result is looked for as a fact before it is computed.** Its
  dependencies from last time are brought up to date, and the key of those reads with the
  fingerprints they have now is looked up. This makes going back
  free: a branch switched away from and back to, an edit that is undone, or
  a commit another worktree already checked finds each result done.
- **A result the state never held is looked for too, where its query is
  portable.** A state has no list of reads for a result it never held. So
  for a portable query the store keeps, once for each key, the names of the
  result's dependencies when it was first computed anywhere, and a new result is
  looked for under those reads, each brought up to date first. This is how a
  state that reaches an instance of the standard library, or a test's key,
  finds the results another state computed, without a state of its own to start
  from. Code generation's queries are portable: an instance's LIR, a pulled
  method's version, an instance's own hash and its references, its group,
  its key, and a test's key. A type checker's result is found through the
  state its worktree starts from, so its reads are not kept a second time.
- **Facts are kept when a state is written,** and by `Engine.record`.
- **A result whose bytes are not kept is no fact,** since there would be no
  value to give. It is cheap to compute, which is why its bytes are not
  kept.

The key holds the compiler's identity because stage0 has one version for the
whole compiler. DESIGN.md asks that each stage be versioned on its own, so
that a release that changes code generation keeps every fact about types.
Once the compiler is written in Truss, a stage's version can be the key of
everything its own code can reach, which the database computes like any
other key, so that a change to the compiler leaves exactly the facts its
changed code could not have made.

### Which results are stored

A stage marks a query as saved where reading its result back is cheaper than
computing it: each lookup's result, each definition's tree, resolved form,
interface, and checked body, each stage's diagnostics, and each instance's
code generation output, with its keys.

An unsaved result is cheap to compute again from the saved ones: a file's tokens and
trees, the indexes over a package's declarations, and a definition's text.
These are part of a state like any result, with their fingerprints and
dependencies, so a change stops at them in a state opened from the store as it
does in a live one. Only their values are missing, and are computed again
where something needs them. A value computed again has the fingerprint it
had, so nothing that read it is touched; were one ever to come back
different, everything that read it would be checked again.

## States in the store

### Artifacts

A state is written as an *artifact*, which is a value in the store, named by
its hash like any other:

- **A whole state** holds every node the state's roots and set inputs
  reach, apart from those of its fixed bases: each node's name and key, its
  fingerprint, its dependencies, as places in a table of names, and whether it
  is a root.
- **A difference** names an earlier artifact and holds the engine's own
  nodes that changed since: the nodes it computed, found as facts, or
  set, those that became or stopped being roots, and the names of those it
  collected.

An artifact never changes, so one names a state for good, and many states
can be differences over one artifact.

- **Writing costs O(change).** `Engine.write` writes a difference over the
  artifact the engine was opened from or last wrote. The first write of an
  engine that was opened from none writes the whole state.
- **A copy that came out as the base's result, reading the same, is not
  written,** since the base holds it. If an earlier difference of the chain
  holds another result for it, it is written, to take that one's place.
- **A node is written with the first node that reads it.** A node that is
  written must find its dependencies when the state is opened, so a node the
  chain does not hold yet goes with its first reader.
- **Values are flushed before a pointer names an artifact,** so a pointer
  never names a value that a crash lost.

### Opening a state

`Engine.open_` follows an artifact's chain back to the whole state it starts
from:

- **The whole state is a frozen base,** made once and shared by every engine
  opened from it, in one process. It is held weakly, so one no engine uses
  is freed.
- **The differences after it are the engine's own.** Each node is the last
  the chain holds for its name and key. A node a difference collected keeps
  its place, with nothing in it, where the whole state holds it too, so that
  the whole state's result, which is of an earlier state, is never read in
  its stead.
- **Values are read when first needed.** Opening reads the artifacts and no
  value.
- **An input whose value the store lost is an error, not an input that is
  not set.** A result can be computed again and an input cannot, so reading
  one whose bytes are gone, as after another process collected the store,
  raises `Engine.Lost`, which is never a query's outcome. The database then
  discards every open state with its pointer and runs the command once
  more, from the files. A state to start a new worktree from, and the
  standard library's, are used only if the store has every input's value.
- **A node that cannot be checked is left out:** a node of a query this compiler
  does not declare, a node that read a node that cannot be found, and
  everything that read those.

So two worktrees opened from one artifact share everything, and each holds
only its changes.

### Folding

A chain of differences is folded into one whole state when its differences
hold more than half as many nodes as the whole state, and more than 256. The
state is written whole, without the nodes its roots no longer reach, and
the session is opened again from it. So the nodes a session holds itself,
and the data read to open a state, stay within a constant of the changes,
and the total written stays a constant multiple of the changes.

Folding costs the state's size, so no command should wait for it:

- **The background process folds a session while no request is waiting.**
  A first test run adds much to a state that only a check made, and the
  command after it finds the session as it left it.
- **A command waits for a fold only when the differences have grown to
  twice the whole state,** which happens only if requests never leave the
  process a second to itself.
- **A command run in its own process folds as it opens the state,** which
  costs it the state's size already.

### Package artifacts

A package whose sources never change is checked once, written whole, and
found from then on by the key of its sources. It is a fixed base under every
state that uses it.

- **The standard library is one.** It is built into the compiler, so its key
  is the compiler's identity. The first process to need it checks every
  module, writes the state, and keeps the artifact's name under that key;
  every later process opens it with one lookup and reads no value until it
  needs one.
- **A package being worked on is part of its worktree's state,** which is a
  base and a difference like any state.

### The standard library's own state

Work on the standard library edits the sources of a fixed base, and the
library is built into the compiler, so each edit makes a new compiler
identity, under which no kept fact is found. `Database.open_library` opens
the library as a state of its own instead:

- **The `standard` package is the engine's own inputs,** over no base, set
  from the sources built into the compiler. The text of a module that is
  gone from the sources is removed.
- **Its facts are kept under the compiler's version,** not its identity. The
  version is a digest of the compiler's source and of its build
  toolchain: the OCaml compiler, the build profile, the target, and the linked
  libraries. Tests, tools, and the library's text are left out. So an edit
  to the library keeps the version, and the state recomputes only the
  edit's dependents; a change to the compiler gives a new version.
- **The state is opened from a pointer the caller names,** so each caller,
  such as each share of the library's proofs, keeps a state of its own.
- **It is folded when it is opened,** as a command run in its own process
  folds a session.

A user's session does not use this: there the library never changes, and is
a fixed base.

## The store

The store lives in `$TRUSS_CACHE`, else `$XDG_CACHE_HOME/truss`, else
`~/.cache/truss`, and is shared by every project, worktree, and compiler on
the machine. It holds:

| Kind | Named by | Where |
|---|---|---|
| Values, artifacts among them | The BLAKE3 hash of their bytes | `segments/` |
| Facts, and each result's first dependencies | Their kind and key, hashed as a store result | `segments/` |
| Results of expensive steps | Their kind and exactly the input that made them, hashed as a store result (see [Exact keys](#exact-keys)) | `segments/` |
| A package's artifact | The key of its sources | `segments/` |
| Object files | Their key, as CODEGEN.md describes | `objects/`, one file each, since a linker reads them by path |
| A registry package's files | The hash of the files, as PACKAGES.md's "The lock file" defines it | `packages/`, one directory each |
| A solver's answers | Their key, as PROVER.md describes | `proofs/`, one file each |
| Pointers | A worktree's session, or a named state of the standard library | `pointers/` |
| The compiler's identity, the list of worktrees, and the background process's lock and log | | the top, and `servers/` |

Everything but a pointer is named by its content or by its inputs, and
never changes.

### Segments

Values and results live in append-only segment files, as Bitcask stores
them, with sorted indexes like git's pack files:

- **A record** is a kind byte, a 32-byte key, the value's length, the value,
  and an 8-byte FNV-1a checksum of the rest. Every key has the same width: a
  value's is the hash of its bytes, and a result's is derived from its
  kind and key under the store result's context.
- **Each process that writes has a segment of its own,** locked while it
  writes, so writers never share a file and need no lock to write. A value
  two processes both add is in both segments, which is harmless, since its
  name is its hash.
- **Records are gathered and written together,** a megabyte at a time, and
  whenever the store is flushed, so that adding a record is not a system
  call. A record that is not written yet is read from memory.
- **A segment is sealed** at 64 MB, and when its process ends or closes the
  store, with an index beside it: its keys sorted, each with its record's
  offset and length, in fixed-width entries. The index is read into memory as
  one string and searched by halving, which takes about 44 bytes for each
  value and no allocation per entry. A process that is killed leaves its
  segment unsealed, without the records it had not written, and such a
  segment is read by scanning it.
- **A lookup that misses looks again** for segments that other processes
  made or grew since, before saying the store has nothing, but not more
  often than every twenty milliseconds: a first check misses on every
  result, and a result another process added a moment ago is only computed
  again. A read that must see another process's latest write, such as a
  worktree's state, looks first.
- **A damaged or cut-off record is missing.** Every read checks the
  checksum, and that the record is the key's own, so a crash or a damaged
  file or index costs a recomputation, never a wrong answer.
- **Small segments are gathered into one.** Every process that writes
  leaves a segment, and a lookup searches each segment's index. Once many
  small segments that no running process is writing have gathered, a
  process that opens the store, and the background process each minute,
  copies their records into its own segment and deletes them.
- **A process holds only so many segments open,** and closes them all past
  that, to open each again when it is next read.
- **The store is written with ordinary file operations:** create, append,
  read, rename, flush to disk, and delete, and a file lock on a writer's own
  segment. Truss has no foreign code, so the compiler written in Truss cannot
  use SQLite or LMDB. A store it can rewrite with the standard library's file
  capabilities keeps the two compilers' stores alike.

One file per value would not do: a project of a hundred thousand
definitions keeps millions of small values, and a file system spends far
more on a file's inode, directory entry, and block than such a value takes,
and far more time creating and opening files than reading one segment.

### Pointers

A pointer is the one thing in the store that is replaced: a few bytes under
a name, such as the name of a worktree's current artifact.

- **It is written beside itself and renamed into place,** after every value
  it may name is flushed, and is framed with its length and a checksum, so a
  pointer cut short reads as nothing.
- **A session's pointer holds text:** the version that wrote the
  state, its artifact's name, and each file's fingerprint. Any compiler can
  read any pointer, so collection reads them all, and keeps the states of
  the versions it can read.
- **A pointer has one writer,** which holds its lock. A session's pointer is
  named by the compiler's identity and its worktree, so a new compiler
  starts from the files, and still finds every result whose key it computes
  the same way.

### Garbage collection

The store is a cache, and the background process keeps it within a size
budget, 20 GiB unless `TRUSS_CACHE_SIZE` gives one in bytes. Every ten
minutes it checks, and when the segments take more:

- **A live state's artifacts are kept:** the artifacts of its chain, and every
  value they name. A worktree's state is live while its directory exists.
  The pointer of a worktree whose directory is gone is removed every
  minute, whatever the store's size, since a new worktree looks through
  every pointer for the state nearest to it.
- **Only this compiler's states are read.** An artifact's bytes mean
  something only to the version that wrote them, and start with that
  version, so another's is not read. A pointer names its state's version,
  which says which states those are. The values of another compiler's
  states are therefore not kept. That compiler finds its state gone, or an
  input's value lost, and starts from its files. The standard
  library's artifact is kept, and so is each named state of the library.
- **Results are kept while in use:** those this process read or added, and
  those in segments written in the last week.
- **Survivors are copied into a new segment, and the old ones deleted.**
  Segments another running process is still writing are left alone, which the
  lock on each tells.

## Exact keys

The most expensive work in a build is outside the compiler's own queries:
compiling C, running tests, running the solver, and running code while
compiling. Each of these is a pure function of an input that the compiler
can write out completely, so its result is a fact kept under the hash of
that input:

| Result | Key | Kept |
|---|---|---|
| A test's outcome | The key of everything the test can reach, as CODEGEN.md's "Test results" describes, the code generator's version, and the target's widths | A pass with nothing to show |
| An object file | The C text, the C compiler's identity, and its flags | The object |
| A solver's answer | The query's text, with every name numbered, and the solver's identity and options, as PROVER.md's "Queries" describes | The answer |
| A tagged template's check | The key of the code that ran, as CODEGEN.md's "Code run while compiling" describes | Whether each clause holds |

- **These keys are exact.** Everything the result depends on is in the key,
  so a result can be reused by any session, on any branch, by any compiler
  that makes the same key. That is how renaming a definition, or moving it
  to another module, finds its test results already done.
- **The target is in a test's key** because `USize` is a `typedef` in the
  generated C, so the LIR is the same for 32-bit and 64-bit targets while
  results such as `USize.maximum` differ. Code for one operating system lives
  only in the standard library, so a difference between systems is already
  in the LIR.
- **Only a pass with nothing to show is kept.** A failure's message, an
  `echo`, and a panic give positions, which the key leaves out, so such a
  test runs again. One that ran out of time, ran out of memory, or
  overflowed its stack depends on the machine, its stack size, and the C
  compiler's optimizations, none of which are in the key, so it is reported
  and never kept. A run with sanitizers keeps nothing.

## Sessions

A *session* is one project's state, in one worktree, with the context a command
needs: its engine, the pointer that names its state in the store,
and the problems its manifests have. A project is as PACKAGES.md's
"Projects" defines it: the directory tree under a manifest with a `[project]`
table, or a single package with no such manifest above it. A session is a
project's, and not a worktree's, because a state names every definition by
its path, and a path means one thing only within one project: two projects
in one repository may each have a package called `tools`.

- **The project's root is found from the files alone:** the nearest
  directory at or above a command's whose manifest has a `[project]` table,
  or with none, the nearest with a manifest. Git is asked nothing, so a
  project builds the same from an archive.
- **Its packages are the directories under the root with a manifest that
  has a `[package]` table,** apart from another project's: under a root with
  a `[project]` table, a directory whose manifest has one of its own, with
  everything below it, and under a root without one, every other directory
  with a manifest. Each module file belongs to the nearest package above
  it. Directories whose names start with `.`, and `_build` and
  `node_modules`, are passed over.
- **A dependency is the project's package of that name.** An error
  between manifests, such as a dependency that names no package or a cycle
  of packages, is a problem of the session, which CLI.md lists.
- **The same project in two worktrees is two sessions,** which are compared
  for overlaps (see [Parallel work](#parallel-work)). They are told to be
  the same project by being at the same place under worktrees of one
  repository.

### Registry packages

A session's build is its project's packages and the registry packages they
use, at the versions PACKAGES.md's "The lock file" and "Choosing
versions" give. Which those are is a query, `Project.selection`, over the
lock file and the records of the packages it names. The database never
chooses a version itself.

- **A registry package's files are in the store,** in `packages/`, a
  directory named by the hash of the files, as [The store](#the-store)
  lists. One that is not there is fetched from the registry, and kept only
  if it has that hash.
- **A registry package's files are inputs of a root of their own,** named
  by their hash. The selection names each package it needs whose files are
  not inputs yet; the database fetches those and sets them, which reaches
  the selection, and asks again, since a package's record can name more.
  They are set once, since they never change, and removed when the build no
  longer selects the package.
- **A registry package is a package like any other to the stages.** Its
  results are computed when something reads them, so a project pays only for
  the parts of a package it uses.
- **A project's package of the same name takes its place,** as PACKAGES.md's
  "Projects" decides: the name is then the project's package, and no line
  of the lock file is for it.
- **Each error is a problem of the session:** a lock file that cannot be
  read, a dependency no lock file or record gives a version, files that
  cannot be had, and a lock file that is not the one the manifests give,
  with that one, which `truss check --fix` writes.
- **Other versions are tried in a trial** (see [Trials](#trials)): a
  session that starts from the project's and has another lock file, which
  `truss upgrade` compares with the project's before it writes the file.
- **A published version can be had in an engine of its own,** over the
  standard library, with the packages it was published with. A package and
  the version before it have the same paths, so the two cannot be in one
  state. `truss publish` compares a package with its last version this way.

### The background process

Each project has a background process of its own, for each compiler, as
each workspace has a Bazel server of its own. A command's client asks the
process of the project its directory is in, which `-C` can name; the first
command starts it, detached from the terminal, with its output in
`servers/server.log`. It exits after three hours without a request, when
its project's directory is gone, or within a minute of its compiler being
built again, since the new compiler's clients start processes of their own.

- **Commands in different projects are answered at once,** and so are
  commands in different worktrees of one project, since each worktree's
  copy of the project has a process of its own. This lets many
  agents, each in a worktree, work at the same time: none waits for
  another's test run. Commands in one worktree are answered one at a time.
- **The processes share the store, and nothing in memory.** Two worktrees
  whose states start from one whole state share its values on disk, and
  each process holds its own nodes for it. A process finds as facts the results
  another computed.
- **It holds nothing that is not in the store.** A session's results are
  written when its command is done. The process keeps its session's engine
  in memory so that the next command finds it there.
- **Clients connect through a Unix socket** in `servers/`, named by the
  compiler's identity and a hash of the project's root, with a file beside
  it that says the root, by which `truss status` and `truss stop` find
  every process. A socket's path has a limit of about 100 bytes, so a
  store with a long path puts the socket in `/tmp/truss-UID`, named by a
  hash of where it would have been. Both directories are the user's alone,
  and the one in `/tmp` is used only if it is: the data on the socket
  is marshaled, so another user who could put a socket there could run code
  as this one. A lock beside it in the store keeps to one process per
  project and compiler.
- **Without the background process,** as in CI, `--no-server` runs a
  command in its own process, against the same store. It takes the
  session's pointer lock first, so a pointer never has two writers, and it
  refuses, saying why, while the background process has that session open.
- **A process answers one request at a time.** Requests, progress, and
  answers travel as OCaml's marshaled values, which is safe because the socket is
  named by the compiler's identity, so both ends are the same program.
- **It runs its client's own code.** The request and the answer are the
  client's own types, and the handler the client gives may send progress,
  text to show while it works, which the client gets as it comes. The
  command line's handler runs the command line itself, so a command's answer
  is the same in the background process and in the command's own process.

### Watching files

- **A command scans its worktree before it is answered.** It compares each
  file's size, modification time, and inode with the stamps the state holds,
  and reads only the files that differ. So a command always sees every
  change made before it, with no need for the cookie files Watchman uses to
  make late file events safe.
- **A file's stamp is set only once its text is.** A file that cannot be
  read, such as one deleted since its directory was listed, is not there,
  and is read by the first scan that can. So a scan that fails part way
  leaves nothing that looks read and was not.
- **While no request is waiting, the process scans every open worktree each
  second,** and brings each state up to date, so diagnostics are current
  before anyone asks for them, and overlaps are found as work happens.
- **A scan that finds every file as it was sets nothing,** so no query of
  the project is computed again. A package that could not be fetched is
  tried again once in each process.
- **Scanning is O(files) in stamps.** FSEvents on macOS and inotify on Linux
  would make it O(change), but OCaml reaches them only through C bindings,
  which stage0 has none of yet. Since a command scans anyway, adding them
  changes only how soon the process hears of a change.

### Starting a session

- **A worktree whose pointer names a state** opens it, scans its files, sets
  the inputs that differ, and brings the state up to date. That costs
  O(files) to scan, reading the chain's artifacts, and O(change) for
  everything else.
- **A new worktree starts from the nearest saved state.** A pointer holds,
  with its artifact's name, the fingerprint of each of its worktree's
  files. The process fingerprints the new worktree's files and takes the
  state that differs from them in the fewest files. The new session opens
  that state's artifact, forgets its file stamps, sets the files that
  differ, and brings the state up to date. Its first write is a difference
  over the other worktree's artifact, so the two share everything but their
  differences, in the store and, in one process, in memory. An agent that
  creates a worktree from `main` gets a warm session at once, whether or not
  any process has `main`'s session open.
- **A worktree with no state near it** is checked from the files, over the
  standard library's artifact, and finds as a fact every result that any
  state computed from the same reads.
- **A state is first written when a command is done,** with the command's
  results, so that the first artifact is a whole state.
- **An idle session is written and dropped from memory** after an hour
  without requests, and opened again when next needed.

### Sessions for commits

A session can also be opened for a git commit, with the files under the
project's root read from git through `git ls-tree` and `git cat-file`. It starts from the nearest saved
state, as a new worktree does, and is kept in memory and never pointed at.
This is how the database gets the state of a base commit, compares a branch
that has no worktree, and checks a merge.

### Trials

`Database.trial` gives a session that starts from another's state, with
some of its files replaced, added, or removed: the session's state is
written, and opened again. The trial holds its files' changes and shares
the rest with the session, and is never saved. A rename checks its plan in
a trial before it writes a file, a merge is checked in one, whose files are
the merged tree's, and an upgrade is tried in one, whose lock file is the
new one.

## Questions

Tools can ask a session these questions. Every answer names definitions by
path and part, and files relative to the worktree's root, never nodes.

| Question | Asked by | Answer |
|---|---|---|
| A session and its diagnostics | `truss check` and every command that reads code | The session for a directory's worktree, current with its files; the packages the directory is about; each file's diagnostics; and the manifests that could not be read |
| Dependencies | `truss dependencies` | For each part of the given definitions, the parts of other definitions it read |
| Dependents | `truss references`, `truss impact`, `truss upgrade` | The parts of other definitions that read a part of the given definitions |
| Reachable definitions | `truss holes`, `truss build`, `truss run` | For each root, every definition it reaches through dependencies |
| Name meaning | `truss references`, `truss dependencies` | The definitions a name means: a full path, or the end of one |
| Changes since a commit | `truss impact` | A session at a commit, and every part a change between two sessions can reach, with whether it changed |
| Where two worktrees meet | `truss overlap`, `truss check` | Where two sessions' changes meet, and the diagnostics a merge of the two would have that neither has |
| A trial | `truss rename` | An engine to try a change in |
| Build storage | `truss test`, `truss run`, `truss build` | Where test results, object files, and programs to run are kept, in the store, and saying which tests' keys are wanted |
| The background process | `truss status`, `truss stop` | The background process's sessions, and ending it |

A result a command demands is a root from then on, and the command line
saves each session it opened when its command is done. A test runs only when
asked.

A question about the graph first checks every package of the sessions it
reads, so that every definition's results are there to read. A part of a
definition depends on a part of another when a node about the first reads
the node about the second, directly or through nodes about no definition,
such as lookups. The path does not continue through a node derived from
fixed bases alone, such as one of the standard library's own lookups, even
where the state holds a copy of it, so a definition does not depend on
everything those lookups read. `dependencies` follows reads from the
definition's nodes, and `dependents` follows readers from the target's
nodes, with the same rule.

### Comparing two states

`changes` compares one state with another. A state holds only its differences
from its bases, or possible ones, so where the two share a base, the nodes that can
differ are those either holds itself; a base that only one of them has is
compared whole. Each such node is found in the other state by its query and
key, computed there if the other has none, and compared by fingerprint, and
by value where fingerprints differ.

### Holes and shipping

A hole's type and the names in scope come from the definition's type checker
tables and resolution: name resolution records the names in
scope at each `todo` as it walks the definition, so there is one account of
scope, and the tables give their types. A hole blocks every
test and `main` that reaches its definition through the definitions'
reads.

## Parallel work

GOALS.md names sorting out conflicts with other agents as one of the things
that will dominate development time, and asks that agents can find exactly
where and how their work overlaps. Git sees only lines. The database sees
each change's effects, so it can find overlaps that merge without a
textual conflict and break once merged:

- Agent A changes `parse` to return a `Result`, and agent B, in another
  worktree, adds a call to `parse`. Git merges both cleanly, and the result
  does not compile.
- Agents A and B each add a method `find` to `List`, in different files.
- Agent A strengthens a type's invariant that agent B's new function relies
  on.

### Overlaps

For two worktrees, the database finds the merge base of their commits and
compares each worktree with it, as `impact` does: each node that differs
from the base's is that worktree's *change*. The two overlap where:

1. **Both changed one node.** This covers editing the same part of the same
   definition, even on different lines, and two additions that answer one
   lookup, such as the two `find` methods, which both change the members of
   `List` named `find`.
2. **One changed a node that depends on a node the other changed.** B's new
   `quadruple` has a body that reads the signature of `parse`, and A changed
   that signature, so the database says "this worktree's change to the body
   of `quadruple` reads the signature of `parse`, which the other changes".

Nodes are matched between sessions by query and key. Each overlap names the
definitions and parts on both sides, or the lookup, when no definition is
involved.

### When overlaps are found

- **As work happens.** A `check` lists where its worktree's changes meet
  those of every other worktree of the repository that a background process
  serves, in a section of its own. It tells the worktrees of one repository
  by their common git directory, and reads each other worktree through a
  snapshot: the state that worktree's process last saved, opened without
  its lock and brought up to date with the worktree's files. Overlaps are not diagnostics: nothing
  is wrong with either worktree's code, and every diagnostic in Truss is an
  error.
- **Against a branch,** `overlap --with BRANCH` compares with the branch's
  commit.
- **For an exact answer,** `overlap --merge` merges the two with
  `git merge-tree`, checks the result in a trial, and reports every
  diagnostic that is in the merge but in neither side. The rules above find
  where work meets; this finds whether it breaks. A worktree's uncommitted
  work goes into the merge through a commit made with an index of its own,
  so its files, index, and branches are untouched.

## Checking the engine

A database that returns a stale result is worse than none, and the ways an
engine can go wrong are too many to think of one at a time. So the engine
checks itself against the one thing that is certainly right: a new engine
with the same inputs.

- **The audit.** `Engine.audit` brings an engine up to date, then computes
  every result it holds in a new engine with the same inputs, and reports
  each that differs. With `~flat:true` the new engine has no bases and is
  given their inputs too, so the bases' results are checked as well. The new
  engine finds no facts, since a fact the engine recorded would only be its
  own result again. With `~before:PHASE` only the results of the phases
  before that one are computed again: the library's proof run audits the
  type checker's results, and not the proofs, which the state is there
  to save computing.
- **Every test audits.** The test harness audits every engine a test made,
  when the test ends. So each test of each stage also tests that the
  database kept every result current, and that the stage's queries are
  pure functions of their reads: a query that read something it did not go
  through its context for would come out different in the new engine.
- **Counts of work.** The engine counts the results it marks, finds current,
  computes, finds as facts, copies, and collects. Tests make the same edit in a
  package of four modules and in one of forty, and assert that the counts
  are equal: for a body, a local, a signature's layout, and a new
  definition. They compare counts, never times, so they are the same on
  every machine.
- **The fuzzer.** `stage0/tools/engine_fuzz` makes a random graph of
  queries with dynamic dependencies over a few inputs, and
  makes random steps: it sets and removes inputs, asks for and releases
  results, writes the state and opens it again, and opens a second engine
  from the same state. After each step it audits each engine against one
  with no bases. For a run that fails it prints the fewest of the run's
  steps that still fail. It is a tool, run by hand, and each problem it
  finds becomes a focused test.
- **Times.** `stage0/tools/database_timing` makes a package of a given size
  in a store of its own and times a first check, writing the state, opening
  it as a new process does, and three edits, each with the counts of
  results computed and found as facts. It is a tool, run by hand, for work the counts do not
  show, such as the work for each reader of a result. No document
  records its output.

## Not built

- **Sharing between machines.** The store is local. Its keys are made so
  that sharing can be added without changing any of them: a fact, a test's
  outcome, a proof, an object, and a package's artifact are each named by
  their inputs, on any machine. Sharing matters most where sessions are
  short: an agent in a fresh container, or CI, starts with no store, and
  without one must compute everything before it can find a single kept test
  or proof, since their keys are made from the compiler's own results. With
  a shared store it finds the nearest state and its facts, and does only the
  work its change needs.

  It is left out because of the claims a result makes. DESIGN.md lets reviewers
  trust proofs instead of reading them, so a forged "proven" or "passed" in
  a shared store would skip exactly the checks Truss exists to make, and an
  object file is code that will run. That is the supply-chain attack
  GOALS.md sets out to stop. So a result from another machine will be used
  only when it is signed by a key the user trusts, as Nix accepts
  substitutes only with `trusted-public-keys`. The registry's key is trusted
  unless a project says otherwise, as PACKAGES.md's "The registry" decides,
  for the results it computed of the packages it holds. Every result is a function of
  its key, so a signed result can also be checked by computing it again.
- **A specified encoding for values.** A fingerprint is the hash of
  marshaled bytes, which only the same compiler can make again. The compiler
  written in Truss will derive a canonical encoding for every result type.
- **Test results as facts with the code that ran.** A test's key covers
  everything its code can reach. Tests are deterministic, so a result also
  stays good while the code the test actually ran is unchanged, which is far
  less. Recording the code a test ran, as a query's reads are recorded, would run fewer
  tests after an edit.
- **Every deterministic outcome of a test kept.** A test that failed an
  `assert`, panicked, or reached a `todo` gives the same outcome on every
  machine, as one that passed does. Once the positions in a failure's
  message are recorded as an instance's number and a place within its
  definition, as CODEGEN.md's anchors are, a kept failure can be shown where
  the code is now.
- **A constant's value kept under an exact key.** Its key is to be the key
  of the code that ran, its input, and the target. Code generation runs a
  constant's evaluator in each run of the compiler.
- **A solver's answers in segments.** Each is a file of its own, which costs
  as much as [Segments](#segments) says a file for each small value costs.
- **A package being worked on as an artifact of its own,** keyed by its
  sources and the interfaces it reads of others, so that an unchanged
  package is found in one lookup from any worktree.
- **Registry packages as artifacts,** each keyed by the hash of the
  package's content and the keys of the packages it depends on, and each a
  fixed base under every state that uses it, as the standard library is.
  A registry package's files are inputs of each session that uses it. A
  second project that uses one finds as facts the results the first
  computed for it, and still holds its own nodes for them.
- **Collecting registry packages.** A package's files stay in the store
  when no lock file names them any more.
- **Artifacts read in part.** A whole state is one value, read whole to open
  the state, so the first command of a new process costs the state's size:
  every node is made before one is asked for. In the background process that
  is paid once for each whole state. A state that reads only the parts it
  touches would open in the time its change needs, however large the
  project.
- **Indexes read in part.** Each index is read whole when a process opens
  the store. Reading an index a block at a time, and merging segments by
  size as a log-structured store does, would keep a lookup within the
  logarithm of the store's size.
- **Collection without the background process.** Only the background
  process keeps the store within its budget, so a store used only with
  `--no-server`, as in CI, grows until it is deleted.
- **Each stage's version in keys,** in place of the compiler's identity.
- **Merging at the level of definitions.** Two worktrees are merged by git,
  line by line, and the merge is then checked. Truss has no comments, one
  format, and no meaning in the order of definitions, so the database could
  merge definition by definition and leave to an agent only the changes that
  really meet.
- **Watching files with FSEvents and inotify,** in place of scanning stamps
  each second.
- **Answering several requests about one worktree at once.** A project's
  background process answers one request at a time, and a test run holds it
  until the run ends. A second command in the same worktree waits.
- **Sharing a whole state in memory between worktrees.** Each background
  process loads the whole state its session starts from. With one process
  for every worktree, ten worktrees of a project held one copy in memory;
  now they hold ten, and share only the store.
- **Unrooting every stale root.** The diagnostics of a module that is
  removed stop being a root. Other roots stay until a driver unroots them:
  the key of a test that was deleted is still a root, and is still
  maintained.
- **A fingerprint summary written in O(change).** A pointer holds every
  file's fingerprint, and is written whole when any file changed.
- **The rules that span a package as many results.** A package's checks are
  one result that reads every module's declarations, every `impl`, and every
  generic body of the package, so it is computed again when a definition is
  added or removed and when any of those changes, and its cost follows the
  package. Splitting it into a result for each definition and one for each
  lookup would make it follow the change.
- **Questions answered from an index.** A graph question scans every node
  of the state to find the nodes about its definitions, which costs the
  state's size each time it is asked. An index from each definition to its
  nodes, kept current like any result, would answer in the size of the
  answer.
- **Running affected tests unasked** is not decided. Test keys stay current
  once a test run has asked for them, so the background process could run
  the tests whose keys changed while the machine is idle, and have their
  results ready before `test` is asked. Whether that is worth the CPU when
  several agents share a machine is open.
