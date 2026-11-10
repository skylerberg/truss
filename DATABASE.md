# Truss Code Database

This document designs the code database: the part of the toolchain that
holds every definition being worked on and everything computed from them,
keeps those results current as files change, keeps what was computed so
that no state computes it twice, and answers questions about what depends
on what. It follows the decisions in [DESIGN.md](DESIGN.md) and
[GOALS.md](GOALS.md), and serves the stages described in
[TYPECHECKER.md](TYPECHECKER.md) and [CODEGEN.md](CODEGEN.md).

It is built in [`stage0/`](stage0): the engine in `incremental`, with its
two views `query` and `engine`, the store in `store`, sessions and the
questions they answer in `database`, and what tools ask of one definition in
`inspect`. The `truss` command line, in `cli`, is the database's client, and
the only program the database serves: the database is a library, and every
command and report is the command line's. What is not built yet is said
where it comes up, and listed at the end.

## What the database does

GOALS.md asks that a change cost O(change), not O(project), for building,
testing, and verifying, and that agents can see exactly what their changes
affect and where their work overlaps with other agents'. The database is what
makes both possible. It:

- holds the inputs of every worktree being worked on: the packages, their
  manifests, and the text of every module
- keeps the results that have been asked for current as inputs change, by
  pushing each change, one phase of the compiler at a time, to the results
  that read what really changed
- gives every result a fingerprint, and keeps each saved result as a fact
  under the key of what it read, so that another worktree, a commit, a
  branch gone back to, or a new process finds it instead of computing it
- writes each state as a difference over an earlier one, and opens a state
  by sharing the whole state it started from, so that a worktree, a commit,
  or a trial of a change costs what it changed
- keeps the results of expensive steps, such as a test run or a C compile,
  under a key built from exactly the input each one consumed
- answers questions about dependencies in terms of definitions: what reads
  a definition, what a change affected, what each `todo` blocks, and where
  two worktrees' changes overlap
- runs as one background process per user and compiler, serving every
  worktree and every command

It does not:

- decide what code means. The stages do, as queries the database runs.
- hold anything that cannot be rebuilt. Text files are the source of truth,
  as DESIGN.md says, so deleting the database loses only time.
- keep history. Version control does that. The database knows the state of
  each worktree now, and of the commits it was asked about.
- share results between machines yet. See
  [Sharing between machines](#sharing-between-machines).

## The model

Three ideas shape everything below.

### A fact is a result and what it read

A query is a pure function of what it reads, so its result is a *fact*: the
value, together with each thing it read and what that was. A compiler
query's result is a fact, and so are a test's outcome, a proof, and an
object file, whose "reads" are the whole input each consumed.

- **Every result has a fingerprint:** the hash of its value's bytes. Two
  results with one fingerprint are the same value, in any state and any
  process.
- **A fact is kept by content, not by place.** It is stored under a key made
  of the query, its key, and the fingerprint of each thing it read. A state
  that reads the same finds the fact, whichever worktree, branch, or process
  computed it. Bazel and Nix keep build steps this way, and Unison keeps
  definitions this way; Truss keeps every saved result of the compiler this
  way.
- **So nothing is computed twice.** The graph a state holds says which facts
  are that state's. It is an index, which can be rebuilt from the facts and
  the files.

### A state is a base and a difference

A *state* is one set of inputs and the results computed from them: a
worktree as it is now, a commit, a merge of two branches, or a change that
is only being tried.

- **A state holds only what differs from the state it started from.** The
  rest it reads from that state, which never changes and which every state
  started from it shares. So ten worktrees of one project cost one project
  and ten changes, in memory and in the store.
- **Starting a state costs nothing,** and comparing two states costs their
  differences, since everything neither holds is the same in both.
- **This is what turns fast inference into throughput.** Trying a change is
  the basic thing an agent does, and many agents try many changes at once.
  Each trial is a state, cheap to start and independent of the others.

Roslyn's snapshots of a solution, Buck2's versioned graph, and git's trees
share structure between versions in the same way.

### Three sizes

Results come in three sizes, and each has its own key:

| Size | Named by | Its key covers |
|---|---|---|
| A package | Its name | Its sources, and for a package whose sources never change, nothing else |
| A part of a definition | The definition's path and the part | What computing it read, each by fingerprint |
| An instance | The definition and its type arguments | Its own code, and the keys of the instances it refers to |

A key that is composed from the keys of smaller things answers "did anything
under here change?" in one comparison. That is how an unchanged package is
found whole, and how an edit changes the test keys of what can reach the
edited code and of nothing else.

## Structure

The database is three layers, each behind one narrow interface:

```text
 command line   language server   agent tools
        \              |              /
         ▼             ▼             ▼
   ┌──────────────────────────────────────┐
   │ Database: sessions, graph questions,  │  data, by definition and part
   │ overlap, the background process       │
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

| Interface | Library | Used by | What it offers |
|---|---|---|---|
| `Query` | `query` | Compiler stages | Declaring inputs and queries, and reading them while a query runs |
| `Engine` | `engine` | `Database` and tests | Setting inputs, keeping results current, bases, writing and opening states, and walking the graph |
| `Store` | `store` | `Engine`, and the exact-key caches in `Database` | Bytes by content hash, results by key, and pointers |
| `Database` | `database` | The command line, and the tools on it | Sessions of worktrees, and answers about them as data |

`Query` and `Engine` are two views of one implementation, `Incremental`,
which nothing else names. These rules keep each interface narrow, so that
each layer can be replaced without touching the others:

- **Stages see only `Query`.** A stage never sees the engine, the store, the
  file system, worktrees, git, or another session.
- **Only `Database` changes inputs,** and inputs are the only way anything
  outside the stages reaches them. A driver that compiles, such as a test
  run, reads results through a context the database gives it, as a query
  would, and asks the database to set what it needs set.
- **Answers name definitions, never engine nodes.** A graph question returns
  paths and parts, so a different engine can answer the same questions.
- **Each query's key and value types belong to the stage that declares
  them.** The database knows them only as values it can compare and save.
- **Code generation does not see the store.** A test run is handed functions
  that find and keep results by key, and the directory object files go in.
- **Clients see only sessions and answers.** Whether the session runs in the
  background process or in the client's own process makes no difference to
  them, since the background process runs the client's own code.

## The engine

### The graph

An engine is one state. Its graph has a *node* for each input and for each
query result, named by the input or query and its key. An *edge* runs from a
node to each node it read the last time it was computed, and the engine
keeps every edge in both directions:

- **Edges are learned, not declared.** A query reads through its context
  while it runs, and each read adds an edge. Truss's dependencies are not
  known before a query runs: a body depends on what its name lookups found,
  which depends on the names it uses.
- **A read that found nothing is an edge too.** Asking for the constants
  named `count` in a file, and finding none, depends on that answer. Adding
  such a constant later changes the answer, and so reaches the reader, as
  DESIGN.md requires for patterns.
- **The edges in from readers are what a change follows.** The edges out say
  what to check when a result may have changed, and answer "why does this
  depend on that?"

### Phases

Every query has a *phase*, and reads only queries of its own phase and of
earlier ones. Reading a later phase is an error, raised at the read. The
phases are the compiler's own order:

| Phase | What its queries compute |
|---|---|
| Syntax | A file's tokens and trees, the names it defines, its imports, and which modules exist |
| Declarations | What each file and package declares, a definition by name, a type's members by name, and each definition's tree |
| Resolution | What each name in a definition means |
| Interfaces | Signatures, shapes, constants' values, and the `impl`s found for a type |
| Bodies | Checked bodies, moves and loans, patterns, and what else is found in a body |
| Checks | The rules that span a package |
| Diagnostics | Every stage's diagnostics for a file |
| Lowering | What each instance compiles to |
| Linking | Each instance's own hash, and what it refers to |
| Recursion | Which instances reach each other |
| Keys | The key of everything an instance can reach |

Phases are what let a change stop exactly where it stops mattering. When a
phase is brought up to date, every earlier phase is final, so the engine
knows which of the phase's results read something that *really* changed,
and touches no others.

### Bringing a state up to date

A clock orders changes. Each change takes the next time, and each node
records when its result last changed and when it was last found current.
Setting an input to a value equal to its old one does nothing. Otherwise:

1. The input takes its new value, and what reads it is queued, each reader
   under its phase.
2. The engine takes the first phase with anything queued, and *marks* each
   queued result, and what reads those within the phase. Marking sets a
   flag and nothing more.
3. Each marked result is then brought up to date. What it read is brought
   up to date first, in the order it read them. If one of them changed after
   the result was last found current, the result is looked for as a fact
   and, failing that, computed again; the check stops at the first such
   read, since a later read may not be made at all once an earlier one gives
   a different answer. Otherwise the result is found current without being
   computed.
4. A result that comes out different queues what reads it in later phases.
   A result that comes out the same queues nothing. This is early cutoff.
5. The engine goes on to the next phase with anything queued, until none
   has.

So a change costs the results that read something that really changed, plus,
within one phase, what reads those. Editing a function's body computes its
tree, its resolved form, its interface, and its checked body again. The
interface comes out the same, so the callers' bodies, which are of a later
phase, are not marked at all, however many there are. The engine counts what
it marks, finds current, computes, finds as facts, and copies, and tests
compare those counts for the same edit in a small package and a large one
(see [Checking the engine](#checking-the-engine)).

- **A result that has been asked for is kept current.** Once a request asks
  for it, every later change that reaches it brings it up to date, so asking
  for it again costs nothing.
- **A result nobody has asked for is computed when first asked for,** by
  running its query, which asks for what it needs in turn. So nothing is
  computed that nobody wants.
- **A read made outside any query brings the engine up to date first,** so a
  driver never sees a result that a change has not reached yet.
- **Results are recomputed, never patched.** A query is a function of what
  it reads, so computing it again from the same reads gives the same value.
  The engine needs no knowledge of what a query does.

Jane Street's Incremental pushes changes in the order of each node's height
in the graph, and stops where a value is unchanged. Truss's phases are that
order, fixed by the compiler's structure and not worked out for each node:
a query cannot come to read something above it, so heights never have to be
maintained, and a query never has to be stopped and started again. Within a
phase the engine marks the way Adapton does, and brings each marked result
up to date when it is needed. A build system that marks everything a change
can reach, as Bazel's Skyframe does, spends time on everything that could be
affected; one that checks each result's inputs when it is asked for, as
Salsa and Rust's incremental compiler do, spends time on everything that is
asked for.

### Bases

An engine holds what differs from its *bases*, which are frozen engines: an
input it sets, a result it computes, and a copy of each base result that a
change reached. Everything else it reads from the bases.

- **A base never changes.** Freezing an engine brings it up to date and
  makes it a base. Several engines over one base share it.
- **A base's result is copied when a change reaches it.** Setting an input a
  base holds gives the engine its own input in its place, and what read the
  base's input is copied into the engine, where it is marked and brought up
  to date like any result. The copy holds the same result and reads what
  the base's result read, as the engine sees each.
- **A copy that comes out the same is the last one copied.** Only when a
  copy's result differs from the base's are the base's readers of it copied
  in turn. So an engine holds what its changes really reached.
- **A base is fixed, or an earlier state.** A fixed base holds a package
  whose sources never change, such as the standard library, and no engine
  replaces its inputs. Any other base is the state the engine started from.
- **An engine that nothing refers to is freed,** with everything it holds:
  each engine owns its nodes, and nothing else keeps them.

### Dropping

A result of the engine's own that nothing reads, and no request kept, is
dropped, but only once nothing is running: a query that is still running
has read results that do not yet count it as a reader. An input that is set
is never dropped, and neither is a copy of a base's result, since the base's
readers may read it; copies go when the state is next written whole.

So once a state is brought up to date, every result it holds is current. A
result that a change reached is brought up to date if something reads it or
a request kept it, and is dropped otherwise, never left as it was: a state
written with such a result in it would be opened with that result taken for
current.

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

### What a query must be

The engine relies on these, and its tests and its audit check them:

- **A query is a pure function of what it reads through its context.** It
  reads no global state, no files, no clock, and no other session. Once the
  compiler is written in Truss, this is checked by the language: a query
  whose only capability is reading the database can do nothing else.
- **Its value is canonical,** as DESIGN.md requires of every stored result:
  no fresh numbering, no hash-table order, no timestamps. Early cutoff and
  fingerprints compare values, so an unstable value would defeat both.
- **Its value holds no functions,** unless the query gives its own equality.
  A value that holds functions has no fingerprint, and is computed again
  where it is needed.
- **It answers for any key.** A query may be asked for a result that nothing
  will read once the state is up to date, so it must give an answer, such as
  `None`, for a key that no longer names anything.
- **An exception is an outcome.** A query that raises keeps its exception
  like a value, so its readers see the same exception until something it read
  changes. An exception has no fingerprint. Absence is better told with an
  option, and the stages do so, except for an input that is not set, which
  `Query.get` reports as `Not_found`.

## The interfaces

The signatures below are the built ones, shortened.

### `Query`, for compiler stages

```ocaml
type context
type subject = { path : Path.t; part : string option }
type phase = Syntax | Declarations | Resolution | Interfaces | Bodies | Checks
           | Diagnostics | Lowering | Linking | Recursion | Keys

val input :
  name:string -> show:('key -> string) -> ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) -> unit -> ('key, 'value) input

val query :
  name:string -> show:('key -> string) -> phase:phase -> ?saved:bool ->
  ?portable:bool -> ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (context -> 'key -> 'value) -> ('key, 'value) query

val get : context -> ('key, 'value) input -> 'key -> 'value
val find : context -> ('key, 'value) input -> 'key -> 'value option
val demand : context -> ('key, 'value) query -> 'key -> 'value

exception Cycle of string list
```

- **Every query says its phase.** A query that left it out would not
  compile.
- **`saved` says whether a result's bytes are kept.** Every result has a
  fingerprint and is part of a written state; a saved one's value is in the
  store too, and is a fact other states find. See
  [What keeps its bytes](#what-keeps-its-bytes).
- **`portable` says that a state which never held the result looks for it
  too.** See [Facts](#facts).
- **`about` connects a node to a definition and a part,** such as the
  `interface` or the `body` of `app::main::double`. Graph questions are asked
  and answered by definition. A node without a subject, such as a lookup by
  name, is passed through when answering them.
- **Nothing here changes an input or names a session.**

### `Engine`, for the database

```ocaml
type t
type node
type change = { computed : node list; changed : node list }

val create : ?log:bool -> ?bases:t list -> unit -> t
val freeze : ?fixed:bool -> t -> unit
val context : t -> Query.context
val set : t -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) Query.input -> 'key -> unit
val get : t -> ('key, 'value) Query.query -> 'key -> 'value
val release : t -> ('key, 'value) Query.query -> 'key -> unit
val stabilize : t -> change
val counters : t -> counters

val nodes : t -> node list
val differing : t -> node list
val unshared : t -> t -> node list
val identity : node -> string
val subject : node -> Query.subject option
val reads : t -> node -> node list
val readers : t -> node -> node list
val current_in : node -> t -> node option
val same_outcome : t -> node -> t -> node -> bool

val attach : t -> Store.t -> version:string -> unit
val record : t -> unit
val write : ?full:bool -> t -> string
val open_ : ?log:bool -> Store.t -> version:string -> bases:t list -> string -> t option
val open_base : Store.t -> version:string -> bases:t list -> string -> t option
val debt : t -> debt
val values_in : Store.t -> string -> string list

val audit : ?flat:bool -> t -> string list
```

`differing` gives the nodes an engine holds itself, and `unshared` those
that may differ from another engine's, which is how two states are compared.
`current_in` finds the same query and key in another engine and computes it
there if it has none.

### `Store`, for the engine and the caches

```ocaml
type t
val open_ : string -> t
val put : t -> string -> string
val get : t -> string -> string option
val refresh : t -> unit
val flush : t -> unit
val find_result : t -> kind:string -> key:string -> string option
val add_result : t -> kind:string -> key:string -> string -> unit
val files : t -> string -> string

type pointer
val pointer : t -> string -> pointer
val lock : pointer -> bool
val read : pointer -> string option
val point : pointer -> string -> unit

val collect : t -> budget:int -> live:(string -> bool) -> unit
```

### `Database`, for tools

`Database` gives tools sessions and answers questions about them with data:
a session's packages, files, and diagnostics, what reads what, how a
session compares with another, and where two worktrees' changes meet (see
[Questions](#questions)). It shows nothing and knows no command. The
command line, in [`stage0/cli/`](stage0/cli) as [CLI.md](CLI.md) describes,
is the one program that turns these into commands and reports, and the
language server is to be another client of the same interface.

`Database.serve` runs the background process with a handler the caller
gives, and `Database.call` sends it a request, starting it if it is not
running. The request and the answer are the caller's own types, and the
handler may send progress, text to show while it works, which the client
gets as it comes. The command line's handler runs the command line itself,
so a command's answer is the same in the background process and in the
command's own process.

## Inputs

A session's inputs are:

| Input | Key | Value |
|---|---|---|
| A package | Its name | Its manifest: dependencies, grants, and `usize_bits`, and its modules |
| A module's text | Its module path | The file's text |
| The layout | The session | Each package's directory and name, and every manifest and module file |
| A file's stamp | Its path in the worktree | Its size, modification time, and inode |
| A manifest's text | Its package's directory | The file's text |
| The wanted keys | How instances are lowered | The tests and programs whose keys have been asked for |

The layout, the stamps, and the manifests' texts are the database's own, so
that a restart reads only the files whose stamps changed. The wanted keys
are code generation's (see [Composed keys](#composed-keys)). A module's text
is set from the file system, or from git for a commit (see
[Sessions](#sessions)). Lexing and parsing are queries: a file is lexed and
split again when its text changes, and a definition whose tree comes out the
same, as one that only moved does, changes nothing that read it.

## Fingerprints and facts

### Fingerprints

A node's *fingerprint* is the BLAKE3 hash of its value's bytes. An input
that is set has one, and so has every result that is a value its bytes can
be made from. A result that raised, or whose value holds functions, has
none, and neither has an input that is not set, which is told apart from one
that is.

- **A fingerprint is worked out when it is first needed:** when the state is
  written, or when a result that read the node is looked for as a fact.
- **A result that was not read back is compared by fingerprint.** A state
  opened from the store holds fingerprints, and reads a value only when
  something asks for it. A result computed again there is compared with the
  fingerprint it had, so nothing is read from the store only to be compared.
- **A value's bytes follow from what the value is, and nothing else.** Stage0
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

- what computed it, which in stage0 is the compiler's identity, the BLAKE3
  hash of its executable
- the query's name and the result's key
- each node the result read, in the order they were first read, with its
  fingerprint

A read that has no fingerprint cannot be compared, so it is gone through, to
what it read in turn.

- **A fact found is the result.** It was computed from reads with exactly
  these fingerprints, and a query is a function of what it reads, so
  computing it now would make the same reads, in the same order, and give
  the same value. This holds whichever state the list of reads came from.
- **A marked result is looked for as a fact before it is computed.** What it
  read last time is brought up to date, and the key of those reads with the
  fingerprints they have now is looked up. This is what makes going back
  free: a branch switched away from and back to, an edit that is undone, or
  a commit another worktree already checked finds each result done.
- **A result the state never held is looked for too, where its query is
  portable.** A state has no list of reads for a result it never held. So
  for a portable query the store keeps, once for each key, the names of what
  the result read when it was first computed anywhere, and a new result is
  looked for under those reads, each brought up to date first. This is how a
  state that reaches an instance of the standard library, or a test's key,
  finds what another state computed, without a state of its own to start
  from. Code generation's queries are portable: an instance's LIR, a pulled
  method's version, an instance's own hash and what it refers to, its group,
  its key, and a test's key. A type checker's result is found through the
  state its worktree starts from, and keeping every result's reads a second
  time would double what a state takes in the store.
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

### What keeps its bytes

A stage marks a query as saved where reading its result back is cheaper than
computing it:

- each file's declarations, and each definition's tree, where it starts, and
  its resolved form
- what a lookup found: a definition by name in a module, a type's members by
  name, a file's imports, whether a module exists, the `impl`s of a trait
  for a type, and the traits that declare a method
- each definition's interface, shape, and signature, each constant's value,
  and whether a method can be pulled
- each definition's checked body and ownership's result, and each stage's
  diagnostics for it
- each file's diagnostics, and each package's checks
- each instance's LIR, each pulled method's version, each instance's own
  hash and what it refers to, the group it is in, and its key, and each
  test's key

What is not saved is a view of something that is: a file's tokens and
trees, the indexes over a package's declarations, and a definition's text.
These are part of a state like any result, with their fingerprints and what
they read, so a change stops at them in a state opened from the store as it
does in a live one. Only their values are missing, and are computed again
where something needs them. A value computed again has the fingerprint it
had, so nothing that read it is touched; were one ever to come back
different, everything that read it would be checked again.

## States in the store

### Artifacts

A state is written as an *artifact*, which is a value in the store, named by
its hash like any other:

- **A whole state** holds every node the state's kept results and set inputs
  reach, apart from those of its fixed bases: each node's name and key, its
  fingerprint, what it read, as places in a table of names, and whether a
  request kept it.
- **A difference** names an earlier artifact and holds what the engine
  itself holds and changed since: the nodes it computed, found as facts, or
  set, those a request began or stopped keeping, and the names of those it
  dropped.

An artifact never changes, so one names a state for good, and many states
can be differences over one artifact.

- **Writing costs O(change).** `Engine.write` writes a difference over the
  artifact the engine was opened from or last wrote. The first write of an
  engine that was opened from none writes the whole state.
- **A copy that came out as the base's result, reading the same, is not
  written,** since the base holds it. If an earlier difference of the chain
  holds another result for it, it is written, to take that one's place.
- **A node is written with the first node that reads it.** A node that is
  written must find what it read when the state is opened, so a node the
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
  the chain holds for its name and key. A node a difference dropped keeps
  its place, with nothing in it, where the whole state holds it too, so that
  the whole state's result, which is of an earlier state, is never read in
  its stead.
- **Values are read when first needed.** Opening reads the artifacts and no
  value.
- **What cannot be checked is left out:** a node of a query this compiler
  does not declare, a node that read a node that cannot be found, and
  everything that read those.

So two worktrees opened from one artifact share everything, and each holds
what it changed.

### Folding

A chain of differences is folded into one whole state when its differences
hold more than half as many nodes as the whole state, and more than 256. The
state is written whole, without what its kept results no longer reach, and
the session is opened again from it. So what a session holds itself, and
what is read to open a state, stay within a constant of what changed, and
the total written stays a constant multiple of what changed.

Folding costs the state's size, so no command should wait for it:

- **The background process folds a session while no request is waiting.**
  A first test run adds half again to a state that only a check made, and
  the command after it finds the session as it left it.
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
- **A dependency is to be another,** keyed by the package's content and the
  keys of the packages it depends on. There is no package registry yet, so
  stage0 has only the standard library's.
- **A package being worked on is part of its worktree's state,** which is a
  base and a difference like any state. Giving each such package an
  artifact of its own, keyed by its sources and the interfaces it reads of
  others, would let an unchanged package be found in one lookup from any
  worktree, and is not built.

## The store

The store lives in `$TRUSS_CACHE`, else `$XDG_CACHE_HOME/truss`, else
`~/.cache/truss`, and is shared by every project, worktree, and compiler on
the machine. It holds:

| Kind | Named by | Where |
|---|---|---|
| Values, artifacts among them | The BLAKE3 hash of their bytes | `segments/` |
| Facts, and what each result first read | The hash of their key | `segments/` |
| Results of expensive steps | The hash of their kind and of exactly the input that made them (see [Exact keys](#exact-keys)) | `segments/` |
| A package's artifact | The key of its sources | `segments/` |
| Object files | Their key, as CODEGEN.md describes | `objects/`, one file each, since a linker reads them by path |
| Pointers | A worktree's session | `pointers/` |
| The compiler's identity, the list of worktrees, and the background process's lock and log | | the top, and `servers/` |

Everything but a pointer is named by what it holds or what made it, and
never changes.

### Segments

Values and results live in append-only segment files, as Bitcask stores
them, with sorted indexes like git's pack files:

- **A record** is a kind byte, a 32-byte key, the value's length, the value,
  and an 8-byte FNV-1a checksum of the rest. Every key has the same width: a
  value's is the hash of its bytes, and a result's is the hash of its kind
  and key.
- **Each process that writes has a segment of its own,** locked while it
  writes, so writers never share a file and need no lock to write. A value
  two processes both add is in both segments, which is harmless, since its
  name is its hash.
- **Records are gathered and written together,** a megabyte at a time, and
  whenever the store is flushed. A first check adds hundreds of thousands of
  records, and a system call for each would be most of the time adding them
  takes. A record that is not written yet is read from memory.
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
  again. A read that must see what another process just wrote, such as a
  worktree's state, looks first.
- **A damaged or cut-off record is missing.** Every read checks the
  checksum, so a crash or a damaged file costs a recomputation, never a wrong
  answer.
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
- **A pointer has one writer,** which holds its lock. A session's pointer is
  named by the compiler's identity and its worktree, so a new compiler
  starts from the files, and still finds every result whose key it computes
  the same way.

### Garbage collection

The store is a cache, and the background process keeps it within a size
budget, 20 GiB unless `TRUSS_CACHE_SIZE` gives one in bytes. Every ten
minutes it checks, and when the segments take more:

- **What a live state names is kept:** the artifacts of its chain, and every
  value they name. A worktree's state is live while its directory exists,
  and its pointer is removed once the directory is gone. The standard
  library's artifact is kept.
- **Results are kept while in use:** those this process read or added, and
  those in segments written in the last week.
- **Survivors are copied into a new segment, and the old ones deleted.**
  Segments another running process is still writing are left alone, which the
  lock on each tells.

## Exact keys

The most expensive work in a build is outside the compiler's own queries:
compiling C, running tests, running the solver, and running code while
compiling. Each of these is a pure function of an input that the compiler can
write out completely, so its result is a fact kept under the hash of that
input:

| Result | Key | Kept | Built |
|---|---|---|---|
| A test's outcome | The key of everything the test can reach, as [Composed keys](#composed-keys) describes, the code generator's version, and the target's widths | Every deterministic outcome | Yes, for a pass with nothing to show |
| An object file | The C text, the C compiler's identity, and its flags | The object | Yes |
| A proof | The query sent to the solver, with every name numbered, and the solver's identity, options, and step limit | Proven or not proven | No: there is no prover yet |
| A value worked out while compiling | The key of the code that ran, its input, and the target | The value's binary form | No: stage0 builds these as objects, and does not run template checks |

- **These keys are exact.** Everything the result depends on is in the key,
  so a result can be reused by any session, on any branch, by any compiler
  that makes the same key. That is how renaming a definition, or moving it
  to another module, finds its test results already done.
- **The target is in a test's key** because `USize` is a `typedef` in the
  generated C, so the LIR is the same for 32-bit and 64-bit targets while
  results such as `USize.maximum` differ. Code for one operating system lives
  only in the standard library, so a difference between systems is already
  in the LIR.
- **A proof's key needs no target.** A proof assumes only what DESIGN.md
  says `USize` is, 32 or 64 bits, unless its package says
  `usize_bits = 64`, and that assumption is part of the query sent to the
  solver.
- **Only deterministic outcomes are kept.** A test that passed, failed an
  `assert`, panicked, or reached a `todo` gives the same outcome on every
  machine. One that ran out of time, ran out of memory, or overflowed its
  stack depends on the machine, its stack size, and the C compiler's
  optimizations, none of which are in the key, so it is reported and never
  kept. A run with sanitizers keeps nothing.
- **Positions in a kept outcome are to be numbered too.** A failure's
  message, an `echo`, and a panic give positions, which the key leaves out.
  Once they are recorded as an instance's number and a place within its
  definition, as CODEGEN.md's anchors are, a kept failure can be shown where
  the code is now. Until then, stage0 keeps only a pass with nothing to show.

### Lowering

Code generation's lowering is a query, so a test run after an edit lowers
only the instances the edit reached:

- **An instance's LIR** is a query keyed by the instance and by how it is
  lowered: the target's widths, and whether the program checks what the
  prover would prove. A pulled method's version, whose locals make its
  cursor's fields, is a query of its own.
- **Each computation lowers in a context of its own,** made from the
  query's reads. A layout or a piece of generated code worked out on the way
  is read through that query, never cached where another query could use it
  without reading what it came from.
- **A constant that is worked out by running code** is the one result a
  query cannot make, since running code is not a function of reads. Its
  query says so instead, and the build runs the constant's evaluator, whose
  code is lowered by the same query, and puts the value in the program. Only
  that constant's data depends on running code; every instance that uses it
  refers to it by name.

### Composed keys

A test's result is kept under the key of everything its code can reach. That
key is composed from the instances' own keys, as a Merkle tree's is, so that
an edit changes the keys of what can reach the edited code and of nothing
else:

- **An instance's own hash** is the hash of its LIR with each instance it
  refers to written as that instance's place in the list of what it refers
  to, and each path as a number given in the order paths are first met. It
  holds no name, so renaming or moving a definition changes no hash. A
  constant worked out by running code refers to its evaluator, whose code is
  what decides its value.
- **The key of everything an instance can reach** is its own hash and the
  key of each instance it refers to, in order.
- **Instances that reach each other are keyed as a group.** A key cannot be
  made of keys that are made of it. So the groups of instances that reach
  each other are found, by Tarjan's algorithm, among everything the wanted
  tests and programs reach, and an instance of a group is keyed by the group
  as a walk from the instance reaches it: each of the group's instances, in
  the order the walk first reaches them, as its own hash and what it refers
  to, a number for an instance of the group and a key for any other. An
  instance that refers only to itself is no group, since its own hash marks
  that.
- **The wanted tests and programs are an input.** Finding groups needs
  somewhere to start, and starting from every test would lower every test's
  code when one test is asked about. So a driver says which tests' keys it
  wants before it asks for them, and the database adds them to this input.
  A key asked for without that is an error wherever the code reaches itself.
- **The groups come out the same unless one forms or changes.** Finding them
  reads what every reached instance refers to, which changes when a call is
  added or removed, and its result changes only when a group does. It is of
  an earlier phase than the keys, so an edit that changes no group costs the
  keys nothing but the keys of what can reach the edit.

Finding the groups walks every instance the wanted tests reach, when what
any of them refers to changes. That is the one step here whose cost follows
the tests asked about and not the change, and it reads only lists of what
instances refer to.

## Sessions

A *session* is one worktree's state, with what a command needs around it: its
engine, the pointer that names its state in the store, and the problems its
manifests have. A worktree is a directory with one or more packages in it:
the top of the git worktree a command's directory is in, or outside git, the
nearest directory at or above it that holds a `truss.toml`, or else the
directory itself. Its packages are the directories under it with a
`truss.toml`, and each module file belongs to the nearest package above it.
Directories whose names start with `.`, and `_build` and `node_modules`, are
passed over.

### The background process

One background process per user and compiler serves every session on the
machine, as Gradle's daemon and Bazel's server do. The first command starts
it, detached from the terminal, with its output in `servers/server.log`, and
it exits after three hours without a request, the default of both.

- **It holds nothing that is not in the store.** What a session computed is
  written when its command is done. The process keeps each session's engine
  in memory so that the next command finds it there, and shares one base
  between every session opened from it.
- **Clients connect through a Unix socket** in `servers/`, named by the
  compiler's identity. A socket's path has a limit of about 100 bytes, so a
  store with a long path puts the socket in `/tmp`, named by a hash of where
  it would have been. A lock beside it in the store keeps to one process per
  compiler.
- **Without the background process,** as in CI, `--no-server` runs a
  command in its own process, against the same store. It takes the
  session's pointer lock first, so a pointer never has two writers, and it
  refuses, saying why, while the background process has that session open.
- **Requests are answered one at a time.** Requests, progress, and answers
  travel as OCaml's marshaled values, which is safe because the socket is
  named by the compiler's identity, so both ends are the same program.

### Watching files

- **A command scans its worktree before it is answered.** It compares each
  file's size, modification time, and inode with the stamps the state holds,
  and reads only the files that differ. So a command always sees every
  change made before it, with no need for the cookie files Watchman uses to
  make late file events safe.
- **While no request is waiting, the process scans every open worktree each
  second,** and brings each state up to date, so diagnostics are current
  before anyone asks for them, and overlaps are found as work happens.
- **Scanning is O(files) in stamps,** a few milliseconds for ten thousand
  files. FSEvents on macOS and inotify on Linux would make it O(change), but
  OCaml reaches them only through C bindings, which stage0 has none of yet.
  Since a command scans anyway, adding them changes only how soon the
  process hears of a change.

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
  over the other worktree's artifact, so the two share everything but what
  differs, in the store and, in one process, in memory. An agent that
  creates a worktree from `main` gets a warm session at once, whether or not
  any process has `main`'s session open.
- **A worktree with no state near it** is checked from the files, over the
  standard library's artifact, and finds as a fact every result that any
  state computed from the same reads.
- **A state is first written when a command is done,** with what the command
  computed, so that the first artifact is a whole state.
- **An idle session is written and dropped from memory** after an hour
  without requests, and opened again when next needed.

### Sessions for commits

A session can also be opened for a git commit, with its files read from git
through `git ls-tree` and `git cat-file`. It starts from the nearest saved
state, as a new worktree does, and is kept in memory and never pointed at.
This is how the database gets the state of a base commit, compares a branch
that has no worktree, and checks a merge.

### Trials

`Database.trial` gives an engine that starts from a session's state and
changes on its own: the session's state is written, and opened again. The
trial holds what it changes and shares the rest with the session. A rename
checks its plan in a trial before it writes a file, and a merge is checked
in one.

## Questions

These are what tools can ask a session. Every answer names definitions by
path and part, and files relative to the worktree's root, never nodes.

| Question | Asked by | Answer |
|---|---|---|
| `open_session`, `diagnostics`, `problems` | `truss check` and every command that reads code | The session for a directory's worktree, current with its files; the packages the directory is about; each file's diagnostics; and the manifests that could not be read |
| `dependencies`, `reads`, `readers` | `truss references`, `truss dependencies`, `truss holes`, `truss impact` | For every definition, what each of its parts reads of other definitions' parts |
| `find_definitions` | `truss references`, `truss dependencies` | The definitions a name means: a full path, or the end of one |
| `base_commit`, `open_commit_of`, `changes` | `truss impact` | A session at a commit, and every part a change between two sessions can reach, with whether it changed |
| `other_worktrees`, `overlap_with`, `merge_preview` | `truss overlap`, `truss check` | Where two sessions' changes meet, and the diagnostics a merge of the two would have that neither has |
| `trial` | `truss rename` | An engine to try a change in |
| `test_results`, `want`, `objects_directory`, `programs_directory` | `truss test`, `truss run`, `truss build` | Where test results, object files, and programs to run are kept, in the store, and saying which tests' keys are wanted |
| `sessions`, `stop` | `truss status`, `truss stop` | The background process's sessions, and ending it |

Results asked for are kept current from then on, and the command line saves
each session it opened when its command is done. A test runs only when
asked.

A question about the graph first checks every package of the sessions it
reads, so that every definition's results are there to read. A definition
reads another's part when one of its nodes reads that part's node, directly
or through nodes about no definition, such as lookups; the standard
library's own lookups are not followed, so a definition is not said to read
everything they read.

### Comparing two states

`changes` compares one state with another. A state holds only what differs
from its bases, or may, so where the two share a base, the nodes that can
differ are those either holds itself; a base that only one of them has is
compared whole. Each such node is found in the other state by its query and
key, computed there if the other has none, and compared by fingerprint, and
by value where fingerprints differ.

### Impact

GOALS.md asks for tools that show agents and reviewers what each change
affects, and the signatures of what it touched. `truss impact` compares the
worktree with a base, its merge base with the default branch unless another
commit is named, and shows:

- **What changed,** by definition and part, such as the tree, the
  interface, or the body.
- **The signatures to review:** every definition whose interface, signature,
  or shape changed, before and after, with every definition that reads one
  of those, since DESIGN.md says a signature carries everything important
  about code.
- **The tests whose keys changed,** which are the only tests the change can
  affect, each with whether its result is already kept.

### Holes and what can ship

A hole's type and the names in scope come from the definition's checked form
and resolution, through `Inspect`: name resolution records the names in
scope at each `todo` as it walks the definition, so there is one account of
scope, and the checked form gives their types. What a hole blocks is every
test and `main` that reaches its definition through what each definition
reads.

## Parallel work

GOALS.md names sorting out conflicts with other agents as one of the things
that will dominate development time, and asks that agents can find exactly
where and how their work overlaps. Git sees only lines. The database sees
what each change affects, so it can find overlaps that merge without a
textual conflict and break once merged:

- Agent A changes `parse` to return a `Result`, and agent B, in another
  worktree, adds a call to `parse`. Git merges both cleanly, and the result
  does not compile.
- Agents A and B each add a method `find` to `List`, in different files.
- Agent A strengthens a type's invariant that agent B's new function relies
  on.

### What counts as an overlap

For two worktrees, the database finds the merge base of their commits and
compares each worktree with it, as `impact` does: each node that differs
from the base's is that worktree's *change*. The two overlap where:

1. **Both changed one node.** This covers editing the same part of the same
   definition, even on different lines, and two additions that answer one
   lookup, such as the two `find` methods, which both change the members of
   `List` named `find`.
2. **One changed a node that reads what the other changed.** B's new
   `quadruple` has a body that reads the signature of `parse`, and A changed
   that signature, so the database says "this worktree's change to the body
   of `quadruple` reads the signature of `parse`, which the other changes".

Nodes are matched between sessions by query and key. Each overlap names the
definitions and parts on both sides, or the lookup, when no definition is
involved.

### When overlaps are found

- **As work happens.** The background process sees every worktree of a
  repository, which it tells by their common git directory. A `check` lists
  where its worktree's changes meet those of every other open worktree of the
  repository, in a section of its own. Overlaps are not diagnostics: nothing
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

## Sharing between machines

The store is local. Its keys are made so that sharing can be added without
changing any of them: a fact, a test's outcome, a proof, an object, and a
package's artifact are each named by what made them, on any machine.

Sharing matters most where sessions are short: an agent in a fresh
container, or CI, starts with no store, and without one must compute
everything before it can find a single kept test or proof, since their keys
are made from the compiler's own results. With a shared store it finds the
nearest state and its facts, and does only the work its change needs.

It is left out because of what a result claims. DESIGN.md lets reviewers
trust proofs instead of reading them, so a forged "proven" or "passed" in a
shared store would skip exactly the checks Truss exists to make, and an
object file is code that will run. That is the supply-chain attack GOALS.md
sets out to stop. So when results are shared, a result from another machine
will be used only when it is signed by a key the user has said to trust, as
Nix accepts substitutes only with `trusted-public-keys`. Every result is a
function of its key, so a signed result can also be checked by computing it
again.

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
  own result again.
- **Every test audits.** The test harness audits every engine a test made,
  when the test ends. So each test of each stage also tests that the
  database kept every result current, and that the stage's queries are
  functions of what they read: a query that read something it did not go
  through its context for would come out different in the new engine.
- **Counts of work.** The engine counts what it marks, finds current,
  computes, finds as facts, copies, and drops. Tests make the same edit in a
  package of four modules and in one of forty, and assert that the counts
  are equal: for a body, a local, a signature's layout, and a new
  definition. They compare counts, never times, so they are the same on
  every machine.
- **The fuzzer.** `stage0/tools/engine_fuzz` makes a random graph of
  queries, whose reads depend on what they have read, over a few inputs, and
  makes random steps: it sets and removes inputs, asks for and releases
  results, writes the state and opens it again, and opens a second engine
  from the same state. After each step it audits each engine against one
  with no bases. For a run that fails it prints the fewest of the run's
  steps that still fail. It is a tool, run by hand, and each problem it
  finds becomes a focused test.
- **Times.** `stage0/tools/database_timing` makes a package of a given size
  in a store of its own and times a first check, writing the state, opening
  it as a new process does, and three edits, each with what the engine
  computed and found. The counts of work say whether what is computed
  follows the change; the times say what it costs, and show what the counts
  do not, such as work done for each reader of a result.

## Testing

The tests follow IMPLEMENTATION.md's rules for testing: each states one fact
about a small input.

- **The engine** (`query_tests`): what a first demand computes, that a
  change computes only what read it, early cutoff, that a result that comes
  out the same marks nothing in a later phase, that a query cannot read a
  later phase, the counts of work with ten readers and a thousand, edges in
  both directions, dropping, that a result a running query read is not
  dropped, that an engine nothing refers to is freed, cycles and exceptions,
  engines over a base, and the audit.
- **The store and states** (`store_tests`): values by name, sealing and
  indexes, a second process's segments, damaged records, results by kind,
  pointers and their locks across processes, collection, a state opened from
  the store, differences, the whole state written again, values gone from
  the store, facts found by another state and on going back, that a
  fingerprint does not depend on which of a value's parts are one block in
  memory, and what the fuzzer found, such as a result that a request kept
  after it was written.
- **Sessions and questions** (`database_tests`): the background process
  passing progress and answers and seeing every earlier write, and a second
  writer refused, diagnostics before and after fixes and restarts, what an
  edit computes again, removed modules, malformed manifests, packages in one
  worktree, the `usize_bits` rule between packages, a new worktree starting
  from the nearest saved state and holding only its difference, what reads
  what in both directions, comparing with a base commit, and both kinds of
  overlap, with a merge, in a git repository. What the command line shows of
  these, and test runs on a session, are tested in `stage0/test/cli`.
- **The cost of a change** (`scale_tests`): the counts of work for the same
  edit in a small package and a large one.
- **Every other stage's tests** run on the same engine, with the standard
  library as a fixed base shared by every test in an executable, and are
  audited.

## Not built yet

- **Sharing between machines,** with signed results, as above.
- **Test results as facts with the code that ran.** A test's key covers
  everything its code can reach. Tests are deterministic, so a result also
  stays good while the code the test actually ran is unchanged, which is far
  less. Recording what ran, as a query's reads are recorded, would run fewer
  tests after an edit. Kept failures, with numbered positions, belong with
  it.
- **A package being worked on as an artifact of its own,** so that an
  unchanged package is found in one lookup from any worktree, and
  **dependency packages as artifacts,** once there is a registry.
- **Artifacts read in part.** A whole state is one value, read whole to open
  the state, so the first command of a new process costs the state's size:
  every node is made before one is asked for. In the background process that
  is paid once for each whole state. A state that reads only the parts it
  touches would open in the time its change needs, however large the
  project.
- **Merging segments, and indexes read in part.** Every process that writes
  leaves a segment, and a lookup searches each segment's index in turn, so a
  lookup costs the number of segments until collection, which runs only over
  the size budget, copies them into one. Each index is also read whole when
  a process opens the store. Merging small segments as they gather, as a
  log-structured store does, and reading an index a block at a time would
  keep both within the logarithm of the store's size.
- **Each stage's version in keys,** in place of the compiler's identity.
- **Merging at the level of definitions.** Two worktrees are merged by git,
  line by line, and the merge is then checked. Truss has no comments, one
  format, and no meaning in the order of definitions, so the database could
  merge definition by definition and leave to an agent only the changes that
  really meet.
- **Watching files with FSEvents and inotify,** in place of scanning stamps
  each second.
- **Answering several requests at once.** The background process answers one
  at a time, and a test run holds it until the run ends. States never change
  each other and a base never changes, so sessions can be brought up to date
  in parallel with no change to any stage.
- **Letting go of kept results.** A result a request asked for is kept until
  its state is folded and nothing reaches it. Nothing lets go of a result
  that is still reached and no longer asked for, such as the key of a test
  that was deleted.
- **A fingerprint summary written in O(change).** A pointer holds every
  file's fingerprint, and is written whole when any file changed.

## Open questions

- **Running affected tests unasked.** Test keys stay current once a test
  run has asked for them, so the background process could run the tests whose
  keys changed while the machine is idle, and have their results ready before
  `test` is asked. Whether that is worth the CPU when several agents share a
  machine is not decided.
- **Questions answered from an index.** A graph question walks the state to
  find what reads what, which costs the state's size each time it is asked.
  An index kept current like any result would answer in the size of the
  answer.
- **The rules that span a package.** A package's checks are one result that
  reads every module's declarations, every `impl`, and every generic body of
  the package, so it is computed again when a definition is added or removed
  and when any of those changes. What it does for each definition is small,
  so adding a function to a package of eight thousand costs milliseconds,
  but the cost follows the package. Splitting it into a result for each
  definition and one for each lookup would make it follow the change.
