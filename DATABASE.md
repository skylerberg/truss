# Truss Code Database

This document designs the code database: the part of the toolchain that
holds every definition being worked on and everything computed from them,
keeps those results current as files change, saves them so that a new
process or a new worktree starts warm, and answers questions about what
depends on what. It follows the decisions in [DESIGN.md](DESIGN.md) and
[GOALS.md](GOALS.md), and serves the stages described in
[TYPECHECKER.md](TYPECHECKER.md) and [CODEGEN.md](CODEGEN.md).

It is built in [`stage0/`](stage0): the engine in `incremental`, with its
two views `query` and `engine`, the store in `store`, sessions and requests
in `database`, and what tools ask of one definition in `inspect`. The
`truss` command is the database's client. What is not built yet is said
where it comes up, and listed at the end.

## What the database does

GOALS.md asks that a change cost O(change), not O(project), for building,
testing, and verifying, and that agents can see exactly what their changes
affect and where their work overlaps with other agents'. The database is what
makes both possible. It:

- holds the inputs of every worktree being worked on: the packages, their
  manifests, and the text of every module
- keeps the results that have been asked for current as inputs change, by
  pushing each change along a graph of what read what, and stopping wherever
  a result comes out the same
- saves the graph and the results worth keeping, so that a restart or a new
  worktree does only the work its differences need
- keeps the results of expensive steps, such as a test run or a C compile,
  under a key built from exactly the input each one consumed, so that every
  worktree on the machine shares them
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
- share results between machines. See
  [Sharing between machines](#sharing-between-machines).

## Structure

The database is three layers, each behind one narrow interface:

```text
 command line   language server   agent tools
        \              |              /
         ▼             ▼             ▼
   ┌──────────────────────────────────────┐
   │ Database: sessions, requests, graph   │  requests and answers, by definition
   │ questions, overlap, scheduling        │
   └──────────────────────────────────────┘
                     │ Engine
   ┌──────────────────────────────────────┐
   │ Engine: nodes, edges, pushing changes │◀── Query ── compiler stages
   │ saving and loading the graph          │
   └──────────────────────────────────────┘
                     │ Store
   ┌──────────────────────────────────────┐
   │ Store: values by hash, results by     │
   │ key, journals                         │
   └──────────────────────────────────────┘
                     │
                ~/.cache/truss
```

| Interface | Library | Used by | What it offers |
|---|---|---|---|
| `Query` | `query` | Compiler stages | Declaring inputs and queries, and reading them while a query runs |
| `Engine` | `engine` | `Database` and tests | Setting inputs, keeping results current, saving and loading, and walking the graph |
| `Store` | `store` | `Engine`, and the exact-key caches in `Database` | Bytes by content hash, results by key, and append-only journals |
| `Database` | `database` | The command line, and the tools on it | Answering requests about a worktree |

`Query` and `Engine` are two views of one implementation, `Incremental`,
which nothing else names. These rules keep each interface narrow, so that
each layer can be replaced without touching the others:

- **Stages see only `Query`.** A stage never sees the engine, the store, the
  file system, worktrees, git, or another session.
- **Only `Database` changes inputs,** and inputs are the only way anything
  outside the stages reaches them. A driver that compiles, such as a test
  run, reads results through a context the database gives it, as a query
  would.
- **Answers name definitions, never engine nodes.** A graph question returns
  paths and parts, so a different engine can answer the same questions.
- **Each query's key and value types belong to the stage that declares
  them.** The database knows them only as values it can compare and save.
- **Code generation does not see the store.** A test run is handed functions
  that find and keep results by key, and the directory object files go in.
- **Clients see only requests and answers.** Whether the session runs in the
  background process or in the client's own process makes no difference to
  them.

## Pushing changes

A change is pushed from where it happened to what it affects. Editing a file
marks the results that can reach it, and only those are checked again; a
result that comes out the same stops the work there.

The alternative is pulling: a command asks for a result, and the engine walks
what that result read, down to the inputs, to see whether anything changed.
Salsa and rustc's queries work this way, and so does Shake. Pulling is cheap
when little changed, but its cost follows what is asked for, not what
changed: a check of a package asks for the checked body of every definition,
so even a one-character edit walks the whole project. Pulling also cannot
answer "what does this change affect?" without a scan, and that question is
behind choosing tests, reviewing a change, listing what a hole blocks, and
finding where two agents' work overlaps.

Pushing is how Jane Street's Incremental and spreadsheet recalculation work,
and how Tup builds, which its author calls a "beta" build system to set it
apart from the scanning "alpha" ones. Truss marks the way Adapton does,
pushing a flag to everything a change can reach and bringing each marked
result up to date when it is needed:

- **A result that has been asked for is kept current.** Once a request asks
  for it, every later change that can reach it marks it, and stabilizing
  brings it up to date, so asking for it again costs nothing.
- **A result nobody has asked for is computed when first asked for,** by
  running its query, which asks for what it needs in turn. So nothing is
  computed that nobody wants.

### The graph

The engine's graph has a *node* for each input and for each query result,
named by the query's name and its key. An *edge* runs from a node to each
node it read the last time it was computed, and the engine keeps every edge
in both directions:

- **Edges are learned, not declared.** A query reads through its context
  while it runs, and each read adds an edge. Truss's dependencies are not
  known before a query runs: a body depends on what its name lookups found,
  which depends on the names it uses.
- **A read that found nothing is an edge too.** Asking for the constants
  named `count` in a file, and finding none, depends on that answer. Adding
  such a constant later changes the answer, and so reaches the reader, as
  DESIGN.md requires for patterns.
- **The edges in from readers are what a change follows.** The edges out
  serve two purposes: when a node is computed again and reads different
  things, the engine removes it from the readers of what it no longer reads;
  and they answer "why does this depend on that?"
- **A node nothing reads, and no request kept, is dropped,** as soon as its
  last reader stops reading it. A node is added to its new reads' readers
  before it is taken from its old ones, so a node read both before and after
  is never dropped in between.

DESIGN.md and TYPECHECKER.md list what a result may read: parts of
definitions, interfaces, shapes, lookups by scope and name, body facts, and
manifest entries. Those are the kinds of node a stage declares. The engine
does not know them.

### Keeping results current

Stamps order changes. Each input change takes the next stamp, and each node
records the stamp at which its result last changed and the stamp at which it
was last confirmed current. Setting an input to a value equal to its old one
does nothing. Otherwise:

1. The input takes its new value and the next stamp, and every node that can
   reach it, through the edges in from readers, is marked. Marking sets a
   flag and nothing more, so it costs the nodes the change can affect.
2. A marked node is brought up to date when it is needed: when something
   reads it, or when stabilizing reaches it because a request kept it. Its
   reads are brought up to date first, in the order it read them.
3. If one of them changed after the node was last confirmed, the node is
   computed again; the check stops at the first such read, since a later read
   may not be made at all once an earlier one gives a different answer.
   Otherwise the node is confirmed without being computed.
4. A node computed again whose result equals its old one keeps its old stamp,
   so its readers find nothing changed and are confirmed without being
   computed. This is early cutoff.
5. Stabilizing brings every marked node a request kept up to date, and
   reports each node it computed again and each whose result changed.

So a change costs a flag on each node it can reach, and computing again the
nodes whose reads really changed. Editing a function's body computes its
resolved form and its checked body again. If its interface comes out the
same, no caller is computed again.

- **Results are recomputed, never patched.** A query is a function of what
  it reads, so computing it again from the same reads gives the same value.
  The engine needs no knowledge of what a query does.
- **Cycles are errors.** A query that asks, directly or not, for its own
  result raises `Cycle` with the queries on the cycle, and every query on the
  cycle has the cycle as its result, whether or not it caught it, so a cycle
  is the same error wherever it is met. The reading that closed the cycle is
  an edge too, so that removing the cycle reaches every query on it.
  TYPECHECKER.md designs the stages so that ordinary code makes no cycle:
  constants that refer to each other, the one real case, are found by the
  constant's own evaluation, which keeps the constants on its way.

### What a query must be

The engine relies on these, and its tests check each:

- **A query is a pure function of what it reads through its context.** It
  reads no global state, no files, no clock, and no other session.
- **Its value is canonical,** as DESIGN.md requires of every stored result:
  no fresh numbering, no hash-table order, no timestamps. Early cutoff
  compares values, so an unstable value would defeat it.
- **Its value holds no functions,** unless the query gives its own equality.
  A saved value that holds functions cannot be saved, and is computed again
  after loading instead.
- **An exception is an outcome.** A query that raises keeps its exception
  like a value, so its readers see the same exception until something it read
  changes. An exception is never saved. Absence is better told with an
  option, and the stages do so, except for an input that is not set, which
  `Query.get` reports as `Not_found`.

## The interfaces

The signatures below are the built ones, shortened.

### `Query`, for compiler stages

```ocaml
type context
type subject = { path : Path.t; part : string option }

val input :
  name:string -> show:('key -> string) -> ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) -> unit -> ('key, 'value) input

val query :
  name:string -> show:('key -> string) -> ?saved:bool ->
  ?equal:('value -> 'value -> bool) -> ?about:('key -> subject option) ->
  (context -> 'key -> 'value) -> ('key, 'value) query

val get : context -> ('key, 'value) input -> 'key -> 'value
val find : context -> ('key, 'value) input -> 'key -> 'value option
val demand : context -> ('key, 'value) query -> 'key -> 'value

exception Cycle of string list
```

- **Inputs are always saved.** A query is saved when it says `~saved:true`.
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

val create : ?log:bool -> ?shared:t -> unit -> t
val frozen_layer : ?log:bool -> unit -> t
val context : t -> Query.context
val set : t -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) Query.input -> 'key -> unit
val get : t -> ('key, 'value) Query.query -> 'key -> 'value
val release : t -> ('key, 'value) Query.query -> 'key -> unit
val stabilize : t -> change
val fork : t -> t

val nodes : t -> node list
val label : node -> string
val subject : node -> Query.subject option
val reads : node -> node list
val readers : node -> node list
val current_in : node -> t -> node option
val same_outcome : node -> node -> bool

val attach : t -> Store.t -> unit
val save : t -> Store.journal -> unit
val load : ?log:bool -> ?shared:t -> ?frozen:bool -> Store.t -> Store.journal -> t option
val values_in : Store.journal -> string list
```

`fork` copies a graph, sharing every result, for a new worktree or a commit
that starts from another session's state. `current_in` finds the same query
and key in another engine and brings it up to date there, which is how two
sessions are compared.

### `Store`, for the engine and the caches

```ocaml
type t
val open_ : string -> t
val put : t -> string -> string
val get : t -> string -> string option
val flush : t -> unit
val find_result : t -> kind:string -> key:string -> string option
val add_result : t -> kind:string -> key:string -> string -> unit
val files : t -> string -> string

type journal
val journal : t -> string -> journal
val lock : journal -> bool
val records : journal -> string list
val append : journal -> string -> unit
val compact : journal -> string -> unit

val collect : t -> budget:int -> live:(string -> bool) -> unit
```

### `Database`, for tools

`Database` is a set of requests, each with an answer. `Database.call` sends
a request to the background process, starting it if it is not running, and
`Database.handle` answers it in the caller's own process; the requests and
answers are the same either way (see [Requests](#requests)).

## Inputs

A session's inputs are:

| Input | Key | Value |
|---|---|---|
| A package | Its name | Its manifest: dependencies, grants, and `usize_bits`, and its modules |
| A module's text | Its module path | The file's text |
| The layout | The session | Each package's directory and name, and every manifest and module file |
| A file's stamp | Its path in the worktree | Its size, modification time, and inode |
| A manifest's text | Its package's directory | The file's text |

The last three are the database's own, so that a restart reads only the files
whose stamps changed. A module's text is set from the file system, or from
git for a commit (see [Sessions](#sessions)). Lexing and parsing are
queries: a file is lexed and split again when its text changes, and a
definition whose tree comes out the same, as one that only moved does,
changes nothing that read it.

### Frozen layers

The standard library is built into the compiler and never changes while
anyone works, so it is a *frozen layer*: an engine whose inputs are set once,
which every session in a process shares, and which is saved in a journal of
its own, one per compiler.

- **A session reads the layer's inputs as its own.** A result computed only
  from frozen inputs, the first time it is computed, moves into the layer, so
  every other session finds it done. A result that already has readers in a
  session stays there, so that they see its later changes.
- **A frozen node keeps no edges in from readers.** It never changes, so
  nothing needs to know who read it. A session's own nodes keep edges out to
  it, which is all a graph question needs.
- **A frozen node never changes, so no result depends on finding it again.**
  A saved graph refers to the frozen nodes it read only when they are saved
  themselves, and loading leaves out a reference it cannot find.
- **Setting a layer's input after it has been read is an error.**

A dependency is meant to be a frozen layer too, keyed by the compiler's
identity, the package's content hash, and the layers it depends on. There is
no package registry yet, so stage0 has only the standard library's layer.

## Content hashes and the store

Definitions are hashed in parts, in deterministic CBOR, as DESIGN.md's
[hash format](DESIGN.md#the-hash-format) and TYPECHECKER.md's "Hashing"
describe. Those hashes are what other definitions' results depend on, and
they are the same in every compiler.

Saved query results are different: a journal belongs to one compiler, since
a result means something only to the code that computed it. So stage0 saves
a result as OCaml's marshaled bytes, named by their BLAKE3 hash, and reads
it back only in the compiler that wrote it. Writing a CBOR encoder and
decoder for each of the stages' result types would cost thousands of lines
that every change to a stage would have to keep up, and buy nothing a saved
graph needs. The compiler written in Truss will save its own results its
own way. Early cutoff after loading compares a recomputed result with the
loaded one by equality, so two encodings of one value can never make a
change look real.

### What the store holds

The store lives in `$TRUSS_CACHE`, else `$XDG_CACHE_HOME/truss`, else
`~/.cache/truss`, and is shared by every project, worktree, and compiler on
the machine. It holds:

| Kind | Named by | Where |
|---|---|---|
| Values | The BLAKE3 hash of their bytes | `segments/` |
| Results of expensive steps | The hash of their kind and of exactly the input that made them (see [Exact keys](#exact-keys)) | `segments/` |
| Object files | Their key, as CODEGEN.md describes | `objects/`, one file each, since a linker reads them by path |
| Journals | A session's name | `journals/` |
| The compiler's identity, the list of worktrees, and the background process's lock and log | | the top, and `servers/` |

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
- **A full segment is sealed,** at 64 MB or when its process closes the
  store, with an index beside it: its keys sorted, each with its record's
  offset and length, in fixed-width entries. The index is read into memory as
  one string and searched by halving, which takes about 44 bytes for each
  value and no allocation per entry. A segment still being written is read by
  scanning it.
- **A lookup that misses looks again** for segments that other processes
  made or grew since, before saying the store has nothing.
- **A damaged or cut-off record is missing.** Every read checks the
  checksum, so a crash or a damaged file costs a recomputation, never a wrong
  answer.
- **The store is written with ordinary file operations:** create, append,
  read, rename, flush to disk, and delete, and a file lock on a writer's own
  segment. Truss has no foreign code, so the compiler written in Truss cannot
  use SQLite or LMDB. A store it can rewrite with the standard library's file
  capabilities keeps the two compilers' stores alike.

One file per value would not do: a project of a hundred thousand
definitions saves about a million small values, and a file system spends far
more on a file's inode, directory entry, and block than such a value takes,
and far more time creating and opening files than reading one segment.

### Journals

A session's graph is saved as a journal: a base holding every saved node,
followed by a record of each save's changes since then.

- **Saving costs O(change).** Each save appends one record: the saved nodes
  computed or changed since the last save, with their values' names and their
  reads, and the nodes dropped since. The base is not rewritten.
- **A saved node's reads go through unsaved ones** to the saved nodes and
  inputs they reach. After loading, an unsaved node is computed again when a
  marked reader needs it. When an unsaved node's own reads change, the saved
  nodes that read through it are saved again, so their recorded reads stay
  true.
- **The changes are folded into a new base** when the journal grows past
  twice the last base and past 1 MB, so the total written stays a constant
  multiple of what changed.
- **A record is framed with its length and checksum.** A record cut short by
  a crash fails its check, and loading stops at the last whole record, which
  is a state the session really had.
- **Values are flushed before the record that names them,** so a journal
  never names a value that a crash lost.
- **A journal belongs to one compiler.** Its name includes the compiler's
  identity, the BLAKE3 hash of its executable, remembered by the executable's
  path, size, modification time, and inode. A new compiler starts from its own
  journal, and still finds every value and result whose key it computes the
  same way, which is what DESIGN.md's separate stage versions are for.
- **A journal has one writer,** which holds its lock.
- **Loading leaves out what it cannot check:** a saved node of a query this
  compiler does not declare, a node that reads an own node that is missing,
  and everything that reads those.

### What is saved

A stage marks a query as saved where reading its result back is cheaper than
computing it, and where early cutoff matters after a restart. Saved are each
file's declarations, each definition's tree and where it starts, its
resolved form, the hash of its parts, its interface, shape, and signature,
its checked body and ownership's result, each file's diagnostics, each
package's checks, each instance's LIR, each pulled method's version, and
each test's key.

### Lowering

Code generation's lowering is a query too, so a test run after an edit
lowers only the instances the edit reached, and a test's key, which is the
hash of what its code can reach, stays current like any other result:

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
- **A test's key** is a query that walks what the test can reach through the
  LIR queries, with an evaluated constant standing for its evaluator's code,
  which decides its value.

### Garbage collection

The store is a cache, and the background process keeps it within a size
budget, 20 GiB unless `TRUSS_CACHE_SIZE` gives one in bytes. Every ten
minutes it checks, and when the segments take more:

- **Values a live journal names are kept.** A session's journal is live
  while its worktree's directory exists, and is deleted once the directory
  is gone; the standard library's journals are kept.
- **Results are kept while in use:** those this process read or added, and
  those in segments written in the last week.
- **Survivors are copied into a new segment, and the old ones deleted.**
  Segments another running process is still writing are left alone, which the
  lock on each tells.

## Exact keys

The most expensive work in a build is outside the compiler's own queries:
compiling C, running tests, running the solver, and running code while
compiling. Each of these is a pure function of an input that the compiler can
write out completely, so its result is kept under the hash of that input,
with no graph:

| Result | Key | Kept | Built |
|---|---|---|---|
| A test's outcome | The numbered LIR of everything the test can reach, as CODEGEN.md describes, the code generator's version, and the target's widths | Every deterministic outcome | Yes, for a pass with nothing to show |
| An object file | The C text, the C compiler's identity, and its flags | The object | Yes |
| A proof | The query sent to the solver, with every name numbered, and the solver's identity, options, and step limit | Proven or not proven | No: there is no prover yet |
| A value worked out while compiling | The numbered LIR of the code that ran, its input, and the target | The value's binary form | No: stage0 builds these as objects, and does not run template checks |

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

## Sessions

A *session* is one worktree's state: its inputs, its graph, and the results
its requests have asked for. A worktree is a directory with one or more
packages in it: the top of the git worktree a request's directory is in, or
the directory itself outside git. Its packages are the directories under it
with a `truss.toml`, and each module file belongs to the nearest package
above it. Directories whose names start with `.`, and `_build` and
`node_modules`, are passed over.

### The background process

One background process per user and compiler serves every session on the
machine, as Gradle's daemon and Bazel's server do. The first command starts
it, detached from the terminal, with its output in `servers/server.log`, and
it exits after three hours without a request, the default of both.

- **One process sees every worktree.** That lets a new worktree start from
  another's state, lets the process find overlapping work as it happens, and
  shares one standard-library layer between every session.
- **Clients connect through a Unix socket** in `servers/`, named by the
  compiler's identity. A socket's path has a limit of about 100 bytes, so a
  store with a long path puts the socket in `/tmp`, named by a hash of where
  it would have been. A lock beside it in the store keeps to one process per
  compiler.
- **Without the background process,** as in CI, `--no-server` answers a
  request in the command's own process, against the same store. It takes the
  session's journal lock first, so a journal never has two writers, and it
  refuses, saying why, while the background process has that session open.
- **Requests are answered one at a time.** Requests and answers travel as
  OCaml's marshaled values, which is safe because the socket is named by the
  compiler's identity, so both ends are the same program.

### Watching files

- **A request scans its worktree before it is answered.** It compares each
  file's size, modification time, and inode with the stamps it saved, and
  reads only the files that differ. So a request always sees every change
  made before it, with no need for the cookie files Watchman uses to make
  late file events safe.
- **While no request is waiting, the process scans every open worktree each
  second,** and stabilizes, so diagnostics are current before anyone asks for
  them, and overlaps are found as work happens.
- **Scanning is O(files) in stamps,** a few milliseconds for ten thousand
  files. FSEvents on macOS and inotify on Linux would make it O(change), but
  OCaml reaches them only through C bindings, which stage0 has none of yet.
  Since a request scans anyway, adding them changes only how soon the
  process hears of a change.

### Starting a session

- **A worktree with a journal** loads it, scans its files, sets the inputs
  that differ, and stabilizes. That costs O(files) to scan and O(change) for
  everything else.
- **A new worktree starts from the nearest session.** The process reads the
  new worktree's modules and picks the open session whose modules differ
  from them in the fewest files. It forks that session's graph, forgets its
  stamps, sets the files that differ, and stabilizes. An agent that creates a
  worktree from `main` while another session is open gets a warm session at
  once, instead of checking the whole project from nothing.
- **A worktree with no near session** is checked from nothing, using the
  frozen layer and every exact-key result already in the store.
- **An idle session is saved and dropped from memory** after an hour without
  requests, and loaded again when next needed.

### Sessions for commits

A session can also be opened for a git commit, with its files read from git
through `git ls-tree` and `git cat-file`. It starts from the nearest
session, as a new worktree does, and is kept in memory and never saved. This
is how the database gets the state of a base commit, compares a branch that
has no worktree, and checks a merge.

## Requests

These are what clients can ask. Every answer names definitions by path and
part, and positions by file, line, and column, never by node.

| Request | Command | Answer |
|---|---|---|
| `Check` | `truss check [DIRECTORY]` | Every diagnostic of the packages at or under the directory, and where the worktree's changes meet those of other open worktrees |
| `Test` | `truss test [DIRECTORY]` | Each test's outcome, from the store or from running the tests whose keys have no result |
| `Build`, `Run` | `truss build DIRECTORY OUTPUT`, `truss run DIRECTORY ARGUMENTS` | A program; for `run`, built in the store for the client to run on its own terminal |
| `Explain` | `truss explain FILE:LINE:COLUMN` | What is at a position: the expression as written, what a name means, its type, and the signature it refers to |
| `References` | `truss references NAME` | Every definition that reads a definition, with the parts on each side |
| `Dependencies` | `truss dependencies NAME` | Every definition a definition reads, by part |
| `Impact` | `truss impact [--base COMMIT]` | What the worktree's changes from a base affected (see below) |
| `Holes` | `truss holes` | Each `todo`, with its type, the names in scope, and the tests and programs it blocks |
| `Overlap` | `truss overlap [--with BRANCH] [--merge]` | Where this worktree's changes meet another's (see [Parallel work](#parallel-work)) |
| `Sync` | `truss sync` | Nothing, once the worktree's changes have been seen |
| `Status`, `Stop` | `truss status`, `truss stop` | The background process's sessions, and ending it |

Every command takes `--no-server` and `--json`; `check --json` gives the
diagnostics as `truss-check --json` does, which is `check --no-server`.
Results asked for through these requests are kept current from then on, and
each request saves its session when it is done. A test runs only when
asked.

A graph question first checks the whole worktree, so that every definition's
results are there to read. A definition reads another's part when one of its
nodes reads that part's node, directly or through nodes about no definition,
such as lookups; the standard library's own lookups are not followed, so a
definition is not said to read everything they read.

### Impact

GOALS.md asks for tools that show agents and reviewers what each change
affects, and the signatures of what it touched. `impact` compares the
worktree with a base, its merge base with the default branch unless another
commit is named, and answers:

- **What changed,** by definition and part, such as the tree, the
  interface, or the body.
- **What was checked again and came out the same,** listed apart from what
  changed.
- **The signatures to review:** every definition whose interface, signature,
  or shape changed, and every definition that reads one of those, each with
  its signature, which DESIGN.md says carries everything important about
  code.
- **The tests whose keys changed,** which are the only tests the change can
  affect.

The comparison starts from the inputs that differ between the two sessions,
and follows the edges in from readers in the worktree's graph: every node a
difference can reach, and nothing else, is compared with the same query and
key in the base's session, which is brought up to date there.

### Holes and what can ship

A hole's type and the names in scope come from the definition's checked form
and resolution, through `Inspect`, which walks the tree's scopes: parameters,
`let` and `var`, `for`, lambdas, `match` arms, and the names an `is` test
binds in the block it guards. What a hole blocks is every test and `main`
that reaches its definition through what each definition reads.

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
  `git merge-tree`, opens a session for the result, and reports every
  diagnostic that is in the merge but in neither side. The rules above find
  where work meets; this finds whether it breaks. A worktree's uncommitted
  work goes into the merge through a commit made with an index of its own,
  so its files, index, and branches are untouched.

## Sharing between machines

The store is local. Results could be shared with CI and with other
developers, as Bazel's remote cache shares build actions, and the exact keys
are designed so that this can be added without changing any key.

It is left out because of what a result claims. DESIGN.md lets reviewers
trust proofs instead of reading them, so a forged "proven" or "passed" in a
shared cache would skip exactly the checks Truss exists to make, and an
object file is code that will run. That is the supply-chain attack GOALS.md
sets out to stop. So when results are shared, a result from another machine
will be used only when it is signed by a key the user has said to trust, as
Nix accepts substitutes only with `trusted-public-keys`. Journals are never
shared: a session is quick to rebuild from shared results.

## Testing

The tests follow IMPLEMENTATION.md's rules for testing: each states one fact
about a small input.

- **The engine** (`query_tests`): what a first demand computes, that a
  change computes only what read it, early cutoff, stabilizing, edges in both
  directions, dropping what nothing reads, cycles and exceptions, frozen
  layers, and forks.
- **The store and saving** (`store_tests`): values by name, sealing and
  indexes, a second process's segments, damaged records, results by kind,
  journals and their locks across processes, collection, and loading a saved
  graph: found done, changed after loading, through unsaved nodes, through
  frozen ones, and with values gone from the store.
- **Sessions and requests** (`database_tests`): the background process seeing
  every earlier write and refusing a second writer, checks before and after
  fixes and restarts, what an edit computes again, removed modules, malformed
  manifests, packages in one worktree, the `usize_bits` rule between
  packages, a new worktree starting near another, a test run that lowers
  nothing after a restart and only what an edit reached after one, holes,
  references,
  dependencies, explaining a name, impact, and both kinds of overlap, with a
  merge, in a git repository.
- **Every other stage's tests** run on the same engine, with the standard
  library as a frozen layer shared by every test in an executable.

A fuzzer that applies random edits to the documents' example packages and
checks after each that every kept result equals what a fresh session
computes is not built yet. It belongs in `stage0/tools/`, run by hand, with
each problem it finds becoming a focused test.

## Not built yet

- **Watching files with FSEvents and inotify,** in place of scanning stamps
  each second.
- **Dependency packages as frozen layers,** once there is a registry.
- **Numbered positions in kept test outcomes,** so that failures are kept
  too.
- **Answering several requests at once.** The background process answers one
  at a time. Queries are pure, so stabilizing sessions in parallel needs no
  change to any stage.
- **The fuzzer** described above.

## Open questions

- **Large projects.** A graph held in memory suits projects up to a few
  hundred thousand definitions. Beyond that, a graph that keeps cold parts on
  disk is a change inside `Engine` alone.
- **Running affected tests unasked.** Test keys stay current once a test
  run has asked for them, so the background process could run the tests whose
  keys changed while the machine is idle, and have their results ready before
  `test` is asked. Whether that is worth the CPU when several agents share a
  machine is not decided.
