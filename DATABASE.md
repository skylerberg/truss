# Truss Code Database

This document designs the code database: the part of the toolchain that
holds every definition being worked on and everything computed from them,
keeps those results current as files change, saves them so that a new
process or a new worktree starts warm, and answers questions about what
depends on what. It follows the decisions in [DESIGN.md](DESIGN.md) and
[GOALS.md](GOALS.md), and serves the stages described in
[TYPECHECKER.md](TYPECHECKER.md) and [CODEGEN.md](CODEGEN.md).

Nothing here is built yet. `stage0/query` holds an in-memory engine that
checks each result again when it is asked for. This design replaces it, and
replaces the code in `codegen/compile` and `bin/truss.ml` that reads and
writes `~/.cache/truss` directly.

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
- keeps the results of expensive steps, such as a test run, a C compile, or a
  solver run, under a key built from exactly the input each one consumed, so
  that every worktree on the machine shares them
- answers questions about dependencies in terms of definitions: what reads
  this definition's interface, what a change affected, what each `todo`
  blocks, and where two worktrees' changes overlap
- runs as one background process per user, serving every worktree, the
  command line, and the language server

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

| Interface | Used by | What it offers |
|---|---|---|
| `Query` | Compiler stages | Declaring inputs and queries, and reading them while a query runs |
| `Engine` | `Database` only | Setting inputs, keeping results current, saving and loading, and walking the graph |
| `Store` | `Engine`, and the exact-key caches in `Database` | Bytes by content hash, results by key, and append-only journals |
| `Database` | The command line, the language server, and agent tools | Opening a worktree and making requests of it |

These rules keep each interface narrow, so that each layer can be replaced
without touching the others:

- **Stages see only `Query`.** A stage never sees the engine, the store, the
  file system, worktrees, git, or another session. A test checks that no
  stage's dune file lists `engine`, `store`, or `database`.
- **Only `Database` changes inputs,** and inputs are the only way anything
  outside the stages reaches them.
- **Answers name definitions, never engine nodes.** A graph question returns
  paths and parts, so a different engine can answer the same questions.
- **Each query's key and value types belong to the stage that declares
  them.** The database knows them only through the encoders the stage
  gives.
- **Clients see only requests and answers.** Whether the session runs in the
  background process or in the client's own process makes no difference to
  them.

## Pushing changes

A change is pushed from where it happened to what it affects. Editing a file
marks the results that read it, and only those are computed again. A result
that comes out the same stops the push there.

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
apart from the scanning "alpha" ones. Truss pushes changes and pulls only
what nobody has asked for yet:

- **A result that has been asked for is kept current.** Once a request asks
  for it, every later change that affects it computes it again, and asking
  for it again costs nothing.
- **A result nobody has asked for is computed when first asked for,** by
  running its query, which asks for what it needs in turn. So nothing is
  computed that nobody wants.

### The graph

The engine's graph has a *node* for each input and for each query result,
named by the query's name and its key. An *edge* runs from a node to each
node it read the last time it was computed, and the engine keeps every edge
in both directions:

- **Edges are learned, not declared.** A query reads through `Query` while it
  runs, and each read adds an edge. Truss's dependencies are not known before
  a query runs: a body depends on what its name lookups found, which depends
  on the names it uses.
- **A read that found nothing is an edge too.** Asking for the constants
  named `count` in a file, and finding none, depends on that answer. Adding
  such a constant later changes the answer, and so reaches the reader, as
  DESIGN.md requires for patterns.
- **The edges in from readers are what a change follows.** The edges out
  serve two purposes: when a node is computed again and reads different
  things, the engine removes it from the readers of what it no longer reads;
  and they answer "why does this depend on that?"
- **A node's value is kept with its hash** when its query is saved (see
  [What is saved](#what-is-saved)), and compared by the query's equality
  otherwise.

DESIGN.md and TYPECHECKER.md list what a result may read: parts of
definitions, interfaces, shapes, lookups by scope and name, body facts, and
manifest entries. Those are the kinds of node a stage declares. The engine
does not know them.

### Keeping results current

Setting an input to a value equal to its old one does nothing. Otherwise:

1. The input takes its new value, and each node that read it is marked
   dirty. Nothing further is marked yet.
2. *Stabilizing* computes the dirty nodes again, in order of *height*, a
   node's distance above the inputs, lowest first, and then by key, so the
   order is the same on every run. A node that comes to read a higher node
   rises above it, as in Incremental.
3. A node computed again whose value equals its old one is clean, and its
   readers are not marked. This is early cutoff.
4. A node whose value changed marks its own readers dirty, and they join the
   queue.
5. When a node being computed reads a node that is dirty or was never
   computed, that node is computed first, then and there. Dependencies that
   appear only when a query runs need nothing more.
6. Stabilizing ends when no node is dirty.

So a change costs the nodes whose values really changed, plus one more
level: each node that read a changed one. That is O(change) as GOALS.md
means it. Editing a function's body computes its resolved form, its checked
body, and its LIR again. If its interface comes out the same, no caller is
touched. If its LIR comes out the same, no test's key changes.

- **Results are recomputed, never patched.** A query is a function of what
  it reads, so computing it again from the same reads gives the same value.
  The engine needs no knowledge of what a query does.
- **Cycles are errors:** a query that asks, directly or not, for its
  own result raises `Cycle` with the queries on the cycle. TYPECHECKER.md
  designs the stages so that ordinary code makes no cycle.
- **What a session keeps.** A session keeps every result some request asked
  for, and everything those results read. A node that nothing kept reads any
  more is dropped from memory when stabilizing ends.

### What a query must be

The engine relies on these, and its tests check each:

- **A query is a pure function of what it reads through `Query`.** It reads
  no global state, no files, no clock, and no other session.
- **Its value is canonical,** as DESIGN.md requires of every stored result:
  no fresh numbering, no hash-table order, no timestamps. Early cutoff
  compares values, so an unstable value would defeat it.
- **Its value holds no functions,** unless the query gives its own equality.
- **Absence is a value, not an exception.** A query reports "no such
  definition" as `None`. An exception that escapes a query is a compiler
  bug: the engine keeps it like a value, so readers see the same exception
  until something it read changes, but never saves it.

## The interfaces

The signatures below are sketches in OCaml. Their exact form is settled when
they are built, but each says everything its layer offers.

### `Query`, for compiler stages

```ocaml
type context
(* What a running query reads through. Nothing else reaches the engine. *)

type ('key, 'value) input
type ('key, 'value) query

type 'a codec = { encode : 'a -> Cbor.t; decode : Cbor.t -> 'a option }

type subject = { path : Path.t; part : Hash.part option }
(* The definition, and the part of it, that a node is about. *)

val input :
  name:string -> show:('key -> string) -> key:'key codec -> value:'value codec ->
  ?about:('key -> subject option) -> unit -> ('key, 'value) input

val query :
  name:string -> show:('key -> string) ->
  ?saved:'key codec * 'value codec ->
  ?equal:('value -> 'value -> bool) ->
  ?about:('key -> subject option) ->
  (context -> 'key -> 'value) -> ('key, 'value) query

val read : context -> ('key, 'value) input -> 'key -> 'value option
val demand : context -> ('key, 'value) query -> 'key -> 'value

exception Cycle of string list
```

- **Inputs are always saved,** so they always have encoders. A query is
  saved only when it gives `saved`.
- **`about` connects a node to a definition.** Graph questions are asked and
  answered by definition and part. A node without a subject, such as a
  lookup by name, is passed through when answering them.
- **Nothing here changes an input or names a session.** A stage cannot
  tell whether it runs in the background process, in a test, or in a
  worktree opened for a git commit.

### `Engine`, for the database

```ocaml
type t

type change = { computed : Query.subject list; changed : Query.subject list }
(* What one stabilization computed again, and what came out different. *)

val create : Store.t -> t
val set : t -> ('key, 'value) Query.input -> 'key -> 'value option -> unit
val stabilize : t -> change
val get : t -> ('key, 'value) Query.query -> 'key -> 'value
(* Computes the result if needed, and keeps it current from then on. *)

val readers : t -> Query.subject -> Query.subject list
val reads : t -> Query.subject -> Query.subject list
val changed_from_base : t -> Query.subject list
(* What differs from the state this engine was shared from. *)

val save : t -> Store.journal -> unit
val load : Store.t -> Store.journal -> t option
val share : t -> t
(* A copy that shares every value and diverges from here on, for a new
   worktree or a commit opened from this one. *)
```

### `Store`, for the engine and the caches

```ocaml
type t
val open_ : string -> t

val put : t -> string -> Hash.digest
val get : t -> Hash.digest -> string option

val find_result : t -> kind:string -> key:Hash.digest -> string option
val add_result : t -> kind:string -> key:Hash.digest -> string -> unit
val add_result_file : t -> kind:string -> key:Hash.digest -> path:string -> unit

type journal
val journal : t -> name:string -> journal
val append : journal -> string -> unit
val records : journal -> string list
val compact : journal -> base:string -> unit
```

### `Database`, for tools

`Database` is a set of requests, each with an answer, encoded in
deterministic CBOR. A client sends them to the background process, or runs
a session in its own process, and the requests and answers are the same
either way (see [Requests](#requests)).

## Inputs

A session's inputs are:

| Input | Key | Value |
|---|---|---|
| A package | Its name | Its manifest: dependencies, grants, and `usize_bits` |
| A module's text | Its module path | The file's bytes |
| The target | The session | The operating system and processor, and the width of `USize` for programs built for it |

The standard library and dependencies are not inputs that change. They are
*frozen layers*, below.

The text of a module is set by the session from the file system, or from git
for a commit (see [Sessions](#sessions)). Lexing and parsing are queries, as
`Workspace` does now: a file is lexed and split again when its text changes,
and a definition whose tree comes out the same, as one that only moved does,
changes nothing that read it.

### Frozen layers

The standard library is built into the compiler, and a dependency is a fixed
version of a package. Neither changes while anyone works, so each is a
*frozen layer*: its nodes are computed once, saved, and shared by every
session that uses it.

- **A layer's key** is the compiler's identity, the package's content hash,
  and the keys of the layers it depends on, so a layer is computed once per
  compiler and version, on any project, as Nix computes a package once per
  set of inputs.
- **A frozen node keeps no edges in from readers.** It never changes, so
  nothing needs to know who read it. A session's own nodes keep edges out to
  it, which is all a graph question needs.
- **What a layer cannot contain.** A grant is in the depending package's
  manifest, so checking that a dependency stays within its grant is the
  session's work, not the layer's. Generic code is compiled for the type
  arguments a session uses, so instances live in the session too.

## Content hashes and the store

Every saved value is encoded in deterministic CBOR and named by its hash, in
DESIGN.md's [hash format](DESIGN.md#the-hash-format), with the format's
version and algorithm in the prefix. The same bytes always have the same
name, so two sessions that compute the same checked form share one copy, in
the store and in memory.

### What the store holds

The store lives in `~/.cache/truss`, or `$XDG_CACHE_HOME/truss` when that is
set, and is shared by every project, worktree, and compiler on the machine.
It holds three kinds of thing:

| Kind | Named by | Written | Directory |
|---|---|---|---|
| Values | The hash of their bytes | Once, by whoever computes them first | `values/` |
| Results of expensive steps | The hash of exactly the input that made them (see [Exact keys](#exact-keys)) | Once | `results/tests/`, `results/proofs/`, `results/objects/`, `results/evaluations/` |
| Journals | A session's name | Appended to by that session's one writer | `journals/` |

- **Values and results are written once, under a temporary name, and renamed
  into place.** Any number of processes can write them at the same time, as
  git's object store allows: two writers of one name write the same bytes,
  since every result is deterministic, and the rename makes either one
  whole.
- **A file is checked against its name when read.** A value whose hash does
  not match is treated as missing and deleted, so a damaged file costs a
  recomputation, never a wrong answer.
- **Each value is one file,** under a two-character directory of its hash,
  as git's loose objects are. Many small files is the known cost of this
  form. Packing values into larger files, as git's packs do, is a change
  inside `Store` alone, when a large project needs it.
- **The store is written with ordinary file operations:** create, write,
  rename, append, flush to disk, and delete. Truss has no foreign code, so the
  compiler written in Truss cannot use SQLite or LMDB. A store it can rewrite
  with the standard library's file capabilities keeps the two compilers'
  stores the same.

### Journals

A session's graph is saved as a journal: a base, which is a value in the
store holding the whole graph at one point, followed by records of each
stabilization's changes since then.

- **Saving costs O(change).** Each stabilization appends one record: the
  nodes that were computed and their new value hashes and edges, the nodes
  that were dropped, and the file metadata of the inputs that changed. The
  base is not rewritten.
- **Compaction folds records into a new base** when the records outgrow the
  base, so the total written stays a constant multiple of what changed, as
  in a log-structured store.
- **Each record ends with its length and hash.** A record cut short by a
  crash fails its check, and loading stops at the last whole record, which
  is a state the session really had.
- **A session's journal belongs to one compiler.** The meaning of a node
  depends on the code of the compiler that computed it, so the journal's name
  includes the compiler's identity: the BLAKE3 hash of its executable,
  remembered by the executable's path, size, and modification time. A new
  compiler starts from its own journal, and still finds every value and
  result whose key it computes the same way, which is what DESIGN.md's
  separate stage versions are for.

### What is saved

Saving every node would write the whole graph's values, most of them cheap
to compute and quick to go stale. A stage marks a query as saved by giving
its encoders. Queries are saved where reading a value back is cheaper than
computing it, and where early cutoff matters after a restart:

- each definition's tree and the hash of its parts
- each definition's resolved form, interface or shape, and checked body,
  with ownership's result
- each file's and definition's diagnostics, and each `todo`'s report
- each instance's LIR, and each test's key

The saved graph is the graph with unsaved nodes taken out: a saved node's
saved edges go to the saved nodes and inputs that it reached through unsaved
ones. After a restart, an unsaved node is computed again when a dirty reader
needs it. It has no old value to compare with, so its readers are computed
again too, up to the next saved node, where its value hash gives early
cutoff again.

### Garbage collection

The store is a cache, and the background process keeps it within a size
budget, 20 GiB unless `TRUSS_CACHE_SIZE` says otherwise:

- **Values reached from a live journal are kept.** A journal is live while
  its worktree's directory exists, and is deleted once the directory is gone.
- **Results are evicted least recently used first.** A result's file is
  touched when it is read, and its modification time is the only record of
  use. That is a fact about the store, not part of any result, so it never
  reaches a stored value.
- **Collection runs in the background** when the store is over budget, with
  the same rename rules as writing, so it never removes a file a running
  build is about to read: a read of a missing value or result computes it
  again.

## Exact keys

The most expensive work in a build is outside the compiler's own queries:
compiling C, running tests, running the solver, and running code while
compiling. Each of these is a pure function of an input that the compiler can
write out completely, so its result is kept under the hash of that input,
with no graph:

| Result | Key | Kept |
|---|---|---|
| A test's outcome | The numbered LIR of everything the test can reach, as CODEGEN.md describes, the code generator's version, and the target | Every deterministic outcome |
| A proof | The query sent to the solver, with every name numbered, and the solver's identity, options, and step limit | Proven or not proven |
| An object file | The C text, the C compiler's identity, and its flags | The object |
| A value worked out while compiling | The numbered LIR of the code that ran, its input, and the target | The value's binary form |

- **These keys are exact.** Everything the result depends on is in the key,
  so a result can be reused by any session, on any branch, by any compiler
  that makes the same key. That is how renaming a definition, or moving it
  to another module, finds its proofs and test results already done.
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
  machine, and is kept. One that ran out of time, ran out of memory, or
  overflowed its stack depends on the machine, its stack size, and the C
  compiler's optimizations, none of which are in the key, so it is reported
  and never kept. A run with sanitizers keeps nothing.
- **Positions in a kept outcome are numbered too.** A failure's message, an
  `echo`, and a panic give positions as an instance's number and a place
  within its definition, as CODEGEN.md's anchors do. Reporting a kept outcome
  turns the numbers into the current names, files, and lines, so after a
  rename or a move, a kept failure shows where the code is now.

Stage0 keeps only a passed test with nothing to show, until outcomes record
numbered positions.

## Sessions

A *session* is one worktree's state: its inputs, its graph, and the results
its requests have asked for. A worktree is a directory with one or more
packages in it, named by its canonical path.

### The background process

One background process per user and compiler serves every session on the
machine, as Gradle's daemon and Bazel's server do. The first command starts
it, and it exits after three hours without a request, the default of both.

- **One process sees every worktree.** That lets a new worktree start from
  another's state, lets the process warn about overlapping work, and lets
  one scheduler share the machine's cores between sessions.
- **Clients connect through a Unix socket** in the store's directory, named
  by the compiler's identity. The command line and the language server are
  thin clients.
- **Without the background process,** as in CI or with `--no-server`, a
  command runs the same session in its own process, against the same store.
  It takes the session's lock file first, so a journal never has two
  writers, and it refuses to run while the background process has that
  session open.

### Watching files

The background process watches each open worktree, with FSEvents on macOS and
inotify on Linux, as IMPLEMENTATION.md plans:

- **Each change sets an input and stabilizes,** so diagnostics are current
  before anyone asks for them.
- **A request first sees every change made before it.** An agent that writes
  a file and runs `truss check` at once must get an answer that includes the
  write, but file events arrive late. The process writes a cookie file in the
  worktree and waits for its event before answering, as Watchman does. Every
  change made before the cookie has then been seen.
- **When events are lost,** as when inotify's queue overflows, the process
  scans the worktree: it compares each file's size, modification time, and
  inode with the journal's, and reads and hashes only the files that differ.
- **Files that are not modules,** such as documentation and build output,
  are not inputs, so changing them does nothing.

### Starting a session

- **A worktree with a journal** loads it, scans the files as above, sets the
  inputs that differ, and stabilizes. That costs O(files) to scan, as
  IMPLEMENTATION.md says, and O(change) for everything else.
- **A new worktree starts from the nearest session.** The process hashes the
  new worktree's modules and picks the open or saved session of the same
  repository and compiler whose module hashes differ in the fewest files. It
  shares that session's graph, sets the files that differ, and stabilizes.
  An agent that creates a worktree from `main` gets a warm session at once,
  instead of checking the whole project from nothing.
- **A worktree with no near session** is checked from nothing, using the
  frozen layers and every exact-key result already in the store.

### Sessions for commits

A session can also be opened for a git commit, with module texts read from
git rather than from files, through `git cat-file --batch`. It starts from
the nearest session, as a new worktree does, and is never written to disk
unless kept for overlap checks. This is how the database compares a branch
that has no worktree, and how it gets the state of a merge base.

### Memory and scheduling

- **Values are shared between sessions in memory.** A saved value is kept
  once, by its hash, however many sessions hold it, and frozen layers are
  shared whole. Two worktrees of one project mostly hold the same checked
  forms, so the second costs little more than its graph.
- **An idle session is saved and dropped from memory** after an hour without
  requests or file changes, and loaded again when next needed.
- **One scheduler runs the work of every session.** The process keeps a pool
  of workers, one per core, for C compiles, test runs, and solver runs, and
  gives the work a waiting client asked for priority over background work. A
  machine running several agents shares its cores between them instead of
  each command starting its own pool.
- **Stabilizing runs one session at a time** in stage0, since each one costs
  O(change). Queries are pure, so stabilizing sessions in parallel, or the
  nodes of one height in parallel, needs no change to any stage.

## Requests

These are what clients can ask a session. Every answer names definitions by
path and part, and positions by file, line, and column, never by node.

| Request | Answer |
|---|---|
| `check` | Every diagnostic in the worktree, and every hole |
| `test` | Each test's outcome, from the store or from running the tests whose keys have no result |
| `build`, `run` | A program, or its run |
| `explain` | At a position: the type of an expression, what a name means, and the signature it refers to |
| `references` | Every definition that reads a definition, or one of its parts |
| `dependencies` | Every definition a definition reads, by part |
| `impact` | What a change affected (see below) |
| `holes` | Each `todo`, with its type, the names in scope, and the tests, proofs, and programs it blocks |
| `overlap` | Where this worktree's changes meet another's (see [Parallel work](#parallel-work)) |
| `sync` | Nothing, once every change made before the request has been seen |

Results asked for through these requests are kept current from then on, as
[Keeping results current](#keeping-results-current) describes. Running tests
stays a request: their keys stay current, but a test runs only when asked.

### Impact

GOALS.md asks for tools that show agents and reviewers what each change
affects, and the signatures of what it touched. `impact` compares the
worktree with a base, `main`'s merge base unless another commit is named,
and answers:

- **What changed,** by definition and part: which interfaces, contracts,
  bodies, defaults, shapes, and invariants differ.
- **What was checked again, and what came out different.** The push itself
  records this: every node it computed, and every one whose value changed.
  A caller that was checked again and came out the same is listed apart from
  one whose checked form or diagnostics changed.
- **The signatures to review.** Every definition whose interface or contract
  changed, and every definition that reads one of those, with their
  signatures, which DESIGN.md says carry everything important about code.
- **The tests whose keys changed,** which are the only tests the change can
  affect.

The base's state comes from the session for that commit, so `impact` costs
what pushing the difference costs: O(change).

### Holes and what can ship

Whether `main` can reach a `todo` or an `echo`, and which tests a hole
blocks, are queries over what each definition calls, kept current like any
other. A build that refuses a program names the hole and the chain of calls
that reaches it, and `holes` lists, for each one, everything it blocks.

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

Each session has a *base*: the commit it is compared with, which is its
merge base with `main` unless another is named. The session starts from the
base's session, and keeps the base's value of every node that has changed
since, so it always knows its *changes*: the nodes whose values differ from
the base's, and nothing that changed and then changed back. Keeping them
costs memory in proportion to the changes, and each stabilization updates
them for what it changed. Two worktrees with the same base overlap where:

1. **Both changed one node.** This covers editing the same part of the same
   definition, even on different lines, and two additions that answer one
   lookup, such as the two `find` methods, which both change the members of
   `List` named `find`.
2. **One changed a node that the other's changes read.** B's new call reads
   the interface of `parse`, and A changed that interface.

Each overlap is reported with the definitions and parts on both sides and
what each side did, in the terms of `impact`. Both sets of changes are
O(change) to find, and comparing them is O(change) too.

### When overlaps are found

- **As work happens.** The background process sees every worktree of a
  repository. After each stabilization, it compares the session's changes
  with the other open sessions', and `check` lists the overlaps it found, in
  their own section, as does the language server. Overlaps are not
  diagnostics: nothing is wrong with either worktree's code, and every
  diagnostic in Truss is an error.
- **For a session against a branch,** `overlap` names the branch, and the
  database opens a session for its commit.
- **For an exact answer,** `overlap --merge` merges the two trees with
  `git merge-tree`, opens a session for the result, and reports every
  diagnostic that is in the merge but in neither side. The rules above find
  where work meets; this finds whether it breaks.

Two worktrees with different bases, as when one has merged a newer `main`,
are compared through a session for the merge base of the two, which comes
from git. The database pushes each worktree's differences from it on a
session shared from it, and compares the two sets of changes the same way.

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

- **What runs again.** A test sets inputs, stabilizes, edits one, and
  asserts exactly which queries were computed again and which changed, from
  the engine's log. There is one for each row of TYPECHECKER.md's table of
  everyday edits.
- **Early cutoff stops the push.** A query whose value comes out the same
  leaves its readers uncomputed.
- **Edges follow reads.** A query that stops reading an input is not
  computed again when that input changes.
- **A read that found nothing is an edge.** Adding the missing thing
  computes the reader again.
- **Saving changes nothing.** A session saved and loaded gives the same
  answers as before, and edits after loading compute the same queries again
  as edits before saving.
- **Encoders round-trip.** For each saved query, decoding an encoded value
  gives an equal value, and encoding is canonical.
- **The store survives damage.** A value with the wrong hash is missing, and
  a journal cut off partway loads to its last whole record.
- **Exact keys.** Renaming a definition keeps its tests' keys, and changing
  the target changes them. A timed-out test keeps no result.
- **Requests see earlier writes.** A file written just before a request is
  in its answer.
- **Overlaps.** Each of the three examples in
  [Parallel work](#parallel-work) is reported, and two worktrees that
  change unrelated definitions report none.
- **The layers stay apart.** No stage's dune file lists `engine`, `store`, or
  `database`.

A tool, `stage0/tools/incremental`, is run by hand: it applies random edits
to the documents' example packages and checks after each that every kept
result equals what a fresh session computes. Each problem it finds becomes a
focused test.

## Open questions

- **Large projects.** One file per value, and a graph held in memory, suit
  projects up to a few hundred thousand definitions. Beyond that, packed
  values and a graph that keeps cold parts on disk are changes inside
  `Store` and `Engine`.
- **Running affected tests unasked.** Test keys are always current, so the
  background process could run the tests whose keys changed while the
  machine is idle, and have their results ready before `test` is asked.
  Whether that is worth the CPU when several agents share a machine is not
  decided.
