# Truss Code Database

This document describes stage0's code database: the part of the toolchain
that holds every definition being worked on and everything computed from
them, keeps those results current as files change, keeps each result so no
state computes it twice, and answers dependency questions. It serves the
stages of [TYPECHECKER.md](TYPECHECKER.md) and [CODEGEN.md](CODEGEN.md), and
the `truss` command line ([CLI.md](CLI.md)) is its only client: the database
is a library, and every command and report is the command line's.

GOALS.md asks that a change cost O(change) for building, testing, and
verifying, and that agents can see the effects of their changes and where
they overlap with other agents'. The database:

- holds the inputs of every project being worked on
- maintains each result a driver demanded, and every result it reads, by
  pushing each change, one phase at a time, to the readers of values that
  really changed
- keeps each saved result as a fact under the key of its reads, so another
  worktree, a commit, a branch gone back to, or a new process finds it
- writes each state as a difference over an earlier one, so a worktree, a
  commit, or a trial costs only its changes
- keeps the results of expensive steps, such as a test run or a C compile,
  under a key of exactly their input
- answers questions about dependencies in terms of definitions
- runs as a background process for each project being worked on

It decides no meaning of code, holds nothing that cannot be rebuilt from the
files, keeps no history, and does not yet share results between machines.

## Structure

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

`Query` and `Engine` are two views of one implementation, `Incremental`,
which nothing else names. These rules keep each interface narrow, so each
layer can be replaced without touching the others:

- **Stages see only `Query`,** never the engine, the store, files, git, or
  another session.
- **`Session` knows no stage and no project.** Manifests, packages, and
  commits are the client's concepts.
- **`Database` knows the project, and no stage beyond it.**
- **A driver sets a stage's input through its session,** with `Database.set`,
  the one way anything outside the stages reaches them.
- **A driver holds no engine.** A trial, a commit, a published package, and the
  standard library's own state are each a session like any other.
- **A session's files are one abstraction:** a worktree, a commit, and texts in
  memory each give paths, a stamp per file, and texts.
- **Answers name definitions, never engine nodes,** so another engine could
  answer the same questions.
- **Each query's key and value types belong to its stage;** the database only
  compares and saves them.
- **Code generation does not see the store;** a test run is handed functions
  that find and keep results by key.
- **Whether a session runs in the background process or the client's makes no
  difference,** since the background process runs the client's own code.

## The engine

### The graph

An engine is one *state*: one set of inputs and the results computed from
them. Its graph has a node for each input and query result, and an edge from
a node to each node it read when last computed, kept in both directions.

- **Edges are learned, not declared,** since a body depends on its name
  lookups' results, which depend on the names it uses.
- **A read that found nothing is an edge too,** so adding a constant named
  `count` reaches every reader that looked for one.

### Phases

Every query has a phase, and reads only its own phase and earlier ones;
reading a later phase is an error at the read. A phase is declared with the
phases it may read, and the compiler declares its own in `Phases`: syntax,
declarations, resolution, interfaces, bodies, package checks, proofs,
verdicts, diagnostics, lowering, linking, recursion, and keys.

Phases let a change stop exactly where it stops mattering: when a phase is
brought up to date, every earlier phase is final, so the engine knows which of
its results read something that really changed.

### Bringing a state up to date

A clock orders changes, and each node records when its result last changed
and when it was last found current. Setting an input to an equal value does
nothing. Otherwise:

1. The input takes its value, and its readers are queued under their phases.
2. The engine takes the first phase with anything queued, and marks each
   queued result and its readers within the phase.
3. Each marked result is brought up to date: its dependencies first, in the
   order it read them. If one changed after the result was last found
   current, the result is looked for as a fact or computed again, stopping at
   the first such read, since a later read may not be made once an earlier one
   gives another answer. Otherwise it is current without being computed.
4. A result that comes out different queues its readers in later phases; one
   that comes out the same queues nothing. This is early cutoff.
5. The engine continues to the next phase with anything queued.

So editing a function's body computes its tree, resolved form, interface,
and checked body again, and its interface comes out the same, so its callers'
bodies, in a later phase, are not marked at all. The engine counts the
results it marks, finds current, computes, finds as facts, and copies, and
tests compare the counts for one edit in a small package and a large one.

- **A result a driver demands becomes a root, and the engine maintains every
  necessary result,** a root or a result a necessary result reads, the term of
  Jane Street's Incremental. Demanding a root again costs nothing.
- **An unnecessary result is not computed.**
- **A driver can observe a result without making it a root,** as comparing two
  states does, so a question does not change what a state maintains.
- **A read outside any query first brings the engine up to date through its
  target's phase,** so a driver never sees a result a change has not reached.
- **A result whose query raised a fatal exception stays queued,** so it is never
  written as current.
- **Results are recomputed, never patched,** so the engine needs no knowledge
  of a query's semantics.

Jane Street's Incremental pushes changes in order of each node's height in the
graph. Truss's phases are that order, fixed by the compiler's structure, so
heights are never maintained and no query is stopped and restarted. Within a
phase the engine marks as Adapton does, and brings each marked result up to
date when it is needed. A system that recomputes everything a change can
reach spends time on everything that could be affected; one that checks each
result's inputs when asked, as Salsa does, spends time on everything asked
for.

### Bases

An engine holds its differences from its *bases*, which are frozen engines:
inputs it sets, results it computes, and copies of base results a change
reached. So ten worktrees of one project cost one project and ten changes,
starting a state costs nothing, and comparing two states costs their
differences. That turns fast inference into throughput: trying a change is
the basic thing an agent does, and each trial is a cheap, independent state.

- **A base never changes;** freezing brings an engine up to date and makes it
  one.
- **A base's result is copied when a change reaches it,** and only a copy whose
  result differs has its base's readers copied in turn.
- **A base is fixed, such as the standard library, or an earlier state.**
- **An engine nothing refers to is freed,** with everything it owns.

### Collecting unnecessary results

An unnecessary result of the engine's own is collected, with each result only
it read, once no query is running. Roots, set inputs, and copies of base
results are not collected. So once a state is up to date every result it holds
is current: a result a change reached is brought up to date or collected,
never left, since a state written with it would be opened with it taken for
current.

### Cycles

A query that asks for its own result raises `Cycle` with the queries on the
cycle, and every query on it, and every reader of one, has the cycle as its
result, so a result never depends on which query met the cycle first. The
read that closed the cycle is an edge too, so removing the cycle reaches
every query on it. TYPECHECKER.md keeps ordinary code free of cycles.

### Query declarations

A stage declares each query with its name, key and value types, function,
and phase, whether its bytes are stored, whether a state that never held the
result looks for it too, and its subject, the definition and part graph
questions are answered by. A query is declared when its module is
initialized, and declaring one after the store is open is an error, since a
state opened earlier would have dropped its results and their readers.

### Query requirements

- **A query is a pure function of its reads,** with no global state, files,
  clock, or other session. Once the compiler is Truss, the language checks
  this: a query whose only capability reads the database can do nothing else.
- **Its value is canonical,** since early cutoff and fingerprints compare
  values.
- **Its value holds no functions,** unless it gives its own equality. A value
  with a function is *opaque*: its fingerprint is a nonce, it is never a fact,
  and its readers are computed again whenever it is.
- **It answers for any key,** such as `None` for a key that no longer names
  anything.
- **An exception is an outcome,** kept like a value with a fingerprint of its
  constructor and arguments, so a result that raises as before stops a change.

## Inputs

An input is a file's text, and little else: a root's files, the roots, each
file's stamp, unavailable registry packages, the keys a driver wants, and the
solver's answers. A project's packages, modules, and manifest errors are
queries over the files, in `Project`, of the first phase, so a stage cannot
tell a project's package from a registry package or the standard library. A
*root* is a tree of files: the project, the standard library, or a registry
package's files.

- **An edit to a module's text changes one input,** read only by that module's
  text query.
- **Nothing is derived by hand.** The database sets a file's text when its stamp
  changed and removes it when the file is gone, and keeps no list of packages
  or modules of its own to bring in line.
- **Lexing and parsing are queries,** so a definition whose tree comes out the
  same changes nothing.

## Fingerprints and facts

A query is a pure function of its reads, so its result is a *fact*: the value
with each dependency and its value at the time. A fact is kept by content, not
place, so any state that reads the same finds it, whichever worktree, branch,
or process computed it, as Bazel and Nix keep build steps. The graph a state
holds is an index, rebuildable from the facts and the files.

### Fingerprints

A node's fingerprint is the BLAKE3 hash of its value's bytes.

- **BLAKE3 is written in stage0,** from the specification and tested against
  the official vectors.
- **Content is hashed in the default mode, and keys in the derive-key mode,**
  each kind under a context naming it. A key's fields are a deterministic CBOR
  array, which prefixes every field with its length, so two lists never share
  an encoding, and the modes keep every key disjoint from every plain hash and
  every other kind of key. A changed key format takes a new context, so old
  keys stop matching instead of being misread.
- **A fingerprint is computed when first needed,** and a result computed again
  in a state opened from the store is compared with its old fingerprint, so
  nothing is read back only to be compared.
- **A value's bytes depend only on the value.** Stage0 uses OCaml's marshaling
  without sharing, since marshaling otherwise records which parts are one
  block in memory, which differs between a value built from results in memory
  and one built from results read back, and would give one value two
  fingerprints.
- **The bytes mean something only to the compiler that made them,** since an
  encoder for each result type would cost thousands of lines to keep up. Two
  equal values can still marshal differently, as a balanced tree can, at the
  cost that a fact is not found. The compiler in Truss will derive a canonical
  encoding.

### Facts

A fact's key is the compiler's identity, the hash of its executable; the
query's name and key; and each node the result read, in order, with its
fingerprint. A result that raised or is opaque, or read an opaque result, is
no fact.

- **A fact found is the result,** since computing it now would make the same
  reads and give the same value, whichever state the reads came from.
- **A marked result is looked for as a fact before it is computed,** which makes
  going back free: a branch switched back to, an undone edit, or a commit
  another worktree checked finds each result done.
- **A portable query's result is looked for even by a state that never held
  it.** The store keeps, once per key, the names of its first computation's
  dependencies, and a new result is looked for under those. This is how a
  state reaching a standard library instance or a test's key finds what
  another state computed. Code generation's queries are portable; a type
  checker's result is found through the state its worktree starts from, so its
  reads are not kept twice.
- **The key holds the compiler's identity** because stage0 is one version.
  Once the compiler is Truss, a stage's version can be the key of everything
  its own code reaches, so a compiler change leaves exactly the facts its
  changed code could not have made.

### Which results are stored

A query's bytes are stored where reading them back is cheaper than computing:
lookups, each definition's tree, resolved form, interface, checked body,
diagnostics, and code generation's outputs. An unsaved result, such as a
file's tokens, is part of a state with its fingerprint and dependencies, so a
change stops at it in a state opened from the store; only its value is
computed again where needed, with the fingerprint it had. A fixed base is
written once for a compiler's identity and read by every state over it, so
it stores the value of every result whose value holds no function, unsaved
or not: otherwise each state would compute those results again as its own.
A driver's read of a fixed base's node makes no root in the state, since the
node never changes and is never collected.

## States in the store

### Artifacts

A state is written as an *artifact*, a value in the store named by its hash:
a whole state, of every node its roots and set inputs reach apart from its
fixed bases, or a difference over an earlier artifact, of the nodes that
changed since. An artifact never changes, so it names a state for good, and
many states can be differences over one.

- **Writing costs O(change):** `Engine.write` writes a difference over the
  artifact the engine was opened from or last wrote.
- **A copy that came out as its base's result is not written,** unless an
  earlier difference holds another result for it.
- **A node is written with its first reader,** so a node's dependencies are
  found when the state is opened.
- **Values are flushed before a pointer names an artifact,** so a pointer
  never names a value a crash lost.

### Opening a state

`Engine.open_` follows an artifact's chain back to its whole state, which is a
frozen base shared by every engine opened from it in a process, held weakly.
The differences after it are the engine's own. A node a difference collected
keeps its place, empty, so the whole state's older result is never read in its
stead. Opening reads no value.

- **An input whose value the store lost is an error,** `Engine.Lost`, since a
  result can be computed again and an input cannot. The database then discards
  every open state and runs the command again from the files.
- **A node that cannot be checked is left out:** a node of a query this
  compiler does not declare, one that read a node not found, and their
  readers.

### Folding

A chain is folded into one whole state when its differences hold more than
half as many nodes as the whole state, and more than 256, so the nodes a
session holds and the data read to open a state stay within a constant of
the changes. Folding costs the state's size, so the background process folds
while no request waits, and a command waits for a fold only when the
differences have grown to twice the whole state.

### Package artifacts

A package whose sources never change is checked once, written whole, and found
by the key of its sources, as a fixed base under every state that uses it.
The standard library is one: its key is the compiler's identity, so the first
process to need it checks every module, and every later process opens it with
one lookup.

**Work on the standard library** edits a fixed base, and each edit makes a new
compiler identity, under which no fact is found. So `Database.open_library`
opens the library as a state of its own, whose inputs are the sources built
into the compiler, with facts kept under the compiler's version: a digest of
its source and build toolchain, leaving out tests, tools, and the library's
text. An edit to the library keeps the version and recomputes only its
dependents.

## The store

The store lives in `$TRUSS_CACHE`, else `$XDG_CACHE_HOME/truss`, else
`~/.cache/truss`, and is shared by every project, worktree, and compiler on
the machine. Values, facts, exact-key results, and package artifacts are in
segments; object files, a registry package's files, and solver answers are a
file or directory each, since a linker reads objects by path; and pointers
name each worktree's state. Everything but a pointer is named by its content
or its inputs, and never changes.

### Segments

Values and results live in append-only segment files, as Bitcask stores
them, with sorted indexes like git's pack files. One file per value would not
do: a project of a hundred thousand definitions keeps millions of small
values, and a file costs far more in inode, directory entry, and time to open
than such a value takes.

- **A record** is a kind byte, a 32-byte key, the length, the value, and a
  checksum. A result's key is derived from its kind and key.
- **Each writing process has a segment of its own,** locked while it writes, so
  writers need no lock to append. A value two processes add is in both, which
  is harmless, since its name is its hash.
- **Records are written a megabyte at a time,** so adding one is not a system
  call.
- **A sealed segment has an index** of its keys sorted, read into memory as one
  string and searched by halving. A killed process leaves its segment
  unsealed, and such a segment is read by scanning.
- **A lookup that misses looks again** for segments other processes made, at
  most every twenty milliseconds, since a result another process added a
  moment ago is only computed again.
- **A damaged or cut-off record is missing,** so a crash costs a recomputation,
  never a wrong answer.
- **Small segments are gathered into one,** by a process that opens the store
  and by the background process each minute.
- **The store uses ordinary file operations** and file locks. The compiler in
  Truss cannot use SQLite or LMDB, since Truss has no foreign code, and a store
  written with the standard library's file capabilities keeps the two
  compilers' stores alike.

### Pointers

A pointer is the one thing in the store that is replaced: a few bytes under a
name, written beside itself and renamed into place after every value it names
is flushed, framed with its length and a checksum. A session's pointer is
text, of the writing version, its artifact, and each file's fingerprint, so
any compiler can read any pointer. A pointer has one writer, holding its lock,
and is named by the compiler's identity and the worktree.

### Garbage collection

The background process keeps the store within a budget, 20 GiB unless
`TRUSS_CACHE_SIZE` says otherwise, checking every ten minutes:

- **A live state's artifacts are kept,** with every value they name, while its
  worktree's directory exists. A gone worktree's pointer is removed every
  minute, since a new worktree looks through every pointer for its nearest
  state.
- **Only this compiler's states are read,** since an artifact's bytes mean
  something only to its version. Another compiler finds its state gone and
  starts from its files.
- **Results in use are kept:** those this process read or added, and those in
  segments written in the last week.
- **Survivors are copied into a new segment,** and segments another running
  process is writing are left alone.

## Exact keys

The most expensive work is outside the compiler's queries: compiling C,
running tests, running the solver, and running code while compiling. Each is a
pure function of an input the compiler can write out completely, so its
result is kept under the hash of that input: a test's outcome under the key of
everything it can reach, code generation's version, and the target; an
object file under the C text, the compiler's identity, and its flags; a
solver answer under the canonical query's text and the solver's identity and
options; and a template check under the key of the code that ran. Everything
the result depends on is in the key, so any session on any branch reuses it,
and renaming a definition finds its test results done.

Only a test that passed with nothing to show is kept. A failure's message and
an `echo` give positions, which the key leaves out, and a test that ran out of
time, memory, or stack depends on the machine, which is not in the key.

## Sessions

A *session* is one project's state in one worktree, with its engine, the
pointer that names its state, and its manifests' problems. It is a project's,
not a worktree's, because a path means one thing only within one project: two
projects in one repository may each have a package called `tools`.

- **The project's root is found from the files alone,** as PACKAGES.md says,
  with git asked nothing, so a project builds the same from an archive.
  Directories starting with `.`, and `_build` and `node_modules`, are passed
  over.
- **An error between manifests,** such as a cycle of packages, is a problem of
  the session.
- **The same project in two worktrees is two sessions,** compared for overlaps.

### Registry packages

The build's registry packages and their versions are a query,
`Project.selection`, over the lock file and the records of the packages it
names; the database never chooses a version.

- **A registry package's files are inputs of a root of their own,** named by
  their hash, fetched into the store if missing and kept only if they have that
  hash. The selection names each package whose files are not inputs yet, and
  the database sets them and asks again, since a package's record can name
  more.
- **A registry package is a package like any other to the stages,** computed
  when read, so a project pays only for the parts it uses.
- **Other versions are tried in a trial,** which `truss upgrade` compares with
  the project's.
- **A published version can be had in an engine of its own,** since a package
  and its last version have the same paths and cannot share a state.
  `truss publish` compares a package with its last version this way.

### The background process

Each project has a background process for each compiler, as each workspace
has a Bazel server. The first command starts it, detached, and it exits after
three hours without a request, when its directory is gone, or within a minute
of its compiler being rebuilt.

- **Commands in different worktrees are answered at once,** since each
  worktree's project has a process of its own, so no agent waits for
  another's test run. Commands in one worktree are answered one at a time.
- **The processes share the store and nothing in memory,** and find as facts
  the results another computed.
- **It holds nothing that is not in the store;** a session is written when its
  command is done.
- **Clients connect through a Unix socket,** named by the compiler's identity
  and a hash of the project's root. A long path puts it in `/tmp/truss-UID`,
  used only if it is the user's alone, since the data on the socket is
  marshaled, and another user's socket there could run code as this one.
- **Requests and answers are marshaled OCaml values,** safe because both ends
  are the same program. The handler is the client's own code, so a command's
  answer is the same in the background process and its own.
- **`--no-server` runs a command in its own process,** taking the session's
  pointer lock first, and refuses while the background process has the
  session open.

### Watching files

- **A command scans its worktree before it is answered,** comparing each file's
  size, modification time, and inode with its stamp, so it always sees every
  change made before it, with no need for cookie files as Watchman uses.
- **A file's stamp is set only once its text is,** so a scan that fails partway
  leaves nothing that looks read and was not.
- **While idle, the process scans every open worktree each second,** so
  diagnostics and overlaps are current before anyone asks.
- **Scanning is O(files) in stamps.** FSEvents and inotify would make it
  O(change), but stage0 has no C bindings for them yet, and since a command
  scans anyway, they would only change how soon the process hears of a change.

### Starting a session

- **A worktree whose pointer names a state** opens it, scans, sets the inputs
  that differ, and brings it up to date: O(files) to scan and O(change) for
  the rest.
- **A new worktree starts from the nearest saved state:** the state whose
  pointer's file fingerprints differ from its files in the fewest. Its first
  write is a difference over that state's artifact, so an agent that creates
  a worktree from `main` gets a warm session at once.
- **A worktree with no state near it** is checked from the files, over the
  standard library's artifact, and still finds every fact computed from the
  same reads.
- **An idle session is written and dropped from memory** after an hour.

A session can also be opened for a git commit, read through `git ls-tree` and
`git cat-file`, from the nearest saved state, and never pointed at. A *trial*
starts from another session's state with some files replaced, and is never
saved: a rename, a merge, and an upgrade are each checked in one.

## Questions

Tools ask a session questions whose answers name definitions by path and part,
never nodes: a session's diagnostics, a definition's dependencies and
dependents, the definitions a root reaches, a name's meaning, the changes
since a commit, where two worktrees meet, a trial, and where build results are
kept. A result a command demands is a root from then on. A graph question
first checks every package of the sessions it reads. A part of a definition
depends on a part of another when a node about the first reads the node about
the second, directly or through nodes about no definition, such as lookups.
The path does not continue through a fixed base's node, such as one of the
standard library's own lookups. `dependencies` follows reads from the definition's nodes, and
`dependents` follows readers from the target's nodes, by the same rule.

- **Comparing two states** compares the nodes either holds itself where they
  share a base, by fingerprint and then by value, computing a node in the
  other state where it has none.
- **A hole's type and names in scope** come from the type checker's tables and
  resolution, which records the names in scope at each `todo`, so there is one
  account of scope.

## Parallel work

GOALS.md names sorting out conflicts between agents as one of the things that
will dominate development time. Git sees only lines; the database sees each
change's effects, so it finds overlaps that merge cleanly and break once
merged: one agent changes `parse` to return a `Result` while another adds a
call to it; two agents each add a method `find` to `List` in different files;
one strengthens an invariant another's new function relies on.

**Overlaps.** For two worktrees, the database compares each with their merge
base, and each node that differs is that worktree's change. They overlap
where both changed one node, which covers two additions that answer one
lookup, such as the members of `List` named `find`, and where one changed a
node that depends on a node the other changed. Each overlap names the
definitions and parts on both sides.

- **As work happens,** `check` lists overlaps with every other worktree of the
  repository that a background process serves, reading each through the state
  its process last saved. Overlaps are not diagnostics, since nothing is wrong
  with either worktree's code.
- **`overlap --with BRANCH`** compares with a branch's commit.
- **`overlap --merge`** merges the two with `git merge-tree`, checks the result
  in a trial, and reports every diagnostic in the merge but in neither side.
  Uncommitted work goes in through a commit made with an index of its own, so
  the worktree is untouched.

## Checking the engine

A database that returns a stale result is worse than none, and an engine can
go wrong in too many ways to think of one at a time, so it checks itself
against a new engine with the same inputs.

- **`Engine.audit`** brings an engine up to date, computes every result it holds
  in a new engine with the same inputs and no facts, and reports each that
  differs. With `~flat:true` the bases' results are checked too.
- **Every test audits** every engine it made, when it ends, so each stage's test
  also tests that the database kept results current and that the stage's
  queries are pure functions of their reads.
- **Counts of work.** Tests make the same edit in a package of four modules and
  one of forty, and assert equal counts of results marked, computed, and
  found, which are the same on every machine.
- **`stage0/tools/engine_fuzz`** makes random graphs of queries and random
  steps, audits after each, and prints the fewest steps that still fail.
- **`stage0/tools/database_timing`** times a first check, a write, an open, and
  edits, for work the counts do not show.

## Not built

- **Sharing between machines.** Keys are made so sharing needs no change to
  them. It matters most where sessions are short, as an agent in a fresh
  container or CI. It is left out because of the claims a result makes: a
  forged "proven" or "passed" would skip exactly the checks Truss exists to
  make, and an object file is code that will run. So a result from another
  machine will be used only when signed by a trusted key, as Nix's
  `trusted-public-keys` require, the registry's key by default.
- **A specified encoding for values,** so a fingerprint does not depend on the
  compiler that marshaled it.
- **Test results as facts with the code that ran,** which is far less than what
  a test can reach, and would run fewer tests after an edit.
- **Every deterministic outcome of a test kept,** once a failure's positions are
  recorded relative to definitions.
- **A constant's value kept under an exact key.**
- **A solver's answers in segments,** not a file each.
- **A package being worked on as an artifact of its own,** and **registry
  packages as artifacts,** each a fixed base, found in one lookup.
- **Collecting registry packages** no lock file names any more.
- **Artifacts and indexes read in part,** so opening a state or the store costs
  the change, not the state's size.
- **Collection without the background process,** so a store used only with
  `--no-server` does not grow until deleted.
- **Each stage's version in keys,** in place of the compiler's identity.
- **Merging definition by definition,** which Truss's lack of comments, one
  format, and no meaning in definition order would allow.
- **Watching files with FSEvents and inotify.**
- **Answering several requests about one worktree at once.**
- **Sharing a whole state in memory between worktrees.**
- **Unrooting every stale root,** such as a deleted test's key.
- **A fingerprint summary written in O(change).**
- **The rules that span a package as many results,** so their cost follows the
  change, not the package.
- **Questions answered from an index.** A graph question scans every node of
  the state to find the nodes about its definitions; an index from each
  definition to its nodes would answer in the size of the answer.
- **Running affected tests unasked** is not decided, since it costs CPU that
  several agents share.
