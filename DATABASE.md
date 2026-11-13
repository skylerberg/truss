# Truss Code Database

Stage0's code database holds every definition being worked on and everything
computed from them, keeps those results current as files change, keeps each
result so no state computes it twice, and answers dependency questions. It
serves the stages of [TYPECHECKER.md](TYPECHECKER.md) and
[CODEGEN.md](CODEGEN.md). The database is a library, and the `truss` command
line ([CLI.md](CLI.md)) is its only client.

GOALS.md asks that a change cost O(change) for building, testing, and
verifying, and that agents can see the effects of their changes and where
they overlap with other agents'. The database:

- maintains each result a driver demanded, pushing each change, one phase at
  a time, to the readers of values that really changed
- keeps each result as a fact under the key of its reads, so another
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

Each interface is narrow, so each layer can be replaced without touching the
others:

- **Stages see only `Query`,** never the engine, the store, files, git, or
  another session.
- **`Session` knows no stage and no project.** Manifests, packages, and
  commits are the client's concepts.
- **Answers name definitions, never engine nodes,** so another engine could
  answer the same questions.

## The engine

An engine is one *state*: one set of inputs and the results computed from
them. Its graph has a node for each input and query result, and an edge from
a node to each node it read when last computed. Edges are learned, not
declared, and a read that found nothing is an edge too, so adding a constant
named `count` reaches every reader that looked for one.

**Every query has a phase,** and reads only its own phase and earlier ones.
When a phase is brought up to date, every earlier phase is final, so a change
stops exactly where it stops mattering. Jane Street's Incremental pushes
changes in order of each node's height in the graph; Truss's phases are that
order, fixed by the compiler's structure, so heights are never maintained.

**A change is pushed with early cutoff.** A changed input queues its readers;
each queued result is brought up to date, its dependencies first; and a
result that comes out the same as before queues nothing. So editing a
function's body computes its tree, resolved form, interface, and checked body
again, and its interface comes out the same, so its callers' bodies are never
marked. Tests make the same edit in a small package and a large one and
compare the counts of results computed.

- **Only necessary results are maintained:** the roots a driver demanded and
  the results they read, the term of Jane Street's Incremental.
- **Results are recomputed, never patched,** so the engine needs no
  knowledge of a query's semantics.
- **A cycle between queries** gives every query on it the cycle as its
  result, so a result never depends on which query met the cycle first.

**An engine holds its differences from its bases,** which are frozen engines,
such as the standard library or an earlier state. So ten worktrees of one
project cost one project and ten changes, starting a state costs nothing, and
comparing two states costs their differences. Trying a change is the basic
thing an agent does, and each trial is a cheap, independent state.

### Query requirements

- **A query is a pure function of its reads,** with no global state, files,
  clock, or other session.
- **Its value is canonical,** since early cutoff and fingerprints compare
  values.
- **Its value holds no functions,** unless it gives its own equality.
- **It answers for any key,** such as `None` for a key that no longer names
  anything.

## Inputs

An input is a file's text, and little else. A project's packages, modules,
and manifest errors are queries over the files, so nothing is derived by
hand, and a stage cannot tell a project's package from a registry package or
the standard library. Lexing and parsing are queries, so a definition whose
tree comes out the same changes nothing.

## Facts

A query is a pure function of its reads, so its result is a *fact*: the value
with each dependency and its fingerprint at the time. A fact is kept by
content, not place, so any state that reads the same finds it, whichever
worktree, branch, or process computed it, as Bazel and Nix keep build steps.
The graph a state holds is an index, rebuildable from the facts and the
files.

- **A fingerprint is the BLAKE3 hash of a value's bytes,** and a value's
  bytes depend only on the value.
- **A fact's key holds the compiler's identity,** the hash of its
  executable, because stage0 is one version. Once the compiler is Truss, a
  stage's version can be the key of everything its own code reaches, so a
  compiler change leaves exactly the facts its changed code could not have
  made.
- **A result is looked for as a fact before it is computed,** which makes
  going back free: a branch switched back to, an undone edit, or a commit
  another worktree checked finds each result done.

## States in the store

A state is written as an *artifact*, a value in the store named by its hash:
either a whole state or a difference over an earlier artifact. An artifact
never changes, so it names a state for good, and writing a state costs
O(change). A chain of differences is folded into a whole state once it holds
more than half as many nodes as the whole, so opening a state stays within a
constant of its changes.

**A package whose sources never change is a fixed base,** checked once,
written whole, and found by the key of its sources. The standard library is
one: the first process to need it checks every module, and every later
process opens it with one lookup.

## The store

The store lives in `$TRUSS_CACHE`, else `$XDG_CACHE_HOME/truss`, else
`~/.cache/truss`, and is shared by every project, worktree, and compiler on
the machine. Everything in it but a pointer is named by its content or its
inputs, and never changes.

- **Values live in append-only segment files,** as Bitcask stores them, with
  sorted indexes like git's pack files. One file per value would not do: a
  large project keeps millions of small values, and a file costs far more to
  create and open than such a value takes.
- **Each writing process has a segment of its own,** so writers need no lock
  to append. A value two processes add is in both, which is harmless, since
  its name is its hash.
- **A damaged or cut-off record is missing,** so a crash costs a
  recomputation, never a wrong answer.
- **A pointer is the one thing that is replaced:** it names a worktree's
  state, and is renamed into place after every value it names is flushed.
- **The store uses ordinary file operations,** not SQLite or LMDB, since the
  compiler in Truss will have no foreign code.
- **The background process keeps the store within a budget** by keeping live
  states and recently used results and copying them into new segments.

## Exact keys

The most expensive work is outside the compiler's queries: compiling C,
running tests, running the solver, and running code while compiling. Each is
a pure function of an input the compiler can write out completely, so its
result is kept under the hash of that input:

| Result | Key |
|---|---|
| A test's outcome | Everything the test can reach, code generation's version, and the target |
| An object file | The C text, the C compiler's identity, and the flags |
| A solver answer | The query's canonical text, the solver's identity, and its options |
| A template check | The code that ran |

Everything the result depends on is in the key, so any session on any branch
reuses it, and renaming a definition finds its test results done.

## Sessions

A *session* is one project's state in one worktree. It is a project's, not a
worktree's, because a path means one thing only within one project.

- **The project's root is found from the files alone,** with git asked
  nothing, so a project builds the same from an archive.
- **A registry package's files are a root of their own,** named by their
  hash, and the selection of versions is a query over the lock file. The
  database never chooses a version.
- **A new worktree starts from the nearest saved state,** the one whose files
  differ least from its own, so an agent that creates a worktree from `main`
  gets a warm session at once.
- **A session can be opened for a git commit,** and a *trial* starts from
  another session's state with some files replaced and is never saved: a
  rename, a merge, and an upgrade are each checked in one.

### The background process

Each project has a background process for each compiler, as each workspace
has a Bazel server. The first command starts it, and it exits after three
hours without a request.

- **Commands in different worktrees are answered at once,** so no agent
  waits for another's test run. Commands in one worktree are answered one at
  a time.
- **The processes share the store and nothing in memory,** and find as facts
  the results another computed.
- **The handler is the client's own code,** so a command's answer is the
  same in the background process and in its own.
- **Clients connect through a Unix socket** that belongs to the user alone,
  since requests are marshaled values, and another user's socket could run
  code as this one.

**A command scans its worktree before it is answered,** comparing each file's
size, modification time, and inode with what the session last read, so it
always sees every change made before it. While idle, the process scans every
open worktree each second, so diagnostics and overlaps are current before
anyone asks.

## Questions

Tools ask a session questions whose answers name definitions by path and
part, never nodes: a session's diagnostics, a definition's dependencies and
dependents, the definitions a root reaches, a name's meaning, the changes
since a commit, and where two worktrees meet. A part of a definition depends
on a part of another when a node about the first reads the node about the
second, directly or through nodes about no definition, such as lookups.

## Parallel work

GOALS.md names sorting out conflicts between agents as one of the things that
will dominate development time. Git sees only lines; the database sees each
change's effects, so it finds overlaps that merge cleanly and break once
merged: one agent changes `parse` to return a `Result` while another adds a
call to it; two agents each add a method `find` to `List` in different files;
one strengthens an invariant another's new function relies on.

For two worktrees, the database compares each with their merge base. They
overlap where both changed one node, which covers two additions that answer
one lookup, and where one changed a node that depends on a node the other
changed. `truss overlap --merge` also checks the merged code in a trial and
reports every diagnostic in the merge but in neither side.

## Checking the engine

A database that returns a stale result is worse than none, and an engine can
go wrong in too many ways to think of one at a time, so it checks itself.
`Engine.audit` computes every result an engine holds again in a new engine
with the same inputs and no facts, and reports each that differs. Every test
audits every engine it made, so each stage's test also tests that the
database kept results current and that the stage's queries are pure
functions of their reads.

## Not built

- **Sharing results between machines.** It matters most where sessions are
  short, as an agent in a fresh container or CI. A forged "proven" or
  "passed" would skip exactly the checks Truss exists to make, and an object
  file is code that will run, so a result from another machine will be used
  only when signed by a trusted key, as Nix's `trusted-public-keys` require.
- A specified encoding for values, so a fingerprint does not depend on the
  compiler that marshaled it.
- Test results keyed by the code that ran rather than the code a test can
  reach.
- Keeping every deterministic test outcome, not only passes.
- A constant's value kept under an exact key.
- Solver answers in segments, not a file each.
- Registry packages and a package being worked on as fixed bases.
- Collecting registry packages no lock file names any more.
- Reading artifacts and indexes in part.
- Collecting the store without the background process.
- Each stage's version in keys, in place of the compiler's identity.
- Merging definition by definition.
- Watching files with FSEvents and inotify.
- Answering several requests about one worktree at once.
- Sharing a whole state in memory between worktrees.
- Removing stale roots, such as a deleted test's key.
- Package-wide rules as many results, so their cost follows the change.
- Answering graph questions from an index of definitions to nodes.
- A decision on running affected tests unasked, which costs CPU that
  several agents share.
