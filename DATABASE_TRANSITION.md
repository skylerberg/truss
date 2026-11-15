# Transition to the Code Database

This document holds the steps from stage0's incremental engine to the code
database of [Incremental builds](DESIGN.md#incremental-builds). It is
deleted when the last step is merged.

## Step 1: a pipeline in the shape of the database

The incremental engine is removed, and a build computes every part of every
definition in one pass. This pass is the database's cold build, so step 2
adds propagation to it without changing a stage.

- **Parts are stored in tables,** keyed by a definition's fully qualified
  name and the kind of part.
- **A stage is a pure function** of a definition's earlier parts and a
  record of lookups that read the tables. A stage depends on the types of
  the data it reads, not on the engine, the tables, or the stages that
  produce that data.
- **The driver computes parts in the order of the stages,** and within a
  stage in the order that the relationships of earlier stages give.
- **A failing part holds its errors as values,** and a part that reads it is
  blocked.
- **Stored state is plain data:** no closures, node pointers, or raised
  exceptions in a part.
- **Lookups record nothing yet.** Step 2 adds recording.

| The store keeps | The store loses |
|---|---|
| Find and add by key, for solver answers and test results | The `Fact` and `Reads` kinds of result |
| The directory of object files | The engine's artifacts |
| Fetched packages | The pointers |
| Each package's whole state, standard library included, keyed by its content and loaded in place of a check | The sessions |

These commands read relationships, so they are disabled until step 3:

| Command | Reads |
|---|---|
| `graph` | Dependencies and dependents |
| `holes` | Reachability |
| `impact` | The changes between two commits, and dependents |
| `overlap` | Other worktrees, their overlap, and merge previews |
| The report of an upgrade's consequences in `upgrade` | Changes and dependents |

`lsp` and `rename` keep working: each builds with some files' contents
replaced, which a pipeline does by taking those contents as input. `build`
keeps refusing a program whose `main` reaches a proof hole: the build holds
the instances the program reaches, and each definition's proof holds its
holes, so the refusal reads no stored relationship.

The tests of the engine's propagation go with the engine: the tests of the
code database and of the query engine and store, the engine fuzzer, the
tests that assert an edit computes nothing again, and the database
benchmark. Step 2 writes the tests it needs.

Step 1 merges as one pull request, once the engine's code is gone.

## Step 2: propagation, then persistence

1. **Propagation.** The background process owns the project's database in
   memory, and its watcher turns changes to files into change sets. Lookups
   record their reads, the database marks stale parts, and the driver
   computes them. The database keeps namespaces and recursion groups, and
   lowering checks each call it emits against the caller's call edges. The
   hot-versus-cold tests compare a propagated database with the step 1
   pipeline, and the fuzzer drives them. A restart, or a command run with
   `--no-server`, does a cold build.
2. **Persistence.** The database lives in `.truss/`, commits each change set
   by writing new segment files and then replacing, by rename, the file that
   lists them, and holds paths relative to the project's root. It records
   its compiler and the fingerprints of the files it was built from, and one
   process owns it at a time.

## Step 3: commands that read relationships

The commands that step 1 disabled are written again against the database's
relationships.
