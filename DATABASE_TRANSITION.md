# Transition to the Code Database

This document holds the steps from stage0's incremental engine to the code
database of [Incremental builds](DESIGN.md#incremental-builds). It is
deleted when the last step is merged.

## Step 2: propagation, then persistence

1. **Propagation.** Done, except that a trial (`lsp`, `rename`, and the new
   errors that `upgrade` reports) and a release build still build cold. A
   trial would propagate its changed files through a copy of the project's
   database, which needs a copy that costs less than a cold build.
2. **Persistence.** The database lives in `.truss/`, commits each change set
   by writing new segment files and then replacing, by rename, the file that
   lists them, and holds paths relative to the project's root. It records
   its compiler and the fingerprints of the files it was built from, and one
   process owns it at a time.

## Step 3: commands that read relationships

These commands read relationships, so they are disabled until they are
written again against the database's relationships:

| Command | Reads |
|---|---|
| `graph` | Dependencies and dependents |
| `holes` | Reachability |
| `impact` | The changes between two commits, and dependents |
| `overlap` | Other worktrees, their overlap, and merge previews |
| The report of an upgrade's consequences in `upgrade` | Changes and dependents |
