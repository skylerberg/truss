# Transition to the Code Database

This document holds the steps from stage0's incremental engine to the code
database of [Incremental builds](DESIGN.md#incremental-builds). It is
deleted when the last step is merged.

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
