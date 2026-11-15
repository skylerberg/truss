# Database benchmark

`database_benchmark` measures the code database on generated packages of several sizes. It times a first build into a store that holds only the standard library, a series of edits, a reopen in a new process, and a copy opened as a new worktree, and reports the engine's counters for each step.

## Rules for agents

- Do not run the benchmark unless you are told to. It runs for about four minutes and loads the machine that every session shares, which slows other sessions' builds and tests and skews their timings.
- When you are told to run it, replace the [baseline](#baseline) with the benchmark's output in the same commit as the change you measured. The history of this file then pairs each baseline with the commit that produced it.

## Running it

```sh
dune exec stage0/tools/database_benchmark/database_benchmark.exe -- [--runs N] [MODULES ...]
```

With no sizes it measures packages of 50, 200, and 800 modules, three runs of each. It prints Markdown: a paragraph naming the machine and its load, and a table for each size. Each run is a process of its own, with a store of its own, copied from one into which the standard library was checked once.

## The workload

The generated package `demo` has a module `core` and `MODULES` modules `m0`, `m1`, and so on.

| Definition | Reads |
|---|---|
| `core::Point`, a type with fields `x` and `y` | nothing |
| `core::Measured`, a trait that `Point` implements | `Point` |
| `core::leaf` | nothing |
| Each of the 25 functions `f<i>_<k>` of module `m<i>` | `core::leaf`, and the function before it; the first reads the last function of module `m<(i - 1) / 2>` |
| `measured_<i>` in `m<i>` | `Point`, through `Measured` and a field |
| The test of `m<i>` | the module's last function and `measured_<i>` |

Every function reads `leaf`, every module reads `Point`, and the modules call each other as a binary tree rooted at `m0`, so the test of a module reaches the modules on its path to `m0`.

## Steps

| Step | Change |
|---|---|
| First build | Opens the project, checks every file, computes every test's key, and saves |
| Edit one function's body | Appends `+ 0` to a body in the last module, which no module calls |
| Undo that edit | Restores the earlier text, whose results the store holds as facts |
| Edit the body of the function every function calls | Changes the body of `core::leaf` |
| Edit the body of a function every test reaches | Changes the body of the last function of `m0` |
| Change the signature of the function every function calls | Gives `core::leaf` a parameter with a default |
| Add a field to the type every module reads | Adds a field to `Point` and to its one construction |
| Add a function to one module | Appends a function to the middle module |
| Rename a function and its callers | Renames the last function of `m0` in `m0`, `m1`, and `m2` |
| Introduce a type error | Adds a `Bool` to an `Int64` in the middle module |
| Fix the type error | Restores the earlier text |
| Remove a module | Deletes the last module |
| Add the module back | Writes the deleted module again |
| Edit a tenth of the modules at once, as switching branches does | Changes one body in every tenth module |
| Open the project again in a new process | Closes every session and the store, then opens the project |
| Open a copy of the project, as a new worktree does | Opens a copy of the project's files, which starts from the nearest saved state |

After each edit the benchmark refreshes the session, checks every file, computes every test's key, and saves.

## Reading the results

| Column | Measures |
|---|---|
| Update ms | Opening the session, or refreshing it after an edit |
| Check ms | Reading every file's diagnostics |
| Lower ms | Computing every test's key, which lowers the code the test reaches and compiles no C |
| Save ms | Writing the state, and flushing the store to disk |
| Marked | Results marked as possibly changed |
| Confirmed | Marked results found current without being computed |
| Computed | Results computed |
| Adopted | Results found as facts in the store instead of computed |
| Written KB | How much the store grew |

A refresh brings every root up to date, so after an edit the update does the work and the check and the lowering only read results. Opening a session writes its state whole again once its chain of differences reaches half its size, which the reopen in these tables does. The store seals a segment once it passes 64 MB, at its next write, and writes the segment's sorted index then: the edit after a large first build pays for that index in its update time and its written bytes.

The counts are deterministic: the benchmark exits with an error when two runs of a size count different work. A run needs a process of its own for that. Within one process, node ids grow from run to run, the engine visits results in an order that follows them, and a second run can compute a result that the first did not. Compare counts exactly. Times vary with the machine's load, by as much as half on a shared machine, so compare times only where they differ by more than that, and read the load averages beside them.

A step whose change is local should count the same work at every size. A step whose counts grow with the package, apart from those that change what every module reads, means a change's cost no longer follows the change.

## Baseline

Run on 2026-11-14, on Darwin arm64 (Apple M4, 10 logical cores). Load averages were 10.47 13.70 12.02 before the run and 9.96 12.21 11.84 after it. Each run is a process of its own, and each time is the median of 3 runs.

Checking the standard library into an empty store took 9402 ms.

### 50 modules, 1303 functions

The first build leaves 45031 results and 235 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Marked | Confirmed | Computed | Adopted | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| First build | 773.5 | 199.2 | 105.4 | 430.8 | 3 | 1 | 44925 | 0 | 14706 |
| Edit one function's body | 4.0 | 0.0 | 0.1 | 1.8 | 274 | 151 | 123 | 0 | 47 |
| Undo that edit | 1.7 | 0.0 | 0.1 | 1.1 | 274 | 151 | 42 | 81 | 33 |
| Edit the body of the function every function calls | 11.5 | 0.0 | 0.1 | 13.5 | 1402 | 53 | 1349 | 0 | 557 |
| Edit the body of a function every test reaches | 11.7 | 0.0 | 0.1 | 14.4 | 1536 | 151 | 1385 | 0 | 568 |
| Change the signature of the function every function calls | 199.4 | 0.0 | 0.1 | 134.5 | 21452 | 2549 | 18903 | 0 | 7080 |
| Add a field to the type every module reads | 16.9 | 0.0 | 0.1 | 13.4 | 1888 | 1065 | 823 | 0 | 489 |
| Add a function to one module | 5.6 | 0.0 | 0.1 | 4.1 | 268 | 87 | 198 | 0 | 118 |
| Rename a function and its callers | 13.8 | 0.0 | 0.1 | 9.2 | 2088 | 1642 | 479 | 72 | 301 |
| Introduce a type error | 5.6 | 0.0 | 0.1 | 3.3 | 282 | 153 | 129 | 0 | 128 |
| Fix the type error | 6.3 | 0.0 | 0.1 | 4.0 | 278 | 153 | 136 | 141 | 139 |
| Remove a module | 9.3 | 0.0 | 0.1 | 5.1 | 989 | 110 | 816 | 0 | 222 |
| Add the module back | 12.1 | 1.6 | 0.1 | 11.4 | 279 | 110 | 855 | 188 | 308 |
| Edit a tenth of the modules at once, as switching branches does | 20.9 | 0.0 | 0.1 | 23.0 | 2559 | 719 | 1840 | 0 | 751 |
| Open the project again in a new process | 1512.1 | 0.1 | 1.2 | 0.7 | 0 | 0 | 2 | 0 | 7629 |
| Open a copy of the project, as a new worktree does | 46.7 | 0.0 | 0.7 | 1.4 | 0 | 0 | 2 | 0 | 14 |

### 200 modules, 5203 functions

The first build leaves 177481 results and 419 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Marked | Confirmed | Computed | Adopted | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| First build | 850.8 | 644.3 | 488.0 | 1980.9 | 3 | 1 | 177075 | 0 | 59399 |
| Edit one function's body | 12.8 | 0.1 | 0.4 | 2.6 | 274 | 151 | 123 | 0 | 49 |
| Undo that edit | 4.1 | 0.1 | 0.3 | 1.6 | 274 | 151 | 42 | 81 | 35 |
| Edit the body of the function every function calls | 42.4 | 0.1 | 0.3 | 54.4 | 5302 | 53 | 5249 | 0 | 2196 |
| Edit the body of a function every test reaches | 44.6 | 0.1 | 0.3 | 61.4 | 5436 | 151 | 5285 | 0 | 2211 |
| Change the signature of the function every function calls | 977.3 | 0.1 | 0.4 | 833.9 | 85502 | 10049 | 75453 | 0 | 36276 |
| Add a field to the type every module reads | 75.7 | 0.1 | 0.4 | 47.9 | 7138 | 4065 | 3073 | 0 | 1706 |
| Add a function to one module | 14.7 | 0.1 | 0.5 | 5.9 | 268 | 87 | 198 | 0 | 125 |
| Rename a function and its callers | 42.4 | 0.1 | 0.3 | 16.3 | 5988 | 5542 | 479 | 72 | 549 |
| Introduce a type error | 26.3 | 0.1 | 0.8 | 13.3 | 282 | 153 | 128 | 0 | 371 |
| Fix the type error | 31.6 | 0.1 | 2.4 | 15.5 | 278 | 153 | 136 | 141 | 382 |
| Remove a module | 38.5 | 0.1 | 0.3 | 17.4 | 1739 | 410 | 1243 | 0 | 541 |
| Add the module back | 36.3 | 2.2 | 0.3 | 23.2 | 1029 | 410 | 1155 | 338 | 605 |
| Edit a tenth of the modules at once, as switching branches does | 102.4 | 0.1 | 0.4 | 117.8 | 10231 | 2853 | 7378 | 0 | 3045 |
| Open the project again in a new process | 4391.8 | 0.3 | 5.3 | 1.2 | 0 | 0 | 2 | 0 | 30832 |
| Open a copy of the project, as a new worktree does | 115.6 | 0.1 | 2.8 | 2.0 | 0 | 0 | 2 | 0 | 52 |

### 800 modules, 20803 functions

The first build leaves 707281 results and 1207 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Marked | Confirmed | Computed | Adopted | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| First build | 778.6 | 2400.8 | 1886.8 | 7624.8 | 3 | 1 | 705675 | 0 | 256221 |
| Edit one function's body | 153.2 | 0.4 | 1.7 | 3.7 | 274 | 151 | 123 | 0 | 9529 |
| Undo that edit | 13.6 | 0.3 | 1.5 | 3.4 | 274 | 151 | 42 | 81 | 35 |
| Edit the body of the function every function calls | 185.4 | 0.4 | 1.4 | 254.6 | 20902 | 53 | 20849 | 0 | 8955 |
| Edit the body of a function every test reaches | 188.9 | 0.3 | 1.3 | 287.3 | 21036 | 151 | 20885 | 0 | 8985 |
| Change the signature of the function every function calls | 3590.5 | 0.3 | 1.5 | 3105.0 | 341702 | 40049 | 301653 | 0 | 128108 |
| Add a field to the type every module reads | 269.0 | 0.3 | 1.3 | 162.0 | 28138 | 16065 | 12073 | 0 | 7186 |
| Add a function to one module | 27.6 | 0.3 | 1.2 | 5.5 | 268 | 87 | 198 | 0 | 152 |
| Rename a function and its callers | 89.3 | 0.3 | 1.1 | 29.1 | 21588 | 21142 | 479 | 72 | 1552 |
| Introduce a type error | 65.6 | 0.3 | 1.7 | 25.1 | 282 | 153 | 128 | 0 | 1347 |
| Fix the type error | 66.8 | 0.4 | 1.3 | 25.3 | 278 | 153 | 136 | 141 | 1359 |
| Remove a module | 122.7 | 0.3 | 2.6 | 34.5 | 4739 | 1610 | 3070 | 0 | 1821 |
| Add the module back | 112.4 | 1.8 | 1.3 | 38.4 | 4029 | 1610 | 2355 | 938 | 1785 |
| Edit a tenth of the modules at once, as switching branches does | 324.5 | 0.4 | 1.4 | 379.0 | 40891 | 11373 | 29518 | 0 | 12393 |
| Open the project again in a new process | 14769.6 | 1.6 | 34.5 | 3.5 | 0 | 0 | 2 | 0 | 125089 |
| Open a copy of the project, as a new worktree does | 684.5 | 0.4 | 11.4 | 8.6 | 0 | 0 | 2 | 0 | 207 |
