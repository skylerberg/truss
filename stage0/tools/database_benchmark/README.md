# Database benchmark

`database_benchmark` measures the code database on generated packages of several sizes. It times a first build into a store that holds only the standard library, a series of edits, a reopen in a new process, and a copy opened as a new worktree, and counts the parts that each step computes and collects.

## Rules for agents

- Do not run the benchmark unless you are told to. It holds liquid for several minutes, and it slows the CI jobs that liquid runs for other projects.
- Run it on liquid, the Ubuntu server that `ssh liquid` reaches, through `run_on_liquid.sh`, and never on the development machine. Every session's builds and tests load the development machine, so its times vary by as much as half from run to run.
- The benchmark reports the CPU time that other processes used while it ran. Idle, liquid's other processes use about one CPU-second for every ten seconds. If they used more than three for every ten seconds of the run, a CI job shared the machine with the run: run it again.
- When you are told to run it, replace the [baseline](#baseline) with the benchmark's output in the same commit as the change you measured. The history of this file then pairs each baseline with the commit that produced it.

## Running it

```sh
stage0/tools/database_benchmark/run_on_liquid.sh [--runs N] [MODULES ...]
```

The script copies the worktree's files, those git tracks and those it does not ignore, to `~/benchmark/truss` on liquid. It keeps that directory's `_build`, builds the benchmark there, and runs it with its store and its projects on liquid's disk, not in its `/tmp`, which is memory. A run holds a lock on liquid, so a second run waits for the first to end.

With no sizes the benchmark measures packages of 50, 200, and 800 modules, three runs of each. It prints Markdown: a paragraph naming the machine and the CPU time that other processes used during the run, and a table for each size. Each run has a store of its own, copied from one into which the standard library was checked once, and runs in two processes: one builds the project and edits it, and the other opens the project again and opens a copy of it.

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
| First build | Opens the project with an empty database |
| Edit one function's body | Appends `+ 0` to a body in the last module, which no module calls |
| Undo that edit | Restores the earlier text |
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
| Open the project again in a new process | Opens the project from the database that the edits saved |
| Open a copy of the project, as a new worktree does | Opens a copy of the project's directory, `.truss` included, as `cp -r` gives a new worktree its start |

Each step takes a snapshot of the project, propagates the change set through every stage, reads every file's diagnostics, computes every test's key, and saves, as the background process does after a change set and a request.

## Reading the results

| Column | Measures |
|---|---|
| Update ms | Taking the snapshot, which opens the database or reads the project's files again, and propagating the change set through every stage, lowering included |
| Check ms | Reading every file's diagnostics |
| Lower ms | Computing every test's key, which compiles no C. A step that introduces an error computes none, as `truss test` runs no test while the project has errors. |
| Save ms | Committing the database's change set to `.truss` and flushing the store |
| Computed | Parts computed |
| Collected | Parts of instances and layouts of ground types collected, since no root of lowering reaches them any more |
| Written KB | The bytes that the step added to the store and to the project's `.truss` |

Propagation drains every stage, so the update does the work, and the check and the lowering only read parts. Without the background process's watcher, a snapshot reads every file of the project again and compares it with the text the database holds. Opening a database reads every segment, unmarshals every part, and rebuilds the namespaces and the references between instances. A commit compacts the segments into one once they number more than 32 or the later segments outgrow the first.

The counts are deterministic: the benchmark exits with an error when two runs of a size count different parts. Compare counts exactly. Times vary with what else the machine runs, so compare them only between runs on liquid that other processes left quiet.

A step whose change is local should count the same parts at every size. A step whose counts grow with the package, apart from those that edit a definition every module reads, means a change's cost no longer follows the change.

## Baseline

Run on 2026-11-15, on Linux x86_64 (AMD Ryzen 7 2700X Eight-Core Processor, 16 logical cores). Other processes used 51.0 CPU-seconds during the run's 494 seconds. Each run is two processes of its own, and each time is the median of 3 runs.

Checking the standard library into an empty store took 15076 ms.

### 50 modules, 1303 functions

The first build computes 27450 parts and leaves 327 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 2220.6 | 14.1 | 1.3 | 308.5 | 27450 | 0 | 13845 |
| Edit one function's body | 43.8 | 11.6 | 1.2 | 15.9 | 33 | 0 | 16 |
| Undo that edit | 44.5 | 11.5 | 1.3 | 15.9 | 33 | 0 | 15 |
| Edit the body of the function every function calls | 91.4 | 11.3 | 1.2 | 24.7 | 1320 | 0 | 224 |
| Edit the body of a function every test reaches | 87.9 | 11.1 | 1.2 | 17.6 | 1295 | 0 | 228 |
| Change the signature of the function every function calls | 900.0 | 11.8 | 1.3 | 75.8 | 13821 | 0 | 3406 |
| Add a field to the type every module reads | 104.6 | 11.4 | 1.2 | 25.8 | 693 | 0 | 257 |
| Add a function to one module | 60.7 | 13.2 | 1.3 | 13.6 | 24 | 0 | 73 |
| Rename a function and its callers | 89.0 | 12.3 | 1.3 | 24.3 | 160 | 75 | 175 |
| Introduce a type error | 60.1 | 12.2 | – | 13.5 | 50 | 36 | 41 |
| Fix the type error | 67.5 | 11.5 | 1.2 | 14.6 | 86 | 0 | 106 |
| Remove a module | 125.5 | 12.9 | 1.2 | 25.7 | 1475 | 81 | 256 |
| Add the module back | 143.0 | 11.9 | 1.3 | 30.9 | 2017 | 0 | 434 |
| Edit a tenth of the modules at once, as switching branches does | 112.7 | 11.5 | 1.2 | 26.6 | 1386 | 0 | 283 |
| Open the project again in a new process | 1722.0 | 21.1 | 1.1 | 0.0 | 0 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 800.2 | 21.4 | 1.1 | 0.1 | 0 | 0 | 0 |

### 200 modules, 5203 functions

The first build computes 108750 parts and leaves 473 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 6567.7 | 56.9 | 4.8 | 1341.6 | 108750 | 0 | 55011 |
| Edit one function's body | 213.2 | 57.6 | 4.8 | 32.5 | 33 | 0 | 16 |
| Undo that edit | 221.5 | 57.1 | 4.9 | 32.5 | 33 | 0 | 15 |
| Edit the body of the function every function calls | 432.4 | 56.8 | 4.9 | 55.1 | 5220 | 0 | 893 |
| Edit the body of a function every test reaches | 404.1 | 56.7 | 4.8 | 49.8 | 5195 | 0 | 897 |
| Change the signature of the function every function calls | 4380.0 | 58.7 | 4.9 | 287.6 | 55221 | 0 | 13802 |
| Add a field to the type every module reads | 483.2 | 58.7 | 4.9 | 43.9 | 2643 | 0 | 1015 |
| Add a function to one module | 247.2 | 57.1 | 4.8 | 25.2 | 24 | 0 | 252 |
| Rename a function and its callers | 300.2 | 58.8 | 4.9 | 39.1 | 160 | 75 | 354 |
| Introduce a type error | 256.6 | 57.9 | – | 21.5 | 50 | 36 | 24 |
| Fix the type error | 283.0 | 57.2 | 4.9 | 27.5 | 86 | 0 | 286 |
| Remove a module | 560.0 | 57.9 | 4.9 | 38.9 | 5975 | 81 | 772 |
| Add the module back | 613.6 | 57.1 | 4.9 | 39.4 | 6517 | 0 | 954 |
| Edit a tenth of the modules at once, as switching branches does | 467.5 | 57.3 | 4.8 | 43.7 | 5556 | 0 | 1151 |
| Open the project again in a new process | 4482.3 | 110.4 | 4.3 | 0.0 | 0 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 3418.3 | 111.7 | 4.3 | 0.1 | 0 | 0 | 0 |

### 800 modules, 20803 functions

The first build computes 433950 parts and leaves 1058 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 26268.4 | 340.3 | 18.7 | 5751.7 | 433950 | 0 | 221029 |
| Edit one function's body | 1177.2 | 360.5 | 19.3 | 21.2 | 33 | 0 | 16 |
| Undo that edit | 1200.2 | 340.4 | 19.1 | 21.2 | 33 | 0 | 15 |
| Edit the body of the function every function calls | 2282.4 | 343.2 | 19.4 | 144.3 | 20820 | 0 | 3590 |
| Edit the body of a function every test reaches | 2284.2 | 341.9 | 19.2 | 146.1 | 20795 | 0 | 3593 |
| Change the signature of the function every function calls | 18946.6 | 351.8 | 19.5 | 1609.6 | 220821 | 0 | 55692 |
| Add a field to the type every module reads | 2311.6 | 341.2 | 19.1 | 81.4 | 10443 | 0 | 4069 |
| Add a function to one module | 1270.9 | 359.6 | 19.5 | 66.5 | 24 | 0 | 1040 |
| Rename a function and its callers | 1861.6 | 348.8 | 19.4 | 63.0 | 160 | 75 | 1142 |
| Introduce a type error | 1506.7 | 346.4 | – | 52.0 | 50 | 36 | 426 |
| Fix the type error | 1395.4 | 340.5 | 19.2 | 61.6 | 86 | 0 | 1074 |
| Remove a module | 2479.3 | 343.8 | 19.2 | 98.4 | 23975 | 81 | 2914 |
| Add the module back | 2516.6 | 347.5 | 19.0 | 92.6 | 24517 | 0 | 3096 |
| Edit a tenth of the modules at once, as switching branches does | 2436.1 | 355.2 | 19.3 | 205.3 | 22236 | 0 | 4648 |
| Open the project again in a new process | 16299.7 | 610.6 | 17.0 | 0.0 | 0 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 16194.7 | 608.7 | 17.0 | 0.1 | 0 | 0 | 0 |
