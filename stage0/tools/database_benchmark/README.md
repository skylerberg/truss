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

Run on 2026-11-15, on Linux x86_64 (AMD Ryzen 7 2700X Eight-Core Processor, 16 logical cores). Other processes used 48.2 CPU-seconds during the run's 471 seconds. Each run is two processes of its own, and each time is the median of 3 runs.

Checking the standard library into an empty store took 15068 ms.

### 50 modules, 1303 functions

The first build computes 27450 parts and leaves 327 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 2131.8 | 8.7 | 1.8 | 335.4 | 27450 | 0 | 13846 |
| Edit one function's body | 44.1 | 6.7 | 1.3 | 13.5 | 33 | 0 | 16 |
| Undo that edit | 44.7 | 6.6 | 1.3 | 13.3 | 33 | 0 | 15 |
| Edit the body of the function every function calls | 91.5 | 6.4 | 1.2 | 17.4 | 1320 | 0 | 224 |
| Edit the body of a function every test reaches | 87.9 | 6.4 | 1.2 | 18.4 | 1295 | 0 | 228 |
| Change the signature of the function every function calls | 907.2 | 7.0 | 1.3 | 77.5 | 13821 | 0 | 3406 |
| Add a field to the type every module reads | 106.2 | 6.5 | 1.3 | 26.3 | 693 | 0 | 257 |
| Add a function to one module | 60.5 | 7.8 | 1.5 | 14.8 | 24 | 0 | 73 |
| Rename a function and its callers | 85.8 | 7.2 | 1.3 | 17.2 | 160 | 75 | 175 |
| Introduce a type error | 58.1 | 7.2 | – | 15.7 | 50 | 36 | 41 |
| Fix the type error | 69.3 | 6.6 | 1.3 | 16.6 | 86 | 0 | 106 |
| Remove a module | 67.1 | 7.9 | 1.3 | 18.3 | 5 | 81 | 151 |
| Add the module back | 85.1 | 6.6 | 1.3 | 20.1 | 547 | 0 | 330 |
| Edit a tenth of the modules at once, as switching branches does | 117.5 | 6.7 | 1.2 | 28.2 | 1386 | 0 | 283 |
| Open the project again in a new process | 1640.1 | 14.6 | 1.1 | 0.0 | 0 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 800.2 | 15.0 | 1.2 | 0.1 | 0 | 0 | 0 |

### 200 modules, 5203 functions

The first build computes 108750 parts and leaves 473 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 6510.6 | 31.6 | 4.9 | 1347.8 | 108750 | 0 | 55016 |
| Edit one function's body | 216.4 | 29.8 | 5.0 | 36.3 | 33 | 0 | 16 |
| Undo that edit | 222.3 | 29.6 | 4.9 | 34.6 | 33 | 0 | 15 |
| Edit the body of the function every function calls | 432.1 | 29.8 | 4.9 | 43.6 | 5220 | 0 | 893 |
| Edit the body of a function every test reaches | 402.4 | 30.0 | 4.9 | 42.7 | 5195 | 0 | 897 |
| Change the signature of the function every function calls | 4388.8 | 32.3 | 5.0 | 284.3 | 55221 | 0 | 13802 |
| Add a field to the type every module reads | 487.4 | 30.0 | 5.0 | 40.0 | 2643 | 0 | 1015 |
| Add a function to one module | 246.1 | 29.8 | 4.9 | 29.0 | 24 | 0 | 252 |
| Rename a function and its callers | 301.9 | 30.4 | 5.0 | 32.6 | 160 | 75 | 354 |
| Introduce a type error | 258.7 | 30.0 | – | 25.6 | 50 | 36 | 24 |
| Fix the type error | 282.6 | 30.0 | 5.0 | 32.4 | 86 | 0 | 286 |
| Remove a module | 286.8 | 31.8 | 5.1 | 31.5 | 5 | 81 | 337 |
| Add the module back | 322.5 | 30.1 | 5.1 | 44.2 | 547 | 0 | 518 |
| Edit a tenth of the modules at once, as switching branches does | 497.3 | 30.2 | 5.0 | 50.0 | 5556 | 0 | 1151 |
| Open the project again in a new process | 4402.9 | 76.3 | 4.4 | 0.0 | 0 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 3370.7 | 77.5 | 4.4 | 0.1 | 0 | 0 | 0 |

### 800 modules, 20803 functions

The first build computes 433950 parts and leaves 1058 MB of live heap.

| Step | Update ms | Check ms | Lower ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 26059.8 | 146.1 | 19.2 | 5884.3 | 433950 | 0 | 221049 |
| Edit one function's body | 1193.8 | 143.5 | 20.0 | 21.6 | 33 | 0 | 16 |
| Undo that edit | 1209.4 | 143.3 | 19.6 | 21.5 | 33 | 0 | 15 |
| Edit the body of the function every function calls | 2302.1 | 145.2 | 19.9 | 142.9 | 20820 | 0 | 3590 |
| Edit the body of a function every test reaches | 2299.6 | 145.4 | 19.8 | 145.3 | 20795 | 0 | 3593 |
| Change the signature of the function every function calls | 19079.2 | 151.7 | 20.0 | 1607.8 | 220821 | 0 | 55692 |
| Add a field to the type every module reads | 2324.5 | 143.4 | 19.7 | 76.8 | 10443 | 0 | 4069 |
| Add a function to one module | 1287.5 | 146.3 | 19.9 | 58.8 | 24 | 0 | 1040 |
| Rename a function and its callers | 1830.0 | 142.5 | 19.8 | 50.8 | 160 | 75 | 1142 |
| Introduce a type error | 1550.0 | 145.7 | – | 34.3 | 50 | 36 | 426 |
| Fix the type error | 1380.3 | 143.1 | 19.7 | 60.6 | 86 | 0 | 1074 |
| Remove a module | 1339.3 | 143.2 | 19.8 | 56.9 | 5 | 81 | 1136 |
| Add the module back | 1390.9 | 143.4 | 19.8 | 72.5 | 547 | 0 | 1318 |
| Edit a tenth of the modules at once, as switching branches does | 2206.8 | 143.7 | 19.7 | 161.8 | 22236 | 0 | 4648 |
| Open the project again in a new process | 16142.6 | 362.6 | 17.5 | 0.0 | 0 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 16197.9 | 368.6 | 17.6 | 0.1 | 0 | 0 | 0 |
