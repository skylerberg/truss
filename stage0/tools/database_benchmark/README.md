# Database benchmark

`database_benchmark` measures the code database on generated packages of several sizes. It times a first build into a cache that holds only the standard library, a series of edits, a reopen in a new process, and a copy opened as a new worktree, and counts the parts that each step computes and collects.

## Rules for agents

- Do not run the benchmark unless you are told to. It holds liquid for several minutes, and it slows the CI jobs that liquid runs for other projects.
- Run it on liquid, the Ubuntu server that `ssh liquid` reaches, through `run_on_liquid.sh`, and never on the development machine. Every session's builds and tests load the development machine, so its times vary by as much as half from run to run.
- The benchmark reports the CPU time that other processes used while it ran. Idle, liquid's other processes use about one CPU-second for every ten seconds. If they used more than three for every ten seconds of the run, a CI job shared the machine with the run: run it again.
- When you are told to run it, replace the [baseline](#baseline) with the benchmark's output in the same commit as the change you measured. The history of this file then pairs each baseline with the commit that produced it.

## Running it

```sh
stage0/tools/database_benchmark/run_on_liquid.sh [--runs N] [MODULES ...]
```

The script waits for the lock `~/benchmark/truss.lock` on liquid, so a second run waits for the first to end. It then copies the worktree's files, those git tracks and those it does not ignore, into a directory of its own under `~/benchmark`, builds the benchmark there, and runs it with its cache and its projects in that directory, on liquid's disk and not in its `/tmp`, which is memory. The directory is deleted when the run ends.

With no sizes the benchmark measures packages of 50, 200, and 800 modules, three runs of each. It prints Markdown: a paragraph naming the machine and the CPU time that other processes used during the run, and a table for each size. Each run has a cache of its own, copied from one into which the standard library was checked once, and runs in two processes: one builds the project and edits it, and the other opens the project again and opens a copy of it.

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
| Add a function to one module | Appends a public function to the middle module, since an unused internal one is an error |
| Rename a function and its callers | Renames the last function of `m0` in `m0`, `m1`, and `m2` |
| Introduce a type error | Adds a `Bool` to an `Int64` in the middle module |
| Fix the type error | Restores the earlier text |
| Remove a module | Deletes the last module |
| Add the module back | Writes the deleted module again |
| Edit a tenth of the modules at once, as switching branches does | Changes one body in every tenth module |
| Open the project again in a new process | Opens the project from the database that the edits saved |
| Open a copy of the project, as a new worktree does | Opens a copy of the project's directory, `.truss` included, as `cp -r` gives a new worktree its start |

Each step takes a snapshot of the project, which applies the change set and propagates it through the checks. It then reads every file's errors, computes every test's key, and saves, as the background process does after a change set and a request. A step fails when it reports an error it should not, or none where it introduces one; warnings are not counted.

## Reading the results

| Column | Measures |
|---|---|
| Update ms | Taking the snapshot, which opens the database or reads the project's files again, applies the change set, and propagates it through the checks |
| Check ms | Reading every file's diagnostics |
| Key ms | Computing every test's key, which lowers the definitions the tests reach and compiles no C. A step that introduces an error computes none, as `truss test` runs no test while the project has errors. |
| Save ms | Committing the database's change set to `.truss` and flushing the cache |
| Computed | Parts computed |
| Collected | Parts of instances and layouts of ground types collected, since no root of lowering reaches them any more |
| Written KB | The bytes that the step added to the cache and to the project's `.truss` |

The update propagates the change set through the checks, so the check only reads parts, and computing the test keys computes the lowering that the tests reach. Without the background process's watcher, a snapshot reads every file of the project again and compares it with the text the database holds. Opening a database reads every segment, unmarshals every part, and rebuilds the namespaces and the references between instances. A commit compacts the segments into one once they number more than 32 or the later segments outgrow the first.

The counts are deterministic: the benchmark exits with an error when two runs of a size count different parts. Compare counts exactly. Times vary with what else the machine runs, so compare them only between runs on liquid that other processes left quiet.

A step whose change is local should count the same parts at every size. A step whose counts grow with the package, apart from those that edit a definition every module reads, means a change's cost no longer follows the change.

## Baseline

Run on 2026-11-20, on Linux x86_64 (AMD Ryzen 7 2700X Eight-Core Processor, 16 logical cores). Other processes used 51.1 CPU-seconds during the run's 481 seconds. Each run is two processes of its own, and each time is the median of 3 runs.

Checking the standard library into an empty cache took 19461 ms.

### 50 modules, 1303 functions

The first build computes 20681 parts and leaves 319 MB of live heap.

| Step | Update ms | Check ms | Key ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 1524.5 | 18.7 | 337.4 | 345.0 | 20681 | 0 | 11280 |
| Edit one function's body | 58.2 | 18.1 | 5.1 | 24.2 | 32 | 0 | 16 |
| Undo that edit | 59.8 | 18.3 | 5.3 | 26.4 | 32 | 0 | 16 |
| Edit the body of the function every function calls | 55.8 | 18.4 | 29.3 | 26.2 | 1368 | 0 | 281 |
| Edit the body of a function every test reaches | 56.4 | 18.2 | 27.7 | 18.8 | 1343 | 0 | 284 |
| Change the signature of the function every function calls | 437.3 | 18.4 | 259.5 | 85.8 | 8869 | 0 | 3362 |
| Add a field to the type every module reads | 77.1 | 18.7 | 29.7 | 30.6 | 535 | 0 | 220 |
| Add a function to one module | 67.8 | 19.6 | 0.1 | 21.0 | 20 | 0 | 72 |
| Rename a function and its callers | 69.6 | 20.3 | 80.9 | 33.1 | 117 | 50 | 154 |
| Introduce a type error | 56.4 | 18.5 | – | 24.5 | 16 | 0 | 33 |
| Fix the type error | 67.2 | 20.1 | 3.4 | 26.4 | 18 | 0 | 70 |
| Remove a module | 149.8 | 19.8 | 0.1 | 30.2 | 1475 | 56 | 241 |
| Add the module back | 159.6 | 20.2 | 67.6 | 38.0 | 1884 | 0 | 379 |
| Edit a tenth of the modules at once, as switching branches does | 74.1 | 20.1 | 32.8 | 36.0 | 1418 | 0 | 340 |
| Open the project again in a new process | 1401.7 | 21.9 | 0.1 | 0.0 | 1359 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 592.3 | 22.1 | 0.1 | 0.0 | 1359 | 0 | 0 |

### 200 modules, 5203 functions

The first build computes 82031 parts and leaves 443 MB of live heap.

| Step | Update ms | Check ms | Key ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 4242.8 | 91.8 | 1470.1 | 1162.0 | 82031 | 0 | 44925 |
| Edit one function's body | 284.3 | 90.6 | 27.8 | 22.3 | 32 | 0 | 16 |
| Undo that edit | 292.3 | 88.0 | 27.7 | 22.3 | 32 | 0 | 16 |
| Edit the body of the function every function calls | 276.8 | 89.2 | 150.7 | 40.1 | 5418 | 0 | 1131 |
| Edit the body of a function every test reaches | 261.5 | 88.3 | 142.7 | 53.2 | 5393 | 0 | 1134 |
| Change the signature of the function every function calls | 2118.7 | 91.4 | 1231.8 | 273.7 | 35419 | 0 | 13604 |
| Add a field to the type every module reads | 385.7 | 92.0 | 135.4 | 29.2 | 2035 | 0 | 866 |
| Add a function to one module | 261.3 | 89.8 | 0.3 | 24.7 | 20 | 0 | 252 |
| Rename a function and its callers | 300.2 | 91.6 | 484.0 | 28.3 | 117 | 50 | 333 |
| Introduce a type error | 238.4 | 88.4 | – | 21.3 | 16 | 0 | 16 |
| Fix the type error | 295.2 | 93.0 | 16.2 | 42.2 | 18 | 0 | 250 |
| Remove a module | 712.6 | 90.2 | 0.3 | 56.0 | 5975 | 56 | 740 |
| Add the module back | 631.2 | 88.2 | 433.1 | 51.0 | 6384 | 0 | 881 |
| Edit a tenth of the modules at once, as switching branches does | 301.6 | 89.8 | 155.0 | 66.2 | 5678 | 0 | 1387 |
| Open the project again in a new process | 3609.5 | 108.8 | 0.3 | 0.0 | 5409 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 3021.7 | 110.2 | 0.4 | 0.0 | 5409 | 0 | 0 |

### 800 modules, 20803 functions

The first build computes 327431 parts and leaves 937 MB of live heap.

| Step | Update ms | Check ms | Key ms | Save ms | Computed | Collected | Written KB |
|---|---:|---:|---:|---:|---:|---:|---:|
| First build | 17200.8 | 547.6 | 6164.4 | 5279.3 | 327431 | 0 | 180798 |
| Edit one function's body | 1587.4 | 596.4 | 146.4 | 25.6 | 32 | 0 | 16 |
| Undo that edit | 1659.9 | 600.2 | 143.1 | 21.2 | 32 | 0 | 16 |
| Edit the body of the function every function calls | 1645.9 | 544.7 | 845.2 | 186.3 | 21618 | 0 | 4562 |
| Edit the body of a function every test reaches | 1767.6 | 546.3 | 793.2 | 118.2 | 21593 | 0 | 4566 |
| Change the signature of the function every function calls | 8817.2 | 555.4 | 5771.9 | 1221.9 | 141619 | 0 | 54850 |
| Add a field to the type every module reads | 1996.7 | 561.5 | 673.0 | 95.2 | 8035 | 0 | 3470 |
| Add a function to one module | 1688.7 | 650.1 | 1.3 | 59.4 | 20 | 0 | 1079 |
| Rename a function and its callers | 1771.3 | 545.7 | 2356.5 | 59.9 | 117 | 50 | 1161 |
| Introduce a type error | 1242.8 | 546.2 | – | 28.3 | 16 | 0 | 420 |
| Fix the type error | 1517.9 | 593.9 | 81.0 | 60.0 | 18 | 0 | 1077 |
| Remove a module | 3072.1 | 581.9 | 1.3 | 113.8 | 23975 | 56 | 2854 |
| Add the module back | 3309.1 | 548.3 | 2503.2 | 135.7 | 24384 | 0 | 2995 |
| Edit a tenth of the modules at once, as switching branches does | 1678.2 | 544.5 | 775.5 | 157.2 | 22718 | 0 | 5609 |
| Open the project again in a new process | 13216.2 | 628.8 | 1.5 | 0.0 | 21609 | 0 | 0 |
| Open a copy of the project, as a new worktree does | 13633.5 | 633.3 | 1.5 | 0.0 | 21609 | 0 | 0 |
