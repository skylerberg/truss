# standard::simulation

`World` provides every standard capability at once, as an in-memory machine:
a file system, a network between its own hosts, a console, an environment,
programs whose output the test scripts, a clock of its own, and tasks
scheduled by a seed.

```truss
test "a reply that never arrives ends at the time limit" {
  let world = simulation::World.new(seed: 3)
  provide world {
    let reply = tasks::with_timeout(Duration.seconds(5), work: fn() { wait_for_reply() })
    assert reply is None
    assert Clock.monotonic() == Duration.seconds(5)
    assert world.output() == ""
  }
}
```

- The clock advances only when every task is blocked, and then jumps to the
  earliest deadline of a sleeping task, so a test of a time limit takes no
  real time.
- `Setup` holds a world's initial state: the lines of its console's input,
  its environment's variables, its files, its hosts, and its programs.
  `World.from(setup, seed: seed)` makes the world. `Setup.with_file(path,
  contents)` adds a file and the directories above it.
- `world.fail_next(operation, error)` makes the next `Open`, `Read`, or
  `Write` of a file fail with `error`, once.
- A `World` is a reference to its state, so it is provided without `mut`. A
  test reads the world's record of events, such as `world.output()`,
  `world.records()`, and `world.file_text(path)`, inside the `provide`.
- Each capability call into a `World` is a point where the seed may switch
  to another task. A deadlock panics, as under `tasks::SeededTasks`.
