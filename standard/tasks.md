# standard::tasks

Channels, limits on how many tasks run at once, cells that several tasks
update, time limits, and a deterministic `Tasks` for tests. The language's
`concurrent` blocks and loops are defined in
[SPECIFICATION.md](../SPECIFICATION.md#concurrency).

## Channels

A `Channel[Message]` is a queue with a fixed capacity. `send` waits while the
channel is full, `receive` waits while it is empty, and `close` ends the
loops that receive from it:

```truss
fn total_size(paths: Slice[Path]) -> USize
  uses Tasks, FileRead
{
  let texts = Channel[String].new(capacity: 16)
  var total: USize = 0
  concurrent {
    {
      for path in paths {
        if FileRead.read_text(path) is Ok(text) {
          let _ = texts.send(own text)
        }
      }
      texts.close()
    }
    for text in texts.messages() {
      total = total.saturating_add(size(text))
    }
  }
  total
}
```

- A message is `Storable`, and sending it moves it.
- A channel's methods take `self` read-only, so every branch can use a
  channel declared before the block. `channel.copy()` is another reference
  to the same queue, which is freed when the last reference is dropped.
- `Channel[Message].new()` has capacity 0: `send` returns when another task
  has received the message.
- The messages of one sender are received in the order it sent them. The
  messages of two senders interleave in any order.
- `send` returns `Err(SendError.Closed)` on a closed channel. `receive`
  returns the messages a closed channel still holds, and then `None`.
  `try_receive` never waits, and `is_closed` tells whether `close` has been
  called.
- In a cancelled task, a `send` that would wait returns
  `Err(SendError.Cancelled)`, and a `receive` that would wait returns `None`.

## Limits, cells, and counters

- `Limiter.new(permits)` bounds how many tasks do something at once.
  `limiter.hold(work)` runs `work` when a permit is free and returns `Some`
  of its result. In a task cancelled while it waits, `hold` returns `None`
  and does not run `work`.
- `Cell[Value]` holds a value that several tasks update.
  `cell.update(change)` runs `change`, which uses no capability, on the value
  while it holds the cell's mutex. `cell.copy()` is another reference to the
  same value.
- `Counter` is a cell that holds an `Int64`.

## Time limits

`with_timeout(limit, work)` runs `work` and a timer as two branches, each of
which returns, so the first to finish cancels the other:

```truss
public fn with_timeout[Output, capability Granted](
  limit: Duration,
  work: (fn() -> Output uses Granted),
) -> Option[Output]
  uses Tasks, Clock, Granted
{
  concurrent {
    return Some(work())
    {
      Clock.sleep(limit)
      return None
    }
  }
}
```

## Testing concurrent code

`SeededTasks.new(seed)` is a `Tasks` that runs one task at a time and
chooses by the seed which runs next, switching only at capability calls, so
a test of concurrent code gives the same result on every run:

```truss
test "two deposits both arrive" {
  let seeds: UInt64 = 64
  for seed in 0..seeds {
    var bank = Bank.new()
    provide mut bank, tasks::SeededTasks.new(seed) {
      concurrent {
        Accounts.deposit(alice, amount: 10)
        Accounts.deposit(alice, amount: 5)
      }
    }
    assert bank.balance(alice) == 15
  }
}
```

A deadlock under `SeededTasks` panics and reports the event each task was
waiting for, so a function that provides one outside a test declares
`uses Panic`. To fake every capability at once, see
[simulation.md](simulation.md).
