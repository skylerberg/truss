(* [concurrent] blocks and loops. Whole programs use the runtime's [Tasks],
   which runs each task when it is spawned. Truss tests provide a [Tasks]
   written in Truss, and the test runner fails a test that leaks a heap
   block. *)

open Codegen_support

let expect_main ~expected text =
  let status, output, errors = run_main text in
  if status <> 0 then fail "ended with status %d: %s" status errors;
  expect_string ~expected output

(* A [Tasks] implementation in Truss that runs each task when it is
   spawned. *)
let in_order =
  {|
type InOrder(opened: UInt64, cancelled: List[UInt64])

fn InOrder.is_cancelled(self, task_group: UInt64) -> Bool {
  for other in self.cancelled {
    if other == task_group {
      return true
    }
  }
  false
}

impl Tasks for InOrder {
  fn open(mut self) -> UInt64 {
    self.opened += 1
    self.opened
  }

  fn spawn(self, task_group: UInt64, work: own fn(UInt64), item: UInt64) -> Bool {
    if self.is_cancelled(task_group) {
      return false
    }
    work(item)
    true
  }

  fn join(self, task_group: UInt64) {}

  fn cancel(mut self, task_group: UInt64) -> Bool {
    if self.is_cancelled(task_group) {
      return false
    }
    mut self.cancelled.push(task_group)
    true
  }

  fn cancelled(self) -> Bool {
    false
  }

  fn watch(self, key: UInt64) -> UInt64 {
    0
  }

  fn wait(self, key: UInt64, ticket: UInt64, reason: StringSlice) {}

  fn wake(self, key: UInt64) {}

  fn lock(self, mutex: UInt64) {}

  fn unlock(self, mutex: UInt64) {}

  fn yield_now(self) {}
}
|}

(* A test of a module whose [count] tests all pass. [InOrder] is appended to
   the module. *)
let passes_in_order name ~count source =
  test name (fun () ->
      expect_output (source ^ in_order)
        (String.concat "" (List.init count (Printf.sprintf "test %d passed\n"))))

(* Blocks *)

let () =
  test "branches use the enclosing capabilities and bind lets for the code after the block"
    (fun () ->
      expect_main ~expected:"first\nsecond\n20 22 made 3\n"
        {|type Pair(first: Int64, second: Int64)

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var pair = Pair(first: 0, second: 0)
  concurrent {
    {
      Console.print_line("first")
      pair.first = 20
    }
    {
      Console.print_line("second")
      pair.second = 22
    }
    let made = "made"
    let lengths = ["a", "bb", "ccc"].map(fn(text) { text.length() })
  }
  Console.print_line("${pair.first} ${pair.second} ${made} ${lengths[2]}")
  ExitCode.success
}
|});
  test "a return in a branch returns its value, and later branches are not spawned" (fun () ->
      expect_main ~expected:"first ran\nsecond ran\nafter the block\n1\n7\n"
        {|fn leaves(early: Bool) -> Int64
  uses Tasks, Console
{
  concurrent {
    {
      if early {
        return 7
      }
      Console.print_line("first ran")
    }
    Console.print_line("second ran")
  }
  Console.print_line("after the block")
  1
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  Console.print_line("${leaves(early: false)}")
  Console.print_line("${leaves(early: true)}")
  ExitCode.success
}
|});
  test "a ? in a branch returns the error and drops the lets of the other branches" (fun () ->
      expect_main ~expected:"sum 5\nfailed at second\nfailed at first\n"
        {|type Failed(at: String)

fn checked(text: own String, good: Bool) -> Result[String, Failed] {
  if good {
    Ok(own text)
  } else {
    Err(Failed(at: own text))
  }
}

fn both(first: Bool, second: Bool) -> Result[USize, Failed]
  uses Tasks
{
  concurrent {
    let left = checked("first", good: first)?
    let right = checked("second", good: second)?
  }
  Ok(left.length() + right.length() - 6)
}

fn report(first: Bool, second: Bool)
  uses Tasks, Console
{
  match both(first, second: second) {
    Ok(sum) => Console.print_line("sum ${sum}")
    Err(failed) => Console.print_line("failed at ${failed.at}")
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  report(true, second: true)
  report(true, second: false)
  report(false, second: false)
  ExitCode.success
}
|});
  test "a task returns a result that is passed through a pointer" (fun () ->
      expect_main ~expected:"early 4 late 5\n"
        {|type Big(first: Int64, second: Int64, third: Int64, fourth: Int64, name: String)

fn big(early: Bool) -> Big
  uses Tasks
{
  concurrent {
    if early {
      return Big(first: 1, second: 2, third: 3, fourth: 4, name: "early")
    }
  }
  Big(first: 5, second: 6, third: 7, fourth: 8, name: "late")
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  let early = big(early: true)
  let late = big(early: false)
  Console.print_line("${early.name} ${early.fourth} ${late.name} ${late.first}")
  ExitCode.success
}
|});
  test "break and continue in a branch apply to the loop that encloses the block" (fun () ->
      expect_main ~expected:"round 0\nbeside round 0\nround 2\nbeside round 2\n2\n"
        {|fn rounds(count: Int64) -> Int64
  uses Tasks, Console
{
  var total: Int64 = 0
  for round in 0..count {
    concurrent {
      {
        if round == 1 {
          continue
        }
        if round == 3 {
          break
        }
        Console.print_line("round ${round}")
      }
      Console.print_line("beside round ${round}")
    }
    total += 1
  }
  total
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  Console.print_line("${rounds(6)}")
  ExitCode.success
}
|})

(* Loops *)

let () =
  test "continue ends one iteration, break cancels the loop, and return returns a value" (fun () ->
      expect_main
        ~expected:
          "iteration 0\n\
           iteration 1\n\
           iteration 3\n\
           before the break 0\n\
           after the loop\n\
           looked at 0\n\
           looked at 1\n\
           20\n\
           looked at 0\n\
           looked at 1\n\
           looked at 2\n\
           -1\n"
        {|fn skips(count: Int64)
  uses Tasks, Console
{
  concurrent for index in 0..count {
    if index == 2 {
      continue
    }
    Console.print_line("iteration ${index}")
  }
}

fn stops(count: Int64)
  uses Tasks, Console
{
  concurrent for index in 0..count {
    if index == 1 {
      break
    }
    Console.print_line("before the break ${index}")
  }
  Console.print_line("after the loop")
}

fn find(count: Int64, wanted: Int64) -> Int64
  uses Tasks, Console
{
  concurrent for index in 0..count {
    if index == wanted {
      return index * 10
    }
    Console.print_line("looked at ${index}")
  }
  -1
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  skips(4)
  stops(4)
  Console.print_line("${find(5, wanted: 2)}")
  Console.print_line("${find(3, wanted: 9)}")
  ExitCode.success
}
|});
  test "a return ends every enclosing task and carries its value through each" (fun () ->
      expect_main
        ~expected:
          "checked item 0\n\
           beside item 0\n\
           done item 0\n\
           found item 1\n\
           checked item 0\n\
           beside item 0\n\
           done item 0\n\
           checked item 1\n\
           beside item 1\n\
           done item 1\n\
           none\n"
        {|fn nested(count: Int64, wanted: Int64) -> String
  uses Tasks, Console
{
  concurrent for index in 0..count {
    let label = "item ${index}"
    concurrent {
      {
        if index == wanted {
          return "found ${label}"
        }
        Console.print_line("checked ${label}")
      }
      Console.print_line("beside ${label}")
    }
    Console.print_line("done ${label}")
  }
  "none"
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  Console.print_line(nested(3, wanted: 1))
  Console.print_line(nested(2, wanted: 5))
  ExitCode.success
}
|});
  test "break and continue in a branch apply to the enclosing concurrent for" (fun () ->
      expect_main ~expected:"first 0\nbeside 0\nafter block 0\nafter the loop\n"
        {|fn search(count: Int64)
  uses Tasks, Console
{
  concurrent for index in 0..count {
    concurrent {
      {
        if index == 1 {
          continue
        }
        if index == 2 {
          break
        }
        Console.print_line("first ${index}")
      }
      Console.print_line("beside ${index}")
    }
    Console.print_line("after block ${index}")
  }
  Console.print_line("after the loop")
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  search(5)
  ExitCode.success
}
|});
  test "a concurrent for over a range of characters and over a range of negative Int8 values"
    (fun () ->
      expect_main ~expected:"letter a\nletter b\nletter c\nsmall -2\nsmall -1\nsmall 0\n"
        {|fn ranges(low: Int8, high: Int8)
  uses Tasks, Console
{
  concurrent for letter in Character"a"..=Character"c" {
    Console.print_line("letter ${letter}")
  }
  concurrent for small in low..high {
    Console.print_line("small ${small}")
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  ranges(-2, high: 1)
  ExitCode.success
}
|});
  test "tasks call a capability implementation that is provided outside the loop" (fun () ->
      expect_main ~expected:"total 10\n"
        {|type Counter(count: Int64)

capability Tally {
  fn add(amount: Int64)
  fn total() -> Int64
}

impl Tally for Counter {
  fn add(mut self, amount: Int64) {
    self.count += amount
  }

  fn total(self) -> Int64 {
    self.count
  }
}

fn tallied(count: Int64) -> Int64
  uses Tasks, Tally
{
  concurrent for index in 1..=count {
    Tally.add(index)
  }
  Tally.total()
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var counter = Counter(count: 0)
  let total = provide mut counter {
    tallied(4)
  }
  Console.print_line("total ${total}")
  ExitCode.success
}
|});
  test "a concurrent for over mut elements gives each task its own element" (fun () ->
      expect_main ~expected:"2 4 6\n2 4 3 at 3\n"
        {|fn doubled(items: mut List[Int64])
  uses Tasks
{
  concurrent for item in mut items {
    item = item * 2
  }
}

fn doubled_until(items: mut List[Int64], stop: Int64) -> Int64
  uses Tasks
{
  concurrent for item in mut items {
    if item == stop {
      return item
    }
    item = item * 2
  }
  0
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var numbers: List[Int64] = [1, 2, 3]
  doubled(mut numbers)
  Console.print_line("${numbers[0]} ${numbers[1]} ${numbers[2]}")
  var others: List[Int64] = [1, 2, 3, 4]
  let stopped = doubled_until(mut others, stop: 3)
  Console.print_line("${others[0]} ${others[1]} ${others[2]} at ${stopped}")
  ExitCode.success
}
|});
  test "a concurrent for over a cursor and over a method that yields owned values" (fun () ->
      expect_main
        ~expected:"pulled left 3\npulled left 2\npulled left 1\ninlined left 4\ninlined left 3\n2\n"
        {|fn countdown(from: Int64) yields own String {
  var left = from
  while left > 0 {
    yield "left ${left}"
    left -= 1
  }
}

fn cursors() -> Int64
  uses Tasks, Console
{
  var lines = countdown(3)
  concurrent for line in lines {
    Console.print_line("pulled ${line}")
  }
  concurrent for line in countdown(4) {
    if line == "left 2" {
      return 2
    }
    Console.print_line("inlined ${line}")
  }
  0
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  Console.print_line("${cursors()}")
  ExitCode.success
}
|});
  test "a task gets a copy of a trivial value that a method yields read-only" (fun () ->
      expect_main ~expected:"saw 5\nsaw 6\nsaw 7\n"
        {|type Bag(items: List[Int64])

fn Bag.each(self) yields Int64 {
  var index: USize = 0
  while index < self.items.length() {
    yield self.items[index]
    index += 1
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  let bag = Bag(items: [5, 6, 7])
  concurrent for item in bag {
    Console.print_line("saw ${item}")
  }
  ExitCode.success
}
|})

(* Ownership of items and return values *)

let () =
  passes_in_order "a task owns its item, and an item whose task is not spawned is dropped" ~count:2
    {|fn longest(words: own List[String], limit: USize) -> String
  uses Tasks
{
  concurrent for word in own words {
    if word.length() > limit {
      return own word
    }
  }
  "none"
}

test "a task returns the item it was given" {
  var tasks = InOrder(opened: 0, cancelled: [])
  let found = provide mut tasks {
    longest(["a", "abcdef", "abc", "abcdefgh"], limit: 4)
  }
  assert found == "abcdef"
}

test "every item is taken when no task leaves" {
  var tasks = InOrder(opened: 0, cancelled: [])
  let found = provide mut tasks {
    longest(["a", "ab", "abc"], limit: 4)
  }
  assert found == "none"
}
|};
  passes_in_order "a value returned through two nested tasks is neither leaked nor dropped twice"
    ~count:1
    {|fn nested(count: Int64, wanted: Int64) -> List[String]
  uses Tasks
{
  concurrent for index in 0..count {
    concurrent {
      let beside = "beside ${index}"
      if index == wanted {
        return ["item ${index}", "found"]
      }
    }
    if beside.length() == 0 {
      return []
    }
  }
  []
}

test "the list is the function's result" {
  var tasks = InOrder(opened: 0, cancelled: [])
  let found = provide mut tasks {
    nested(4, wanted: 2)
  }
  assert found.length() == 2
  assert found[0] == "item 2"
  var again = InOrder(opened: 0, cancelled: [])
  let none = provide mut again {
    nested(2, wanted: 7)
  }
  assert none.length() == 0
}
|}

(* Programs that are reported as not built *)

let unsupported name ~message text =
  test name (fun () ->
      match run_main text with
      | exception Failure raised -> expect_string ~expected:message raised
      | _ -> fail "the program was built")

let () =
  unsupported "a concurrent for over a method that yields borrowed places of a non-trivial type"
    ~message:
      "example/main.truss:15:3: Stage0 cannot build this yet: a `concurrent for` over \
       `example::main::Bag.each`, which yields borrowed places and whose body is not a single \
       `for` over a range."
    {|type Bag(items: List[String])

fn Bag.each(self) yields String {
  var index: USize = 0
  while index < self.items.length() {
    yield self.items[index]
    index += 1
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  let bag = Bag(items: ["a", "b"])
  concurrent for item in bag {
    Console.print_line(item)
  }
  ExitCode.success
}
|};
  unsupported "concurrent code in a pulled method"
    ~message:
      "example/main.truss:5:3: Stage0 cannot build this yet: `concurrent` code in a yielding \
       method that is pulled."
    {|fn counted(limit: Int64) yields own Int64
  uses Tasks
{
  var total: Int64 = 0
  concurrent {
    total = limit
  }
  yield total
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var cursor = counted(3)
  if mut cursor.next() is Some(value) {
    Console.print_line("${value}")
  }
  ExitCode.success
}
|}

let () = Harness.finish ()
