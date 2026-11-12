(* [concurrent] blocks and loops. Whole programs use the runtime's [Tasks],
   which runs each task when it is spawned. Truss tests provide a [Tasks]
   written in Truss, and the test runner fails a test that leaks a heap
   block. *)

open Codegen_support

(* The output of a program whose tasks run sequentially, in the order they
   are spawned, so that the output shows which tasks ran. *)
let expect_main ~expected text =
  let status, output, errors = run_main ~in_order:true text in
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
    let built = "made"
    let lengths = ["a", "bb", "ccc"].map(fn(text) { text.length() })
  }
  Console.print_line("${pair.first} ${pair.second} ${built} ${lengths[2]}")
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
  test "tasks spawned inside a provide block capture its evidence" (fun () ->
      expect_main ~expected:"total 10 then 110\n"
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

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var counter = Counter(count: 0)
  provide mut counter {
    concurrent for index in 1..=4 {
      Tally.add(index)
    }
    let first = Tally.total()
    concurrent {
      Tally.add(40)
      Tally.add(60)
    }
    Console.print_line("total ${first} then ${Tally.total()}")
  }
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
  passes_in_order "a task borrows an element that a method lends from a read-only parameter"
    ~count:3
    {|type Bag(items: List[String])

fn Bag.each(self) yields String {
  var index: USize = 0
  while index < self.items.length() {
    yield self.items[index]
    index += 1
  }
}

fn total_length(words: List[String]) -> USize
  uses Tasks
{
  concurrent for word in words {
    if word.length() > 100 {
      return word.length()
    }
  }
  var total: USize = 0
  for word in words {
    total += word.length()
  }
  total
}

fn first_longer(bag: Bag, limit: USize) -> String
  uses Tasks
{
  concurrent for word in bag {
    if word.length() > limit {
      return word.copy()
    }
  }
  "none"
}

test "every element is still owned by the list after the loop" {
  var tasks = InOrder(opened: 0, cancelled: [])
  let length = provide mut tasks {
    total_length(["a${1}", "bc${2}", "def${3}"])
  }
  assert length == 9
}

test "a task that returns ends the loop, and later elements are not spawned" {
  var tasks = InOrder(opened: 0, cancelled: [])
  let bag = Bag(items: ["a${1}", "abcdef${2}", "abc${3}", "abcdefgh${4}"])
  let present = provide mut tasks {
    first_longer(bag, limit: 4)
  }
  assert present == "abcdef2"
  assert bag.items.length() == 4
  assert bag.items[3] == "abcdefgh4"
}

test "no task returns" {
  var tasks = InOrder(opened: 0, cancelled: [])
  let bag = Bag(items: ["a${1}", "ab${2}"])
  let present = provide mut tasks {
    first_longer(bag, limit: 9)
  }
  assert present == "none"
}
|};
  passes_in_order "a task owns a value that a method computes, and copies a plain one" ~count:2
    {|type Counter(count: Int64)

fn Counter.labels(self) yields String {
  var index: Int64 = 0
  while index < self.count {
    yield "label ${index}"
    index += 1
  }
}

fn Counter.steps(mut self) yields Int64 {
  while self.count > 0 {
    yield self.count
    self.count -= 1
  }
}

fn label_lengths(counter: Counter, stop: Int64) -> USize
  uses Tasks
{
  concurrent for label in counter.labels() {
    if label == "label ${stop}" {
      return label.length()
    }
  }
  0
}

fn sum_steps(counter: mut Counter) -> Int64
  uses Tasks, Tally
{
  concurrent for step in mut counter.steps() {
    Tally.add(step)
  }
  Tally.total()
}

capability Tally {
  fn add(amount: Int64)
  fn total() -> Int64
}

type Sum(total: Int64)

impl Tally for Sum {
  fn add(mut self, amount: Int64) {
    self.total += amount
  }

  fn total(self) -> Int64 {
    self.total
  }
}

test "a computed value is dropped by its task or by the loop" {
  var tasks = InOrder(opened: 0, cancelled: [])
  provide mut tasks {
    assert label_lengths(Counter(count: 4), stop: 2) == 7
    assert label_lengths(Counter(count: 3), stop: 9) == 0
  }
}

test "a plain value lent from a mut parameter is copied" {
  var tasks = InOrder(opened: 0, cancelled: [])
  var sum = Sum(total: 0)
  var counter = Counter(count: 4)
  let total = provide mut tasks, mut sum {
    sum_steps(mut counter)
  }
  assert total == 10
  assert counter.count == 0
}
|}

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
  let present = provide mut tasks {
    longest(["a", "abcdef", "abc", "abcdefgh"], limit: 4)
  }
  assert present == "abcdef"
}

test "every item is taken when no task leaves" {
  var tasks = InOrder(opened: 0, cancelled: [])
  let present = provide mut tasks {
    longest(["a", "ab", "abc"], limit: 4)
  }
  assert present == "none"
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
  let present = provide mut tasks {
    nested(4, wanted: 2)
  }
  assert present.length() == 2
  assert present[0] == "item 2"
  var again = InOrder(opened: 0, cancelled: [])
  let none = provide mut again {
    nested(2, wanted: 7)
  }
  assert none.length() == 0
}
|}

(* Tasks on threads *)

let expect_threaded ~expected text =
  let status, output, errors = run_main text in
  if status <> 0 then fail "ended with status %d: %s" status errors;
  expect_string ~expected output

let () =
  test "on threads, calls of a mut implementation by many tasks are mutually exclusive" (fun () ->
      expect_threaded ~expected:"total 40000 after 40000 calls\n"
        {|type Counter(count: Int64, calls: Int64)

capability Tally {
  fn add(amount: Int64)
  fn total() -> Int64
  fn calls() -> Int64
}

impl Tally for Counter {
  fn add(mut self, amount: Int64) {
    let before = self.count
    self.calls += 1
    self.count = before + amount
  }

  fn total(self) -> Int64 {
    self.count
  }

  fn calls(self) -> Int64 {
    self.calls
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var counter = Counter(count: 0, calls: 0)
  provide mut counter {
    concurrent for task in 0..8 {
      for step in 0..5000 {
        if task >= 0 && step >= 0 {
          Tally.add(1)
        }
      }
    }
    Console.print_line("total ${Tally.total()} after ${Tally.calls()} calls")
  }
  ExitCode.success
}
|});
  test "on threads, a task that waits on a key runs again when another task wakes the key"
    (fun () ->
      expect_threaded ~expected:"saw the flag\n"
        {|type Flag(raised: Bool)

capability Flags {
  fn raise()
  fn raised() -> Bool
}

impl Flags for Flag {
  fn raise(mut self) {
    self.raised = true
  }

  fn raised(self) -> Bool {
    self.raised
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var flag = Flag(raised: false)
  provide mut flag {
    concurrent {
      {
        var seen = false
        while !seen {
          let ticket = Tasks.watch(7)
          if Flags.raised() {
            seen = true
          } else {
            Tasks.wait(7, ticket: ticket, reason: "the flag")
          }
        }
        Console.print_line("saw the flag")
      }
      {
        Tasks.yield_now()
        Flags.raise()
        Tasks.wake(7)
      }
    }
  }
  ExitCode.success
}
|});
  test "on threads, a return cancels a blocked task and the tasks it has spawned" (fun () ->
      expect_threaded ~expected:"5 cancelled true and nested true\n"
        {|type Seen(outer: Bool, nested: Bool)

capability Report {
  fn outer(cancelled: Bool)
  fn nested(cancelled: Bool)
  fn text() -> String
}

impl Report for Seen {
  fn outer(mut self, cancelled: Bool) {
    self.outer = cancelled
  }

  fn nested(mut self, cancelled: Bool) {
    self.nested = cancelled
  }

  fn text(self) -> String {
    "cancelled ${self.outer} and nested ${self.nested}"
  }
}

fn blocked()
  uses Tasks, Report
{
  var waiting = true
  while waiting {
    let ticket = Tasks.watch(9)
    if Tasks.cancelled() {
      waiting = false
    } else {
      Tasks.wait(9, ticket: ticket, reason: "a key that is never woken")
    }
  }
  Report.outer(Tasks.cancelled())
  concurrent {
    Report.nested(Tasks.cancelled())
  }
}

fn race() -> Int64
  uses Tasks, Report
{
  concurrent {
    blocked()
    {
      Tasks.yield_now()
      return 5
    }
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var seen = Seen(outer: false, nested: false)
  provide mut seen {
    let winner = race()
    Console.print_line("${winner} ${Report.text()}")
  }
  ExitCode.success
}
|});
  test "on threads, tasks take ownership of their items and free the blocks" (fun () ->
      expect_threaded ~expected:"total 1400\n"
        {|type Sum(total: USize)

capability Lengths {
  fn add(length: USize)
  fn total() -> USize
}

impl Lengths for Sum {
  fn add(mut self, length: USize) {
    self.total += length
  }

  fn total(self) -> USize {
    self.total
  }
}

fn labels(count: Int64) yields own String {
  var index: Int64 = 0
  while index < count {
    yield "label number ${index % 10}"
    index += 1
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var sum = Sum(total: 0)
  provide mut sum {
    concurrent for label in labels(100) {
      Lengths.add(label.length())
    }
    Console.print_line("total ${Lengths.total()}")
  }
  ExitCode.success
}
|})

(* The scheduler, with each number of threads *)

let expect_with_each_thread_count ~expected text =
  Fun.protect
    ~finally:(fun () -> Unix.putenv "TRUSS_WORKERS" "")
    (fun () ->
      List.iter
        (fun workers ->
          Unix.putenv "TRUSS_WORKERS" (string_of_int workers);
          expect_threaded ~expected text)
        worker_counts)

let tally =
  {|type Counter(count: Int64)

capability Tally {
  fn add(amount: Int64)
  fn total() -> Int64
}

impl Tally for Counter {
  fn add(mut self, amount: Int64) {
    let before = self.count
    self.count = before + amount
  }

  fn total(self) -> Int64 {
    self.count
  }
}
|}

let () =
  test "on threads, nested groups of tasks park, yield, block, and lock with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"total 2000\n"
        (tally
       ^ {|
fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Clock, Console
{
  var counter = Counter(count: 0)
  provide mut counter {
    concurrent for outer in 0..40 {
      concurrent for inner in 0..50 {
        if (outer + inner) % 10 == 0 {
          Clock.sleep(Duration.nanoseconds(1000000))
        }
        if inner % 7 == 0 {
          Tasks.yield_now()
        }
        Tally.add(1)
      }
    }
    Console.print_line("total ${Tally.total()}")
  }
  ExitCode.success
}
|}
        ));
  (* A flag that the runs shared would let one run drop a value that
     another had moved, or leave one that it still owned. *)
  test "on threads, each run of a concurrent for and of a parallel for has its own drop flags"
    (fun () ->
      expect_threaded ~expected:"total 3000\nparallel total 2000\n"
        (tally
       ^ {|
fn label(index: Int64) -> Result[String, String] {
  if index % 2 == 0 {
    Ok("even ${index}")
  } else {
    Err("odd ${index}")
  }
}

fn held(text: own String) -> Int64 {
  if text.length() > 0 { 1 } else { 0 }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var counter = Counter(count: 0)
  provide mut counter {
    concurrent for index in 0..2000 {
      match label(index) {
        Ok(text) => Tally.add(held(own text))
        Err(_) => Tally.add(2)
      }
    }
    Console.print_line("total ${Tally.total()}")
  }
  var sums: List[Int64] = []
  for _ in 0..2000 {
    mut sums.push(0)
  }
  parallel for sum in mut sums {
    match label(sum) {
      Ok(text) => {
        sum = held(own text)
      }
      Err(_) => {
        sum = 2
      }
    }
  }
  var total = 0
  for sum in sums {
    total += sum
  }
  Console.print_line("parallel total ${total}")
  ExitCode.success
}
|}
        ));
  test "on threads, tasks run parallel blocks and loops with any number of threads" (fun () ->
      expect_with_each_thread_count ~expected:"total 40064\n"
        (tally
       ^ {|
fn fib(n: Int64) -> Int64 {
  if n < 2 {
    return n
  }
  parallel {
    let left = fib(n - 1)
    let right = fib(n - 2)
  }
  left.wrapping_add(right)
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console
{
  var counter = Counter(count: 0)
  provide mut counter {
    concurrent for _ in 0..64 {
      Tasks.yield_now()
      Tally.add(fib(15))
      var numbers: List[Int64] = [1, 2, 3, 4, 5, 6, 7, 8]
      parallel for item in mut numbers {
        item = item * 2
      }
      Tally.add(numbers[7])
    }
    Console.print_line("total ${Tally.total()}")
  }
  ExitCode.success
}
|}
        ));
  (* The seeded scheduler runs its tasks as coroutines. [add] yields to the
     program's scheduler in one, so the task resumes on another thread
     while it is in a coroutine, and the other tasks park in theirs for
     the mutex. The coroutine then suspends on that thread, when it yields
     to the seeded scheduler. *)
  test "on threads, a task that leaves its thread in a coroutine resumes with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"total 1920\n"
        {|use standard::tasks

type Counter(count: Int64)

capability Tally {
  fn add(amount: Int64)
  fn total() -> Int64
}

impl Tally for Counter
  uses Tasks
{
  fn add(mut self, amount: Int64) {
    let before = self.count
    Tasks.yield_now()
    self.count = before + amount
  }

  fn total(self) -> Int64 {
    self.count
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console, Panic
{
  var counter = Counter(count: 0)
  provide mut counter {
    concurrent for _ in 0..32 {
      provide tasks::SeededTasks.new(7) {
        concurrent for _ in 0..30 {
          Tally.add(1)
          Tasks.yield_now()
          Tally.add(1)
        }
      }
    }
    Console.print_line("total ${Tally.total()}")
  }
  ExitCode.success
}
|})

(* Waiting for time and for a socket *)

let () =
  (* A sleeping task that held a thread would keep the last task from
     running until a sleep ended: the runtime has fewer threads than this
     program has sleeping tasks. *)
  test "on threads, more tasks sleep at once than the runtime has threads" (fun () ->
      expect_threaded ~expected:"600 woke first, before a sleep ended true\n"
        {|fn first_to_wake(sleepers: Int64) -> Int64
  uses Tasks, Clock
{
  concurrent for sleeper in 0..=sleepers {
    if sleeper == sleepers {
      return sleeper
    }
    Clock.sleep(Duration.nanoseconds(60000000000))
  }
  -1
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Clock, Console
{
  let before = Clock.monotonic()
  let first = first_to_wake(600)
  let after = Clock.monotonic()
  Console.print_line("${first} woke first, before a sleep ended ${after.total_seconds() - before.total_seconds() < 30}")
  ExitCode.success
}
|});
  test "on threads, tasks connect, accept, read, and write on sockets with any number of threads"
    (fun () ->
      expect_with_each_thread_count ~expected:"echoed 16\n"
        ({|use standard::network

|} ^ tally
       ^ {|
fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console, NetworkServer, NetworkClient, Handles
{
  let loopback = network::SocketAddress(address: network::IpAddress.loopback, port: 0)
  var counter = Counter(count: 0)
  if NetworkServer.listen(loopback) is Ok(opened) {
    var listener = own opened
    let at = listener.local_address()
    provide mut counter {
      concurrent {
        {
          for _ in 0..16 {
            if mut listener.accept() is Ok(moved) {
              var server = own moved
              var heard: List[UInt8] = []
              if mut server.read(mut heard, limit: 100) is Ok(_) {
                let _ = mut server.write(heard.slice())
              }
            }
          }
        }
        concurrent for _ in 0..16 {
          if NetworkClient.connect(at, timeout: None) is Ok(built) {
            var client = own built
            let request: List[UInt8] = [7, 8, 9]
            let _ = mut client.write(request.slice())
            var answer: List[UInt8] = []
            if mut client.read(mut answer, limit: 100) is Ok(count) {
              if count == 3 && answer[2] == 9 {
                Tally.add(1)
              }
            }
          }
        }
      }
      Console.print_line("echoed ${Tally.total()}")
    }
  }
  ExitCode.success
}
|}
        ));
  test "on threads, a read in a task ends at the socket's time limit" (fun () ->
      expect_threaded ~expected:"timed out true\nthe peer closed true\n"
        {|use standard::network

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console, NetworkServer, NetworkClient, Handles
{
  let loopback = network::SocketAddress(address: network::IpAddress.loopback, port: 0)
  if NetworkServer.listen(loopback) is Ok(opened) {
    var listener = own opened
    let at = listener.local_address()
    concurrent {
      {
        if NetworkClient.connect(at, timeout: Some(Duration.nanoseconds(2000000000))) is Ok(built) {
          var client = own built
          let _ = mut client.set_read_timeout(Some(Duration.nanoseconds(50000000)))
          var heard: List[UInt8] = []
          if mut client.read(mut heard, limit: 10) is Err(error) {
            Console.print_line("timed out ${error == SystemError.TimedOut}")
          }
        }
      }
      {
        if mut listener.accept() is Ok(moved) {
          var server = own moved
          var heard: List[UInt8] = []
          if mut server.read(mut heard, limit: 10) is Ok(count) {
            Console.print_line("the peer closed ${count == 0}")
          }
        }
      }
    }
  }
  ExitCode.success
}
|})

(* A child's pipes. Each of the child's two outputs is larger than a pipe
   holds, so the child ends only if both are read as it writes them. *)

let child_lines =
  {|use standard::processes

fn lines(count: Int64) -> processes::Command {
  processes::Command.new("awk")
    .argument("BEGIN { for (i = 0; i < ${count}; i++) { print \"out-line-\" i; print \"err-line-\" i > \"/dev/stderr\" } }")
    .output(processes::Redirect.Capture)
    .error_output(processes::Redirect.Capture)
}
|}

let () =
  test "on threads, tasks read and write the pipes of child processes with any number of threads"
    (fun () ->
      expect_with_each_thread_count
        ~expected:"captured 110890 and 110890\ncaptured from many\nechoed 262144\n"
        (child_lines
       ^ {|
fn echoed(through: mut processes::Child, count: USize) -> USize
  uses Tasks, Handles, Panic
{
  var input = mut through.take_input().unwrap()
  var output = mut through.take_output().unwrap()
  var got: USize = 0
  concurrent {
    {
      var block: List[UInt8] = []
      for _ in 0..4096 {
        mut block.push(65)
      }
      var written: USize = 0
      while written < count {
        written += mut input.write(block.slice()).unwrap()
      }
      let _ = own input.close()
    }
    {
      var heard: List[UInt8] = []
      var open = true
      while open {
        mut heard.clear()
        let read = mut output.read(mut heard, limit: 65536).unwrap()
        got += read
        open = read > 0
      }
    }
  }
  got
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Console, Processes, Handles, Panic
{
  match Processes.run(lines(8000)) {
    Ok(output) => Console.print_line("captured ${output.output.length()} and ${output.error_output.length()}")
    Err(error) => Console.print_line("run: ${error}")
  }
  concurrent for index in 0..12 {
    match Processes.run(lines(7)) {
      Ok(output) => {
        if output.output.length() != 77 || output.error_output.length() != 77 {
          Console.print_line("child ${index} gave ${output.output.length()} and ${output.error_output.length()}")
        }
      }
      Err(error) => Console.print_line("run: ${error}")
    }
  }
  Console.print_line("captured from many")
  let cat = processes::Command.new("cat")
    .input(processes::Redirect.Pipe)
    .output(processes::Redirect.Pipe)
  match Processes.spawn(cat) {
    Ok(child) => {
      var through = own child
      Console.print_line("echoed ${echoed(mut through, count: 262144)}")
      let _ = mut through.wait()
    }
    Err(error) => Console.print_line("spawn: ${error}")
  }
  ExitCode.success
}
|}
        ));
  test "in a program with one thread, both of a child's outputs are captured whole" (fun () ->
      expect_main ~expected:"captured 110890 and 110890\n"
        (child_lines
       ^ {|
fn main(arguments: List[String]) -> ExitCode
  uses Console, Processes
{
  match Processes.run(lines(8000)) {
    Ok(output) => Console.print_line("captured ${output.output.length()} and ${output.error_output.length()}")
    Err(error) => Console.print_line("run: ${error}")
  }
  ExitCode.success
}
|}
        ))

(* Cancelling a task that waits *)

let () =
  (* The child's output is discarded. A child that inherited the program's
     output would keep it open after the program ended, and the test would
     wait for the child to end. *)
  test "on threads, a cancelled task returns from a call that blocks in the operating system"
    (fun () ->
      expect_threaded ~expected:"run: cancelled\ntimed out\n"
        {|use standard::processes

fn run_or_time_out() -> String
  uses Tasks, Clock, Console, Processes
{
  concurrent {
    {
      let slow = processes::Command.new("sleep")
        .argument("5")
        .output(processes::Redirect.Discard)
        .error_output(processes::Redirect.Discard)
      match Processes.run(slow) {
        Ok(_) => Console.print_line("run: ended")
        Err(error) => Console.print_line("run: ${error}")
      }
    }
    {
      Clock.sleep(Duration.nanoseconds(100000000))
      return "timed out"
    }
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Clock, Console, Processes
{
  Console.print_line(run_or_time_out())
  ExitCode.success
}
|});
  test "on threads, a cancelled task returns early from a sleep" (fun () ->
      expect_threaded ~expected:"1 early true\n"
        {|fn nap(seconds: Int64) -> Int64
  uses Tasks, Clock
{
  concurrent {
    Clock.sleep(Duration.nanoseconds(seconds * 1000000000))
    {
      Clock.sleep(Duration.nanoseconds(50000000))
      return 1
    }
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Clock, Console
{
  let before = Clock.monotonic()
  let result = nap(60)
  let after = Clock.monotonic()
  Console.print_line("${result} early ${after.total_seconds() - before.total_seconds() < 20}")
  ExitCode.success
}
|});
  test "on threads, an accept in a cancelled task returns the cancelled error" (fun () ->
      expect_threaded ~expected:"accept: cancelled\ntimed out\n"
        {|use standard::network

fn accept_or_time_out() -> String
  uses Tasks, Clock, Console, NetworkServer, Handles
{
  let loopback = network::SocketAddress(address: network::IpAddress.loopback, port: 0)
  if NetworkServer.listen(loopback) is Ok(opened) {
    var listener = own opened
    concurrent {
      {
        match mut listener.accept() {
          Ok(_) => Console.print_line("accept: a connection")
          Err(error) => Console.print_line("accept: ${error}")
        }
      }
      {
        Clock.sleep(Duration.nanoseconds(50000000))
        return "timed out"
      }
    }
  }
  "could not listen"
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Clock, Console, NetworkServer, Handles
{
  Console.print_line(accept_or_time_out())
  ExitCode.success
}
|});
  test "on threads, a wait for signals in a cancelled task returns None" (fun () ->
      expect_threaded ~expected:"no signal\ntimed out\n"
        {|use standard::processes

fn signal_or_time_out() -> String
  uses Tasks, Clock, Console, Signals
{
  let wanted = [processes::Signal.User2]
  concurrent {
    {
      if Signals.wait(wanted.slice()) is Some(_) {
        Console.print_line("a signal")
      } else {
        Console.print_line("no signal")
      }
    }
    {
      Clock.sleep(Duration.nanoseconds(50000000))
      return "timed out"
    }
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Clock, Console, Signals
{
  Console.print_line(signal_or_time_out())
  ExitCode.success
}
|});
  test "on threads, a cancelled task returns from a wait for a child's output" (fun () ->
      expect_threaded ~expected:"run: cancelled\ntimed out\n"
        {|use standard::processes

fn run_or_time_out() -> String
  uses Tasks, Clock, Console, Processes
{
  concurrent {
    {
      let slow = processes::Command.new("sleep")
        .argument("5")
        .output(processes::Redirect.Capture)
        .error_output(processes::Redirect.Capture)
      match Processes.run(slow) {
        Ok(_) => Console.print_line("run: ended")
        Err(error) => Console.print_line("run: ${error}")
      }
    }
    {
      Clock.sleep(Duration.nanoseconds(100000000))
      return "timed out"
    }
  }
}

fn main(arguments: List[String]) -> ExitCode
  uses Tasks, Clock, Console, Processes
{
  Console.print_line(run_or_time_out())
  ExitCode.success
}
|})

(* Programs that are reported as not built *)

let unsupported name ~message text =
  test name (fun () ->
      match run_main text with
      | exception Failure raised -> expect_string ~expected:message raised
      | _ -> fail "the program was built")

let () =
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
