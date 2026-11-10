(* Truss source compiled and run: every value is dropped exactly once, on
   every way out of the code that owns it. A test passes only if it frees
   each block it allocates, which the runner checks. *)

open Codegen_support

let () =
  passes "an assignment to an element drops the element it replaces"
    {|test "replaced" {
  var names: List[String] = ["a${1}", "b${2}"]
  names[0] = "c${3}"
  assert names[0] == "c3"
}
|};
  passes "an early return inside an interpolation drops the text built so far"
    {|fn label(value: Option[Int64]) -> Option[String] {
  Some("number ${value?}")
}

test "left early" {
  assert label(None) == None
  assert label(Some(4)) == Some("number 4")
}
|};
  passes "an argument moved before a later argument returns early is dropped"
    {|fn pair(first: own String, second: Int64) -> Int64 {
  second
}

fn build(value: Option[Int64]) -> Option[Int64] {
  var text = "a${1}"
  Some(pair(own text, second: value?))
}

test "left early" {
  assert build(None) == None
  assert build(Some(2)) == Some(2)
}
|};
  passes "an early return while an any value is being made leaves no block"
    {|trait Shown {
  fn show(self) -> Int64
}

type Box(value: Int64)

impl Shown for Box {
  fn show(self) -> Int64 {
    self.value
  }
}

fn boxed(value: Option[Int64]) -> Option[any Shown] {
  Some(any Box(value: value?))
}

test "left early" {
  assert boxed(None) is None
  assert boxed(Some(3)) is Some(_)
}
|};
  passes "a pulled loop left without taking its value drops the value"
    {|fn words() yields own String {
  yield "a${1}"
  yield "b${2}"
}

test "left early" {
  var each = words()
  for _ in each {
    break
  }
}
|};
  passes "continue keeps a list a loop is over, when the list is a call's result"
    {|fn make() -> List[String] {
  ["a${1}", "bb${2}", "c${3}"]
}

test "skipped" {
  var count = 0
  for name in make() {
    if name.length() == 3 {
      continue
    }
    count += 1
  }
  assert count == 2
}
|};
  passes "a loop over a yielding function that takes nothing"
    {|fn ticks() yields Int64 {
  yield 1
  yield 2
}

test "looped" {
  var total = 0
  for tick in ticks() {
    total += tick
  }
  assert total == 3
}
|};
  passes "an own parameter left to its default is dropped once"
    {|fn total(items: own List[Int64] = [1, 2, 3]) -> Int64 {
  var sum = 0
  for item in items {
    sum += item
  }
  sum
}

test "defaulted" {
  assert total() == 6
  assert total(items: [4, 5]) == 9
}
|};
  passes "a lambda that ignores an own parameter drops it"
    {|fn apply(text: own String, using: fn(own String) -> Int64) -> Int64 {
  using(own text)
}

test "ignored" {
  assert apply("a${1}", using: fn(_) { 7 }) == 7
}
|};
  passes "a compound assignment evaluates its target once"
    {|fn next_index(calls: mut Int64) -> USize {
  calls += 1
  0
}

test "once" {
  var items: List[Int64] = [10, 20]
  var calls = 0
  items[next_index(mut calls)] += 5
  assert calls == 1
  assert items[0] == 15
}
|};
  passes "a result assigned over its own argument reads the argument as it was"
    {|type Quad(a: Int64, b: Int64, c: Int64, d: Int64)

fn swapped(q: Quad) -> Quad {
  q with (a: q.b, b: q.a)
}

test "swapped" {
  var q = Quad(a: 1, b: 2, c: 3, d: 4)
  q = swapped(q)
  assert q.a == 2
  assert q.b == 1
}
|}

let () = Harness.finish ()
