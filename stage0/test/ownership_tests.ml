(* The tests of moves, loans, and views. See TYPECHECKER.md, "Ownership:
   moves, loans, and views". *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Infer.diagnostics database module_
  @ Patterns.diagnostics database module_
  @ Usage.diagnostics database module_
  @ Ownership.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]
let keep = "fn keep(items: own List[Int64]) {}\n\nfn look(items: List[Int64]) {}\n\n"

let () =
  test "a moved place cannot be used, with a fix that copies at the move" (fun () ->
      one_diagnostic
        (keep ^ "fn f(items: own List[Int64]) {\n  keep(own items)\n  look(items)\n}\n")
        "ownership.use_after_move"
        ~fixed:(keep ^ "fn f(items: own List[Int64]) {\n  keep(items.copy())\n  look(items)\n}\n"));
  test "a place that copies implicitly is copied, not moved" (fun () ->
      fine "fn take(count: own Int64) {}\n\nfn f(count: Int64) {\n  take(count)\n  take(count)\n}\n");
  test "a place moved on one path cannot be used after the paths meet" (fun () ->
      one_diagnostic
        (keep
       ^ "fn f(items: own List[Int64], ready: Bool) {\n\
         \  if ready {\n\
         \    keep(own items)\n\
         \  }\n\
         \  look(items)\n\
          }\n")
        "ownership.use_after_move");
  test "a place moved in a loop is moved in the loop's next iteration" (fun () ->
      one_diagnostic
        (keep
       ^ "fn f(items: own List[Int64], count: USize) {\n\
         \  for i in 0..count {\n\
         \    let _ = i\n\
         \    keep(own items)\n\
         \  }\n\
          }\n")
        "ownership.use_after_move");
  test "a place is usable again once it is assigned" (fun () ->
      fine
        (keep
       ^ "fn f(items: own List[Int64]) {\n\
         \  var current = own items\n\
         \  keep(own current)\n\
         \  current = []\n\
         \  look(current)\n\
          }\n"));
  test "a field can be moved out on its own" (fun () ->
      fine
        "type Config(name: String, port: UInt16)\n\n\
         fn take(name: own String) {}\n\n\
         fn f(config: own Config) -> UInt16 {\n\
        \  take(own config.name)\n\
        \  config.port\n\
         }\n");
  test "a read-only parameter cannot be moved" (fun () ->
      one_diagnostic
        (keep ^ "fn f(items: List[Int64]) {\n  keep(own items)\n}\n")
        "ownership.not_owned");
  test "a mut parameter's field moved out must be put back" (fun () ->
      one_diagnostic
        "type Config(name: String, port: UInt16)\n\n\
         fn take(name: own String) {}\n\n\
         fn f(config: mut Config) {\n\
        \  take(own config.name)\n\
         }\n"
        "ownership.field_not_restored");
  test "one place cannot be lent mut twice to one call" (fun () ->
      one_diagnostic
        "fn swap(first: mut Int64, second: mut Int64) {}\n\n\
         fn f() {\n\
        \  var first = 1\n\
        \  swap(mut first, second: mut first)\n\
         }\n"
        "ownership.conflicting_loan");
  test "a place cannot change while a view of it is in use" (fun () ->
      one_diagnostic
        "fn f() -> USize {\n\
        \  var items: List[Int64] = [1, 2, 3, 4, 5]\n\
        \  let middle = items[1..4]\n\
        \  mut items.push(9)\n\
        \  middle.length()\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a place can change once the view of it is no longer used" (fun () ->
      fine
        "fn f() -> USize {\n\
        \  var items: List[Int64] = [1, 2, 3, 4, 5]\n\
        \  let middle = items[1..4]\n\
        \  let total = middle.length()\n\
        \  mut items.push(9)\n\
        \  total\n\
         }\n");
  test "a function cannot return a view of its own local" (fun () ->
      one_diagnostic
        "fn f() -> Slice[Int64] {\n  let items: List[Int64] = [1, 2, 3]\n  items[0..2]\n}\n"
        "ownership.returns_local_view");
  test "a function can return a view of its parameter" (fun () ->
      fine "fn f(items: List[Int64]) -> Slice[Int64] {\n  items[0..2]\n}\n");
  test "a var needs an owned value, with fixes that give up or copy the place" (fun () ->
      one_diagnostic "fn f(items: own List[Int64]) {\n  var copy = items\n  mut copy.push(1)\n}\n"
        "ownership.needs_owned"
        ~fixed:"fn f(items: own List[Int64]) {\n  var copy = own items\n  mut copy.push(1)\n}\n");
  test "a list element needs an owned value" (fun () ->
      one_diagnostic "fn f(name: String) -> List[String] {\n  [name]\n}\n" "ownership.needs_owned");
  test "a lending method yields on every path" (fun () ->
      one_diagnostic
        "type Grid(cells: List[Int64])\n\n\
         fn Grid.cell(self, ready: Bool) lends Int64 {\n\
        \  if ready {\n\
        \    yield self.cells[0]\n\
        \  }\n\
         }\n"
        "ownership.lends_count");
  test "a yielding method that yields through recursion cannot be pulled" (fun () ->
      one_diagnostic
        "type Tree =\n\
        \  | Leaf\n\
        \  | indirect Node(left: Tree, value: Int64, right: Tree)\n\n\
         fn Tree.each(self) yields Int64 {\n\
        \  match self {\n\
        \    Leaf => {}\n\
        \    Node(left, value, right) => {\n\
        \      for item in left.each() {\n\
        \        yield item\n\
        \      }\n\
        \      yield value\n\
        \      for item in right.each() {\n\
        \        yield item\n\
        \      }\n\
        \    }\n\
        \  }\n\
         }\n\n\
         fn f(tree: Tree) -> Option[Int64] {\n\
        \  var cursor = tree.each()\n\
        \  mut cursor.next()\n\
         }\n"
        "ownership.not_pullable");
  test "a cursor of a method that can be pulled is pulled" (fun () ->
      fine
        "fn f(items: List[Int64]) -> Option[Int64] {\n\
        \  var cursor = items.each()\n\
        \  mut cursor.next()\n\
         }\n");
  test "a parallel branch cannot change what another uses" (fun () ->
      one_diagnostic
        "fn bump(count: mut Int64) {}\n\n\
         fn f() -> Int64 {\n\
        \  var count = 0\n\
        \  parallel {\n\
        \    bump(mut count)\n\
        \    let seen = count\n\
        \  }\n\
        \  seen\n\
         }\n"
        "ownership.parallel_conflict")

(* Methods *)

let () =
  let bag = "type Bag(items: List[Int64])\n\n" in
  test "an impl method's read-only parameter may be returned as a view" (fun () ->
      fine
        (bag
       ^ "trait Shower {\n\
         \  fn show(self, items: List[Int64]) -> Slice[Int64]\n\
          }\n\n\
          impl Shower for Bag {\n\
         \  fn show(self, items: List[Int64]) -> Slice[Int64] { items[..] }\n\
          }\n"));
  test "an impl method cannot move a read-only parameter" (fun () ->
      one_diagnostic
        (keep ^ bag
       ^ "trait Eater {\n\
         \  fn eat(self, items: List[Int64])\n\
          }\n\n\
          impl Eater for Bag {\n\
         \  fn eat(self, items: List[Int64]) {\n\
         \    keep(own items)\n\
         \  }\n\
          }\n")
        "ownership.not_owned");
  test "an impl method may move a field of an owned self" (fun () ->
      fine
        (bag
       ^ "trait Taker {\n\
         \  fn take(own self) -> List[Int64]\n\
          }\n\n\
          impl Taker for Bag {\n\
         \  fn take(own self) -> List[Int64] { own self.items }\n\
          }\n"));
  test "a trait's method with a body is checked too" (fun () ->
      one_diagnostic
        (keep ^ "trait Eater {\n  fn eat(self, items: List[Int64]) {\n    keep(own items)\n  }\n}\n")
        "ownership.not_owned")

(* Loans held for a stretch of code *)

let () =
  test "a loop's body cannot change what it goes over, even inside a branch" (fun () ->
      one_diagnostic
        "fn f(ready: Bool) {\n\
        \  var items: List[Int64] = [1, 2]\n\
        \  for _ in items {\n\
        \    if ready {\n\
        \      items = []\n\
        \    }\n\
        \  }\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a loop's body cannot lend mut what it goes over" (fun () ->
      one_diagnostic
        "fn f() {\n\
        \  var items: List[Int64] = [1, 2]\n\
        \  for item in items {\n\
        \    mut items.push(item)\n\
        \  }\n\
         }\n"
        "ownership.changed_while_viewed");
  test "a parallel for cannot lend mut a place from outside it" (fun () ->
      one_diagnostic
        "fn f(items: List[Int64]) {\n\
        \  var total: List[Int64] = []\n\
        \  parallel for item in items {\n\
        \    mut total.push(item)\n\
        \  }\n\
         }\n"
        "ownership.parallel_conflict");
  test "a parallel for cannot assign a place from outside it, even inside a branch" (fun () ->
      one_diagnostic
        "fn f(ready: Bool) {\n\
        \  var total = 0\n\
        \  parallel for item in 0..10 {\n\
        \    if ready {\n\
        \      total = item\n\
        \    }\n\
        \  }\n\
         }\n"
        "ownership.parallel_conflict");
  test "a parallel for may change its own element and locals" (fun () ->
      fine
        "fn f(items: mut List[Int64]) {\n\
        \  parallel for item in mut items {\n\
        \    var doubled = item * 2\n\
        \    doubled = doubled + 1\n\
        \    item = doubled\n\
        \  }\n\
         }\n");
  test "a call cannot view a place another of its arguments moves" (fun () ->
      one_diagnostic
        "fn both(first: List[Int64], second: own List[Int64]) {}\n\n\
         fn f(items: own List[Int64]) {\n\
        \  both(items, second: own items)\n\
         }\n"
        "ownership.conflicting_loan");
  test "a Plain place passed own is copied, so the call may use it twice" (fun () ->
      fine
        "fn both(first: Int64, second: own Int64) {}\n\n\
         fn f(count: Int64) {\n\
        \  both(count, second: count)\n\
         }\n")

(* Pulling and lending *)

let () =
  let tree =
    "type Tree =\n  | Leaf\n  | indirect Node(left: Tree, value: Int64, right: Tree)\n\n"
  in
  test "a method that yields through itself inside a branch cannot be pulled" (fun () ->
      one_diagnostic
        (tree
       ^ "fn Tree.odd(self) yields Int64 {\n\
         \  match self {\n\
         \    Leaf => {}\n\
         \    Node(left, ..) => {\n\
         \      for item in left.odd() {\n\
         \        if item > 0 {\n\
         \          yield item\n\
         \        }\n\
         \      }\n\
         \    }\n\
         \  }\n\
          }\n\n\
          fn f(tree: Tree) -> Option[Int64] {\n\
         \  var cursor = tree.odd()\n\
         \  mut cursor.next()\n\
          }\n")
        "ownership.not_pullable");
  test "methods that yield through each other cannot be pulled" (fun () ->
      one_diagnostic
        (tree
       ^ "fn Tree.first(self) yields Int64 {\n\
         \  match self {\n\
         \    Leaf => {}\n\
         \    Node(left, ..) => {\n\
         \      for item in left.second() {\n\
         \        yield item\n\
         \      }\n\
         \    }\n\
         \  }\n\
          }\n\n\
          fn Tree.second(self) yields Int64 {\n\
         \  for item in self.first() {\n\
         \    yield item\n\
         \  }\n\
          }\n\n\
          fn f(tree: Tree) -> Option[Int64] {\n\
         \  var cursor = tree.first()\n\
         \  mut cursor.next()\n\
          }\n")
        "ownership.not_pullable");
  test "a call's result does not view a Plain argument it was given" (fun () ->
      fine
        "fn window(items: List[Int64], start: USize) -> Slice[Int64] {\n\
        \  items[start..]\n\
         }\n\n\
         fn f(items: List[Int64]) -> Slice[Int64] {\n\
        \  let start: USize = 1\n\
        \  window(items, start)\n\
         }\n");
  test "a lending method's path that cannot finish need not yield" (fun () ->
      fine
        "type Grid(cells: List[Int64])\n\n\
         fn Grid.cell(self, ready: Bool) lends Int64 {\n\
        \  if ready {\n\
        \    yield self.cells[0]\n\
        \  } else {\n\
        \    unreachable\n\
        \  }\n\
         }\n")

(* Views of temporaries *)

let () =
  let same = "fn same(prefix: String) yields String {\n  yield prefix.copy()\n}\n\n" in
  test "a cursor cannot view a temporary that the statement drops" (fun () ->
      one_diagnostic
        (same ^ "fn f() -> Option[String] {\n  var each = same(\"a${1}\")\n  mut each.next()\n}\n")
        "ownership.views_temporary");
  test "a cursor may view a named value" (fun () ->
      fine
        (same
       ^ "fn f() -> Option[String] {\n\
         \  let prefix = \"a${1}\"\n\
         \  var each = same(prefix)\n\
         \  mut each.next()\n\
          }\n"));
  test "a cursor may view a string literal, which lives in static memory" (fun () ->
      fine (same ^ "fn f() -> Option[String] {\n  var each = same(\"a\")\n  mut each.next()\n}\n"));
  test "a slice cannot view a temporary list" (fun () ->
      one_diagnostic
        "fn make() -> List[Int64] { [1, 2, 3] }\n\n\
         fn f() -> USize {\n\
        \  let middle = make()[1..2]\n\
        \  middle.length()\n\
         }\n"
        "ownership.views_temporary");
  test "a value computed from a temporary's view is fine" (fun () ->
      fine
        "fn make() -> List[Int64] { [1, 2, 3] }\n\nfn f() -> USize {\n  make()[1..2].length()\n}\n")

(* Pulling views of places *)

let () =
  test "pulling a view of a String element is an error" (fun () ->
      one_diagnostic
        "fn f(names: List[String]) -> Option[String] {\n\
        \  var each = names.each()\n\
        \  mut each.next()\n\
         }\n"
        "ownership.not_pullable");
  test "a for loop over a held cursor of String elements is an error too" (fun () ->
      one_diagnostic
        "fn f(names: List[String]) {\n\
        \  var each = names.each()\n\
        \  for name in mut each {\n\
        \    let _ = name\n\
        \  }\n\
         }\n"
        "ownership.not_pullable");
  test "a method that yields owned values can be pulled whatever its element" (fun () ->
      fine
        "fn greetings() yields String {\n\
        \  yield \"hello\"\n\
        \  yield \"hi\"\n\
         }\n\n\
         fn f() -> Option[String] {\n\
        \  var each = greetings()\n\
        \  mut each.next()\n\
         }\n");
  test "a for loop over a marked call drives the method, not a cursor" (fun () ->
      fine
        "fn f(names: mut List[String]) {\n\
        \  for name in mut names.each() {\n\
        \    let _ = name\n\
        \  }\n\
         }\n");
  test "a recursive mut walk may loop over itself" (fun () ->
      fine
        "type Tree(value: Int64, children: List[Tree])\n\n\
         fn Tree.each(mut self) yields mut Int64 {\n\
        \  yield mut self.value\n\
        \  for child in mut self.children {\n\
        \    for value in mut child.each() {\n\
        \      yield mut value\n\
        \    }\n\
        \  }\n\
         }\n");
  test "looping over a method that yields views of String elements is fine" (fun () ->
      fine
        "fn f(names: List[String]) -> USize {\n\
        \  var count: USize = 0\n\
        \  for name in names {\n\
        \    count = count + name.length()\n\
        \  }\n\
        \  count\n\
         }\n")

let () = finish ()
