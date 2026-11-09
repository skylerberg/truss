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

let () = finish ()
