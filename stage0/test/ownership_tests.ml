(* The tests of moves, loans, and views. *)

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
  test "a function cannot return a view of its local nested in a type nested in itself" (fun () ->
      one_diagnostic
        "type Holder[Value](value: Value)\n\n\
         fn f() -> Holder[Holder[Slice[Int64]]] {\n\
        \  let items: List[Int64] = [1, 2, 3]\n\
        \  Holder(Holder(items[0..2]))\n\
         }\n"
        "ownership.returns_local_view");
  test "a function cannot return a view of its local kept as an associated type" (fun () ->
      one_diagnostic
        "trait Shown {\n\
        \  type Part\n\
        \  fn part(self) -> Self.Part\n\
         }\n\n\
         type Numbers(items: List[Int64])\n\n\
         impl Shown for Numbers {\n\
        \  type Part = Slice[Int64]\n\n\
        \  fn part(self) -> Slice[Int64] {\n\
        \    self.items[0..2]\n\
        \  }\n\
         }\n\n\
         type Kept[Source: Shown](part: Source.Part)\n\n\
         fn f() -> Kept[Numbers] {\n\
        \  let numbers = Numbers([1, 2, 3])\n\
        \  Kept(numbers.part())\n\
         }\n"
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

let () =
  test "is on a temporary binds its parts as owned, as match does" (fun () ->
      fine
        "fn make() -> Option[String] { todo }\n\n\
         fn keep(text: own String) {}\n\n\
         fn f() {\n\
        \  if make() is Some(text) {\n\
        \    keep(own text)\n\
        \  }\n\
         }\n");
  test "a let of a marked call's result binds it owned" (fun () ->
      fine
        "fn keep(found: own Option[List[Int64]]) {}\n\n\
         fn f(source: mut List[List[Int64]]) {\n\
        \  let last = mut source.pop()\n\
        \  keep(own last)\n\
         }\n");
  test "is on a place binds views of its parts" (fun () ->
      one_diagnostic
        "fn keep(text: own String) {}\n\n\
         fn f(found: Option[String]) {\n\
        \  if found is Some(text) {\n\
        \    keep(own text)\n\
        \  }\n\
         }\n"
        "ownership.not_owned")

let () =
  let make = "fn make() -> Option[String] { todo }\n\nfn keep(text: own String) {}\n\n" in
  test "a binding inside a loop is a new one each time, so it may be moved" (fun () ->
      fine
        (make
       ^ "fn f(ready: Bool) {\n\
         \  while ready {\n\
         \    let found = make()\n\
         \    keep_found(own found)\n\
         \  }\n\
          }\n\n\
          fn keep_found(found: own Option[String]) {}\n"));
  test "a while loop's is binding may be moved each time round" (fun () ->
      fine (make ^ "fn f() {\n  while make() is Some(text) {\n    keep(own text)\n  }\n}\n"));
  test "an is binding in an if inside a loop may be moved" (fun () ->
      fine
        (make
       ^ "fn f(ready: Bool) {\n\
         \  while ready {\n\
         \    if make() is Some(text) {\n\
         \      keep(own text)\n\
         \    }\n\
         \  }\n\
          }\n"));
  test "a let-else binding inside a loop may be moved" (fun () ->
      fine
        (make
       ^ "fn f(ready: Bool) {\n\
         \  while ready {\n\
         \    let Some(text) = make() else {\n\
         \      return\n\
         \    }\n\
         \    keep(own text)\n\
         \  }\n\
          }\n"))

(* The prover's part *)

(* How many [Disjoint] obligations a definition leaves to the prover. *)
let disjoint_obligations text =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  List.fold_left
    (fun total declaration ->
      match Query.demand database Ownership.ownership (Resolve.Names.key_of declaration) with
      | Some result ->
          total
          + List.length
              (List.filter
                 (function Checked.Disjoint _ -> true | _ -> false)
                 result.Ownership.obligations)
      | None -> total)
    0
    (Query.demand database Resolve.Names.declarations module_)

let () =
  test "two slices of one list lent together are left to the prover" (fun () ->
      let found =
        disjoint_obligations
          "fn both(first: mut Slice[Int64], second: mut Slice[Int64]) {}\n\n\
           fn f(items: mut List[Int64], middle: USize) {\n\
          \  both(mut items[..middle], second: mut items[middle..])\n\
           }\n"
      in
      if found <> 1 then fail "%d obligations" found);
  test "parallel branches that change two elements are left to the prover" (fun () ->
      let found =
        disjoint_obligations
          "fn f(items: mut List[Int64], first: USize, second: USize) {\n\
          \  parallel {\n\
          \    items[first] = 1\n\
          \    items[second] = 2\n\
          \  }\n\
           }\n"
      in
      if found <> 1 then fail "%d obligations" found)

(* Lending: a call of a lending method is a part, lent for the rest of the
   statement, and the place it is lent from is lent whole for as long. *)

let grid =
  "type Cell(name: String)\n\n\
   type Grid(cells: List[Cell])\n\n\
   fn Cell.visit(mut self) {\n\
  \  self.name = \"seen\"\n\
   }\n\n\
   fn Grid.cell(self, index: USize) lends Cell {\n\
  \  yield self.cells[index]\n\
   }\n\n\
   fn Grid.cell(mut self, index: USize) lends mut Cell {\n\
  \  yield mut self.cells[index]\n\
   }\n\n"

let counter =
  "type Counter(count: Int64)\n\n\
   fn Counter.current(self) lends Int64 {\n\
  \  yield self.count\n\
   }\n\n\
   fn Counter.step(mut self) {\n\
  \  self.count = 3\n\
   }\n\n"

let tally =
  "type Tally(cells: List[Int64])\n\n\
   impl Index for Tally {\n\
  \  type Key = USize\n\
  \  type Output = Int64\n\n\
  \  fn at(self, key: USize) lends Int64 {\n\
  \    yield self.cells[key]\n\
  \  }\n\n\
  \  fn at(mut self, key: USize) lends mut Int64 {\n\
  \    yield mut self.cells[key]\n\
  \  }\n\
   }\n\n\
   fn bump(first: mut Int64, second: mut Int64) {\n\
  \  first = 1\n\
  \  second = 2\n\
   }\n\n"

let () =
  test "a part lent `mut` is changed through its `mut self` method, with no mark of its own"
    (fun () -> fine (grid ^ "fn f(grid: mut Grid) {\n  mut grid.cell(0).visit()\n}\n"));
  test "a part lent `mut` is assigned to" (fun () ->
      fine (grid ^ "fn f(grid: mut Grid) {\n  mut grid.cell(0).name = \"new\"\n}\n"));
  test "a part lent read-only is not assigned to" (fun () ->
      one_diagnostic
        (grid ^ "fn f(grid: mut Grid) {\n  grid.cell(0).name = \"new\"\n}\n")
        "types.not_assignable");
  test "a part lent read-only is not passed `mut`" (fun () ->
      one_diagnostic
        (grid
       ^ "fn change(cell: mut Cell) {}\n\nfn f(grid: mut Grid) {\n  change(grid.cell(0))\n}\n")
        "types.wrong_mark");
  test "a part that is lent cannot be given up" (fun () ->
      one_diagnostic
        (grid ^ "fn take(cell: own Cell) {}\n\nfn f(grid: Grid) {\n  take(grid.cell(0))\n}\n")
        "types.missing_mark");
  test "a part that is lent cannot be returned" (fun () ->
      one_diagnostic
        (grid ^ "fn f(grid: Grid) -> Cell {\n  grid.cell(0)\n}\n")
        "ownership.not_owned");
  test "a name cannot keep a part that is lent" (fun () ->
      one_diagnostic
        (grid
       ^ "fn look(cell: Cell) {}\n\n\
          fn f(grid: Grid) {\n\
         \  let kept = grid.cell(0)\n\
         \  look(kept)\n\
          }\n")
        "ownership.keeps_lent_part");
  test "a name copies a `Plain` part that is lent" (fun () ->
      fine (counter ^ "fn f(counter: Counter) -> Int64 {\n  let now = counter.current()\n  now\n}\n"));
  test "matching a part that is lent binds views of it, which cannot be given up" (fun () ->
      one_diagnostic
        (grid
       ^ "fn take(name: own String) {}\n\n\
          fn f(grid: Grid) {\n\
         \  match grid.cell(0) {\n\
         \    (name) => take(own name)\n\
         \  }\n\
          }\n")
        "ownership.not_owned");
  test "a place is lent whole, so two parts of it are not lent `mut` in one statement" (fun () ->
      one_diagnostic
        (grid
       ^ "fn touch(first: mut Cell, second: mut Cell) {}\n\n\
          fn f(grid: mut Grid) {\n\
         \  touch(mut grid.cell(0), second: mut grid.cell(1))\n\
          }\n")
        "ownership.conflicting_loan");
  test "a place and a part it lends `mut` do not go to one call" (fun () ->
      one_diagnostic
        (grid
       ^ "fn both(grid: Grid, cell: mut Cell) {}\n\n\
          fn f(grid: mut Grid) {\n\
         \  both(grid, cell: mut grid.cell(0))\n\
          }\n")
        "ownership.conflicting_loan");
  test "a place lent read-only is not changed in the same statement" (fun () ->
      one_diagnostic
        (tally ^ "fn f(tally: mut Tally) {\n  tally[0] = tally[1]\n}\n")
        "ownership.changed_while_viewed");
  test "two parts of a place are lent read-only in one statement" (fun () ->
      fine (tally ^ "fn f(tally: Tally) -> Int64 {\n  tally[0] + tally[1]\n}\n"));
  test "a lend ends with its statement" (fun () ->
      fine
        (grid
       ^ "fn f(grid: mut Grid) -> USize {\n  mut grid.cell(0).visit()\n  grid.cells.length()\n}\n"));
  test "what a `while` loop's test lends goes back before its body" (fun () ->
      fine
        (counter
       ^ "fn f(counter: mut Counter) {\n\
         \  while counter.current() < 3 {\n\
         \    mut counter.step()\n\
         \  }\n\
          }\n"));
  test "two indexes of a user's collection are not lent `mut` together" (fun () ->
      one_diagnostic
        (tally ^ "fn f(tally: mut Tally) {\n  bump(mut tally[0], second: mut tally[1])\n}\n")
        "ownership.conflicting_loan");
  test "two indexes of a list are lent `mut` together, for the prover to show apart" (fun () ->
      fine
        "fn bump(first: mut Int64, second: mut Int64) {\n\
        \  first = 1\n\
        \  second = 2\n\
         }\n\n\
         fn f(items: mut List[Int64]) {\n\
        \  bump(mut items[0], second: mut items[1])\n\
         }\n")

let () = finish ()
