(* Tests of the core form. Most tests check a program and compare its
   printed core form with the expected text. *)

open Harness
open Support

(* The printed core form of the definition [name] of the program [text]. *)
let printed_definition text name =
  let database = setup [ ("app::main", text) ] in
  let module_ = module_of "app::main" in
  (match
     List.map
       (fun message -> Diagnostic.make ~code:(Types Mismatch) (Source.span 0 0) message)
       (parse_errors database module_)
     @ Resolve.diagnostics database module_
     @ Interface.diagnostics database module_
     @ Infer.diagnostics database module_
   with
  | [] -> ()
  | found -> failwith (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)));
  let found =
    List.find_map
      (fun (declaration : Resolve.Names.declaration) ->
        let key = Resolve.Names.key_of declaration in
        if Path.show key.path = "app::main::" ^ name then Query.demand database Infer.core key
        else None)
      (Query.demand database Resolve.Names.declarations module_)
  in
  match found with
  | Some form -> Core_print.show form
  | None -> failwith (Printf.sprintf "`%s` has no core form" name)

(* The printed body of the function [name]: the last line of its printed
   core form. *)
let printed_body text name =
  match List.rev (String.split_on_char '\n' (printed_definition text name)) with
  | last :: _ -> last
  | [] -> ""

let expect_definition what text expected =
  test what (fun () ->
      let found = printed_definition text "g" in
      if found <> expected then fail "found:\n%s" found)

let expect_body what text expected =
  test what (fun () ->
      let found = printed_body text "g" in
      if found <> expected then fail "found:\n%s" found)

let meters =
  "type Meters(value: Int64)\n\n\
   impl Ordered for Meters {\n\
  \  fn compare(self, other: Meters) -> Ordering { todo }\n\
   }\n\n\
   impl Equal for Meters {\n\
  \  fn equal(self, other: Meters) -> Bool { todo }\n\
   }\n\n"

let shape =
  "type Shape =\n  | Circle(radius: Int64)\n  | Square(side: Int64, label: String = \"s\")\n\n"

(* Operators *)

let () =
  expect_body "an operator and a method call on built-in integers both become an Operator"
    "fn g(left: Int64, right: Int64) -> Int64 {\n  left + right.multiply(2)\n}\n"
    "{ add(left, multiply(right, 2)) }";
  expect_body "a comparison of built-in integers becomes a Compare"
    "fn g(left: Int64, right: Int64) -> Bool {\n  left <= right && left != 0\n}\n"
    "{ ((left <= right) && (left != 0)) }";
  expect_body
    "`<=` on a user type tests the result of `compare`, and `!=` negates a call of `equal`"
    (meters
   ^ "fn g(first: Meters, second: Meters) -> Bool {\n  first <= second || first != second\n}\n")
    "{ (!(Ordered.compare for Meters by app::main::impl Ordered for Meters(place first, place \
     second) is Greater) || !Equal.equal for Meters by app::main::impl Equal for Meters(place \
     first, place second)) }";
  expect_body "a compound assignment evaluates its target once"
    "fn g(items: mut List[Int64]) {\n  items[0] += 2\n}\n"
    "{ compound_assign lent Index.at for List[Int64] by standard::list::impl Index for \
     List[Element](mut place items, 0) lends mut = add(current_target, 2) }";
  expect_definition "arithmetic in a specification converts its operands to Integer"
    "fn g(count: Int64) -> Int64\n  ensures result + 1 > count\n{\n  count\n}\n"
    "fn(count: Int64)\n\
     ensures (add(to_integer(result), to_integer(1)) > to_integer(count))\n\
     { count }"

(* Calls *)

let () =
  expect_body "a call has one argument per parameter, in parameter order"
    "fn connect(host: Int64, port: UInt16 = 443, secure: Bool = true) {}\n\n\
     fn g() {\n\
    \  connect(1, secure: false)\n\
     }\n"
    "{ app::main::connect(1, default, false) }";
  expect_body "a read-only parameter receives a place, and an `own` parameter receives a value"
    "fn keep(items: own List[Int64], limit: Int64) {}\n\n\
     fn g(items: List[Int64], limit: Int64) {\n\
    \  keep(own items, limit)\n\
     }\n"
    "{ app::main::keep(own items, place limit) }";
  expect_body "the first argument of a method call is the receiver"
    "fn g(items: mut List[Int64]) -> USize {\n  mut items.push(4)\n  items.length()\n}\n"
    "{ standard::list::List.push(mut self)[Int64](mut place items, own 4); \
     standard::list::List.length[Int64](place items) }";
  expect_body "a String passed as a StringSlice becomes a call of `slice`"
    "fn greet(text: StringSlice) {}\n\nfn g(name: String) {\n  greet(name)\n}\n"
    "{ app::main::greet(standard::text::String.slice(place name)) }";
  expect_body "a capability method call, and a built-in copy"
    "fn g(count: Int64) -> Int64\n  uses Clock\n{\n  let _ = Clock.now()\n  count.copy()\n}\n"
    "{ let _ = standard::capabilities::Clock.now(); copy(place count) }";
  expect_body "a lambda lists its parameters and its captures"
    "fn g(items: List[Int64], step: Int64) -> List[Int64] {\n\
    \  items.map(fn(item) { item + step })\n\
     }\n"
    "{ Iterable.map for List[Int64] by standard::list::impl Iterable for List[Element](place \
     items, lambda(item) capturing step { add(item, step) }) }"

(* Values *)

let () =
  expect_body "a constructor lists every field, and marks an omitted field as default"
    (shape ^ "fn g() -> Shape {\n  Shape.Square(side: 2)\n}\n")
    "{ Shape.Square(side: 2, label: default) }";
  expect_body "a range expression becomes a Range record" "fn g() -> Range[Int64] {\n  1..5\n}\n"
    "{ Range[Int64](start: 1, stop: 5, inclusive: false) }";
  expect_body "an interpolated string becomes a text builder, a call for each piece, and `finish`"
    "fn g(name: String, count: Int64) -> String {\n  \"${name}: ${count}\"\n}\n"
    "{ { let var own builder = standard::text::TextBuilder.new(); Display.display for String by \
     standard::text::impl Display for String(place name, mut place builder); \
     standard::text::TextBuilder.write(mut self)(mut place builder, \": \"); Display.display for \
     Int64 by standard::numbers::signed::impl Display for Int64(place count, mut place builder); \
     standard::text::TextBuilder.finish(own self)(own builder) } }";
  expect_body "a list literal, a slice, and an index"
    "fn g() -> Int64 {\n  let numbers = [1, 2, 3]\n  let _ = numbers[1..]\n  numbers[0]\n}\n"
    "{ let own numbers = { let var own storage = intrinsic::storage_with_capacity(3); \
     intrinsic::storage_push(mut place storage, own 1); intrinsic::storage_push(mut place storage, \
     own 2); intrinsic::storage_push(mut place storage, own 3); \
     standard::list::List.from_storage[Int64](own storage) }; let _ = slice \
     standard::list::List.slice_range[Int64](place numbers, 1, \
     standard::list::List.length[Int64](place numbers)); lent Index.at for List[Int64] by \
     standard::list::impl Index for List[Element](place numbers, 0) lends }";
  expect_body "a set literal becomes `with_capacity` and one `insert` per element"
    "fn g(first: own String, second: own String) -> Set[String] {\n  [own first, own second]\n}\n"
    "{ { let var own set = standard::set::Set.with_capacity[String](2); \
     standard::set::Set.insert(mut self)[String](mut place set, own first); \
     standard::set::Set.insert(mut self)[String](mut place set, own second); set } }";
  expect_body "a map literal becomes `with_capacity` and one `insert_absent` per entry"
    "fn g() -> Map[Int64, Int64] {\n  [1: 2, 3: 4]\n}\n"
    "{ { let var own map = standard::map::Map.with_capacity[Int64, Int64](2); \
     standard::map::Map.insert_absent(mut self)[Int64, Int64](mut place map, own 1, own 2); \
     standard::map::Map.insert_absent(mut self)[Int64, Int64](mut place map, own 3, own 4); map } \
     }";
  expect_body "an empty set literal is the call of `with_capacity`"
    "fn g() -> Set[Int64] {\n  []\n}\n" "{ standard::set::Set.with_capacity[Int64](0) }";
  expect_body "a slice holds the call of `slice_range`, with an inclusive stop as `stop + 1`"
    "fn g(items: List[Int64], last: USize) -> Slice[Int64] {\n  items[..=last]\n}\n"
    "{ slice standard::list::List.slice_range[Int64](place items, 0, add(last, 1)) }";
  expect_body "a slice of a slice calls the slice's `slice_range`"
    "fn g(items: Slice[Int64]) -> Slice[Int64] {\n  items[1..3]\n}\n"
    "{ slice standard::list::Slice.slice_range[Int64](place items, 1, 3) }";
  expect_body "a record update lists the replaced fields, and expands the shorthand"
    "type Config(port: Int64, host: String)\n\n\
     fn g(config: Config, port: Int64) -> Config {\n\
    \  config with (port)\n\
     }\n"
    "{ config with (port: port) }"

(* Control flow *)

let () =
  expect_body "`?` becomes a match that returns the error"
    "fn parse(text: String) -> Result[Int64, String] { todo }\n\n\
     fn g(text: String) -> Result[Int64, String] {\n\
    \  let value = parse(text)?\n\
    \  Ok(value)\n\
     }\n"
    "{ let own value = match app::main::parse(place text) { Ok(value: own value) => { value } \
     Err(error: own error) => { return Result[Int64, String].Err(error: error) } diverges }; \
     Result[Int64, String].Ok(value: value) }";
  expect_body "a match on a place borrows the place"
    (shape
   ^ "fn g(shape: Shape) -> Int64 {\n\
     \  match shape {\n\
     \    Circle(radius) => radius\n\
     \    Square(side, ..) if side > 2 => side\n\
     \    _ => 0\n\
     \  }\n\
      }\n")
    "{ match place shape { Circle(radius: radius) => { radius } Square(side: side) if (side > 2) \
     => { side } _ => { 0 } } }";
  expect_body "a `match` or `is` on a value binds `own`, even if the receiver of the call is marked"
    "type Queue(items: List[Int64])\n\n\
     fn Queue.take(mut self) -> Option[List[Int64]] {\n\
    \  todo\n\
     }\n\n\
     fn g(queue: mut Queue) -> USize {\n\
    \  if mut queue.take() is Some(first) {\n\
    \    return first.length()\n\
    \  }\n\
    \  match mut queue.take() {\n\
    \    Some(second) => second.length()\n\
    \    None => 0\n\
    \  }\n\
     }\n"
    "{ if (app::main::Queue.take(mut self)(mut place queue) is Some(value: own first)) { return \
     standard::list::List.length[Int64](place first) } diverges; match app::main::Queue.take(mut \
     self)(mut place queue) { Some(value: own second) => { \
     standard::list::List.length[Int64](place second) } None => { 0 } } }";
  expect_body "`is` becomes a Matches, and a block that returns diverges"
    (shape
   ^ "fn g(shape: Shape) -> Int64 {\n  if shape is Circle(radius) { return radius }\n  0\n}\n")
    "{ if (place shape is Circle(radius: radius)) { return radius } diverges; 0 }";
  expect_body
    "a `for` loop over a collection calls `each`, and one over a range is an Integer_range"
    "fn g(items: List[Int64]) -> Int64 {\n\
    \  var total = 0\n\
    \  for item in items {\n\
    \    total += item\n\
    \  }\n\
    \  for step in 0..=total {}\n\
    \  while total < 3 {\n\
    \    total += 1\n\
    \  }\n\
    \  total\n\
     }\n"
    "{ let var own total = 0; for item in yielding_call standard::list::impl Iterable for \
     List[Element].each[Int64](place items) { compound_assign total = add(current_target, item) }; \
     for step in integer_range 0..=total {  }; while (total < 3) { compound_assign total = \
     add(current_target, 1) }; total }"

let () =
  expect_body "a `for` loop over the result of a call calls `each` on the result"
    "fn make() -> List[Int64] {\n\
    \  todo\n\
     }\n\n\
     fn g() {\n\
    \  for item in make() {\n\
    \    let _ = item\n\
    \  }\n\
     }\n"
    "{ for item in yielding_call standard::list::impl Iterable for \
     List[Element].each[Int64](app::main::make()) { let _ = place item } }"

(* Specifications *)

let () =
  expect_definition "a `requires` clause with a quantifier is not executable"
    "fn g(items: List[Int64], limit: Int64) -> Int64\n\
    \  requires limit > 0\n\
    \  requires forall index in 0..items.length() => items[index] < limit\n\
    \  ensures result >= 0\n\
     {\n\
    \  proof {\n\
    \    assert limit > 0\n\
    \  }\n\
    \  limit\n\
     }\n"
    "fn(items: List[Int64], limit: Int64)\n\
     requires (limit > 0)\n\
     requires forall index in 0..standard::list::List.length[Int64](place items) { (lent Index.at \
     for List[Int64] by standard::list::impl Index for List[Element](place items, place index) \
     lends < limit) } (not executable)\n\
     ensures (result >= 0)\n\
     { proof { assert (limit > 0) }; limit }"

(* Other constructs *)

let () =
  expect_body "a tagged string becomes a call of `from_template`"
    "type Shout(text: String)\n\n\
     impl FromTemplate for Shout {\n\
    \  type Part = String\n\n\
    \  fn from_template(template: Template[String]) -> Shout { todo }\n\
     }\n\n\
     fn g(name: own String) -> Shout {\n\
    \  Shout\"hey ${own name}!\"\n\
     }\n"
    "{ template(\"hey \", \"!\") call FromTemplate.from_template for Shout by app::main::impl \
     FromTemplate for Shout(own Template[String](literals: { let var own storage = \
     intrinsic::storage_with_capacity(2); intrinsic::storage_push(mut place storage, own \
     Literal(text: \"hey \")); intrinsic::storage_push(mut place storage, own Literal(text: \
     \"!\")); standard::list::List.from_storage[Literal](own storage) }, parts: { let var own \
     storage = intrinsic::storage_with_capacity(1); intrinsic::storage_push(mut place storage, own \
     name); standard::list::List.from_storage[String](own storage) })) }";
  expect_body "a cursor is advanced by a `for` loop or by a call of `next`"
    "fn count_to(limit: Int64) yields Int64 {\n\
    \  yield limit\n\
     }\n\n\
     fn g() {\n\
    \  var first = count_to(3)\n\
    \  while mut first.next() is Some(left) {\n\
    \    let _ = left\n\
    \  }\n\
    \  for value in count_to(2) {}\n\
    \  for value in first {}\n\
     }\n"
    "{ let var own first = app::main::count_to(3); while (cursor_next(first) is Some(value: own \
     left)) { let _ = place left }; for value in yielding_call app::main::count_to(2) {  }; for \
     value in cursor first {  } }";
  expect_body "a conversion to `any` records the impl, and a method call on `any` is dynamic"
    "trait Source {\n\
    \  type Item\n\
    \  fn first(self) -> Self.Item\n\
     }\n\n\
     type Numbers(items: List[Int64])\n\n\
     impl Source for Numbers {\n\
    \  type Item = Int64\n\n\
    \  fn first(self) -> Int64 {\n\
    \    self.items[0]\n\
    \  }\n\
     }\n\n\
     fn g(numbers: own Numbers) -> Int64 {\n\
    \  let source: any Source[Item = Int64] = any numbers\n\
    \  source.first()\n\
     }\n"
    "{ let own source = any Source[Item = Int64](numbers by app::main::impl Source for Numbers); \
     Source[Item = Int64].first for any Source[Item = Int64] by any(place source) }";
  expect_body "the result of a `lends mut` method is a place that can be assigned"
    "type Cell(state: Int64)\n\n\
     type Grid(cells: List[Cell])\n\n\
     fn Grid.cell(mut self, index: USize) lends mut Cell {\n\
    \  yield mut self.cells[index]\n\
     }\n\n\
     fn g(grid: mut Grid) {\n\
    \  mut grid.cell(0).state = 4\n\
     }\n"
    "{ lent app::main::Grid.cell(mut self)(mut place grid, 0) lends mut.state = 4 }";
  expect_body
    "a `mut self` method called on an indexed element indexes with the `mut self` version of `at`"
    "type Worker(count: Int64)\n\n\
     fn Worker.reset(mut self) {\n\
    \  self.count = 0\n\
     }\n\n\
     fn g(workers: mut List[Worker], index: USize) {\n\
    \  mut workers[index].reset()\n\
     }\n"
    "{ app::main::Worker.reset(mut self)(mut place lent Index.at for List[Worker] by \
     standard::list::impl Index for List[Element](mut place workers, place index) lends mut) }";
  expect_body "a `for` loop over a `mut` element indexes with the `mut self` version of `at`"
    "fn g(rows: mut List[List[Int64]]) {\n  for cell in mut rows[0] {\n    cell = 0\n  }\n}\n"
    "{ for mut cell in yielding_call standard::list::List.each(mut self)[Int64](mut place lent \
     Index.at for List[List[Int64]] by standard::list::impl Index for List[Element](mut place \
     rows, 0) lends mut) { cell = 0 } }";
  test "a `lends mut` method yields a mutable place" (fun () ->
      let found =
        printed_body
          "type Cell(state: Int64)\n\n\
           type Grid(cells: List[Cell])\n\n\
           fn Grid.cell(mut self, index: USize) lends mut Cell {\n\
          \  yield mut self.cells[index]\n\
           }\n"
          "Grid.cell(mut self)"
      in
      if
        found
        <> "{ yield mut place lent Index.at for List[Cell] by standard::list::impl Index for \
            List[Element](mut place self.cells, place index) lends mut }"
      then fail "found:\n%s" found);
  test "a yielded constructor lends the places among its fields" (fun () ->
      let found =
        printed_body
          "type Shelf(books: List[String])\n\n\
           type First(title: String, rest: Slice[String])\n\n\
           fn Shelf.first(self) lends Option[First] {\n\
          \  if self.books.is_empty() {\n\
          \    yield None\n\
          \  } else {\n\
          \    yield Some(First(title: self.books[0], rest: self.books[1..]))\n\
          \  }\n\
           }\n"
          "Shelf.first"
      in
      if
        found
        <> "{ if standard::list::List.is_empty[String](place self.books) { yield \
            Option[First].None() } else { yield Option[First].Some(value: First(title: place lent \
            Index.at for List[String] by standard::list::impl Index for List[Element](place \
            self.books, 0) lends, rest: slice standard::list::List.slice_range[String](place \
            self.books, 1, standard::list::List.length[String](place self.books)))) } }"
      then fail "found:\n%s" found);
  test "a constructor yielded `mut` lends the places that are marked `mut`" (fun () ->
      let found =
        printed_body
          "type Shelf(books: List[String])\n\n\
           type Numbered(index: USize, title: String)\n\n\
           fn Shelf.numbered(mut self) yields mut Numbered {\n\
          \  var index: USize = 0\n\
          \  while index < self.books.length() {\n\
          \    yield Numbered(index: index, title: mut self.books[index])\n\
          \    index = index + 1\n\
          \  }\n\
           }\n"
          "Shelf.numbered(mut self)"
      in
      if
        found
        <> "{ let var own index = 0; while (index < standard::list::List.length[String](place \
            self.books)) { yield mut Numbered(index: index, title: place lent Index.at for \
            List[String] by standard::list::impl Index for List[Element](mut place self.books, \
            place index) lends mut); index = add(index, 1) } }"
      then fail "found:\n%s" found);
  expect_definition "a quantifier over a collection calls `each` in code, and not in a contract"
    "fn g(items: List[Int64]) -> Bool\n\
    \  ensures result == (exists item in items => item < 0)\n\
     {\n\
    \  exists item in items => item < 0\n\
     }\n"
    "fn(items: List[Int64])\n\
     ensures (result == exists item in items { (item < 0) })\n\
     { exists item in yielding_call standard::list::impl Iterable for \
     List[Element].each[Int64](place items) { (item < 0) } }";
  expect_body "a method of `Cursor` on a yielding method's cursor is a call, and `next` is not"
    "fn g(items: List[Int64]) -> USize {\n\
    \  var cursor = items.each()\n\
    \  let _ = mut cursor.next()\n\
    \  items.each().skip(1).count()\n\
     }\n"
    "{ let var own cursor = standard::list::impl Iterable for List[Element].each[Int64](place \
     items); let _ = cursor_next(cursor); Cursor.count for Skip[the cursor of standard::list::impl \
     Iterable for List[Element].each] by standard::cursors::impl Cursor for Skip[Source](own \
     Cursor.skip for the cursor of standard::list::impl Iterable for List[Element].each by derived \
     standard::core::Cursor for standard::list::impl Iterable for List[Element].each(own \
     standard::list::impl Iterable for List[Element].each[Int64](place items), 1)) }";
  expect_body "an early exit from concurrent code names the tasks that it ends"
    "fn fetch(item: Int64) -> Result[Int64, Int64]\n\
    \  uses Clock\n\
     {\n\
    \  Ok(item)\n\
     }\n\n\
     fn g(items: List[Int64]) -> Result[Int64, Int64]\n\
    \  uses Tasks, Clock\n\
     {\n\
    \  for item in items {\n\
    \    concurrent {\n\
    \      let first = fetch(item)?\n\
    \      if item > 3 {\n\
    \        break\n\
    \      }\n\
    \    }\n\
    \    let _ = first\n\
    \  }\n\
    \  concurrent for item in items {\n\
    \    if item > 5 {\n\
    \      break\n\
    \    }\n\
    \    if item > 4 {\n\
    \      continue\n\
    \    }\n\
    \    if item > 3 {\n\
    \      return Err(item)\n\
    \    }\n\
    \  }\n\
    \  Ok(0)\n\
     }\n"
    "{ for item in yielding_call standard::list::impl Iterable for List[Element].each[Int64](place \
     items) { concurrent #48 { let own first = match app::main::fetch(place item) { Ok(value: own \
     value) => { value } Err(error: own error) => { task_exit branch 0 of #48 { return \
     Result[Int64, Int64].Err(error: error) } } diverges }; if (item > 3) { task_exit branch 1 of \
     #48 { break } } diverges }; let _ = place first }; concurrent #93 for item in yielding_call \
     standard::list::impl Iterable for List[Element].each[Int64](place items) { if (item > 5) { \
     task_exit an iteration of #93 { break } } diverges; if (item > 4) { continue } diverges; if \
     (item > 3) { task_exit an iteration of #93 { return Result[Int64, Int64].Err(error: item) } } \
     diverges }; Result[Int64, Int64].Ok(value: 0) }";
  expect_body "an assignment through an index calls `assign` where the type has it"
    "fn g(name: own String) {\n\
    \  var ports: Map[String, Int64] = [\"http\": 80]\n\
    \  var scores: List[Int64] = [1]\n\
    \  ports[own name] = 8080\n\
    \  scores[0] = 5\n\
     }\n"
    "{ let var own ports = { let var own map = standard::map::Map.with_capacity[String, Int64](1); \
     standard::map::Map.insert_absent(mut self)[String, Int64](mut place map, own \"http\", own \
     80); map }; let var own scores = { let var own storage = intrinsic::storage_with_capacity(1); \
     intrinsic::storage_push(mut place storage, own 1); \
     standard::list::List.from_storage[Int64](own storage) }; IndexAssign.assign for Map[String, \
     Int64] by standard::map::impl core::IndexAssign for Map[Key, Value](mut place ports, own \
     name, own 8080); lent Index.at for List[Int64] by standard::list::impl Index for \
     List[Element](mut place scores, 0) lends mut = 5 }";
  expect_body "patterns of constants, ranges, and strings"
    "let limit: Int64 = 10\n\n\
     fn g(count: Int64, name: String) -> Int64 {\n\
    \  let size = match count {\n\
    \    limit => 1\n\
    \    0..5 => 2\n\
    \    7 | 8 => 3\n\
    \    _ => 4\n\
    \  }\n\
    \  match name {\n\
    \    \"yes\" => size\n\
    \    _ => 0\n\
    \  }\n\
     }\n"
    "{ let own size = match place count { app::main::limit => { 1 } 0..5 => { 2 } 7 | 8 => { 3 } _ \
     => { 4 } }; match place name { equal to \"yes\" => { size } _ => { 0 } } }";
  expect_definition "a quantifier over a type, and old"
    "fn g(count: Int64) -> Bool\n\
    \  ensures result == (forall value: Int64 => value + 0 == value)\n\
    \  ensures old(count) == count\n\
     {\n\
    \  true\n\
     }\n"
    "fn(count: Int64)\n\
     ensures (result == forall value: Int64 { (add(to_integer(value), to_integer(0)) == \
     to_integer(value)) })\n\
     ensures (old(count) == count)\n\
     { true }"

let () =
  expect_body "a `mut` parameter receives a slice of a place"
    "fn sort_part(part: mut Slice[Int64]) {}\n\n\
     fn g(items: mut List[Int64]) {\n\
    \  sort_part(mut items[..2])\n\
     }\n"
    "{ app::main::sort_part(mut slice standard::list::List.slice_range[Int64](place items, 0, 2)) }"

(* Holes *)

let () =
  expect_body
    "a use of a local whose type is a hole is a Todo, and a pattern on a hole is a Wildcard"
    "fn g() -> Int64 {\n  let value = todo\n  value\n}\n" "{ let _ = todo; todo } diverges";
  expect_body "an operation on a hole evaluates its operands and ends in a Todo"
    "fn g(count: Int64) -> Int64 {\n  let value = todo\n  value.method(count) + 1\n}\n"
    "{ let _ = todo; { let _ = todo; let _ = place count; let _ = 1; todo } diverges } diverges";
  List.iter
    (fun statement ->
      test (Printf.sprintf "`%s` on a hole has a core form" statement) (fun () ->
          no_diagnostics
            ~check:(fun database module_ ->
              Resolve.diagnostics database module_
              @ Interface.diagnostics database module_
              @ Infer.diagnostics database module_)
            [
              ( "app::main",
                "type Config(port: Int64)\n\n\
                 fn take(count: Int64) -> Int64 {\n\
                \  count\n\
                 }\n\n\
                 fn g(items: List[Int64], config: Config) -> Int64 {\n\
                \  var hole = todo\n\
                \  " ^ statement ^ "\n  config.port\n}\n" );
            ]))
    [
      "let member = hole.field";
      "let called = hole(1, items)";
      "let result = hole.method(items)";
      "let mapped = items.map(fn(item) { item + hole })";
      "let indexed = hole[0]";
      "let sliced = hole[1..]";
      "let sum = hole + 1";
      "let negated = -hole";
      "let same = hole == 1";
      "let less = 1 < hole";
      "let tried = hole?";
      "let updated = hole with (port: 1)";
      "let text = \"${hole} and ${items.length()}\"";
      "let listed = [hole, hole]";
      "let passed = take(hole)";
      "let chosen = if hole is Some(inner) { inner } else { 0 }";
      "let matched = match hole {\n    Some(inner) if inner > 0 => inner\n    _ => 0\n  }";
      "let Some(bound) = hole else { return 0 }";
      "for item in hole {\n    let _ = item\n  }";
      "hole.field = 1";
      "hole += 1";
      "hole = 2";
      "while hole is Some(inner) {\n    let _ = inner\n  }";
      "let shown = echo hole";
      "let field = Config(port: hole)";
    ]

(* Capabilities *)

let () =
  let apply =
    "fn apply[capability Granted](run: (fn() uses Granted))\n\
    \  uses Granted\n\
     {\n\
    \  run()\n\
     }\n\n\
     fn shout()\n\
    \  uses Console\n\
     {\n\
    \  Console.print_line(\"named\")\n\
     }\n\n"
  in
  expect_body "a capability parameter is inferred as the set of capabilities the argument uses"
    (apply ^ "fn g()\n  uses Console\n{\n  apply(fn() { Console.print_line(\"inside\") })\n}\n")
    "{ app::main::apply[{Console}](lambda() { \
     standard::capabilities::Console.print_line(standard::text::String.slice(\"inside\")) }) }";
  expect_body "a named function passed for a capability-generic parameter is a Function_value"
    (apply ^ "fn g()\n  uses Console\n{\n  apply(shout)\n}\n")
    "{ app::main::apply[{Console}](fn app::main::shout) }";
  test "a call's `uses` and a lambda's type contain the inferred set, not the callee's parameter"
    (fun () ->
      let text =
        apply ^ "fn g()\n  uses Console\n{\n  apply(fn() { Console.print_line(\"inside\") })\n}\n"
      in
      let database = setup [ ("app::main", text) ] in
      let found = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::g" then
            match Query.demand database Infer.core key with
            | Some form ->
                Core_walk.definition
                  {
                    Core_walk.ignore_all with
                    expression =
                      (fun (node : Core.expression) ->
                        match node.kind with
                        | Call { callee = Function { path; _ }; uses; _ }
                          when Path.show path = "app::main::apply" ->
                            found := ("needs " ^ Types.show_argument (Capabilities uses)) :: !found
                        | Lambda _ -> found := Types.show node.type_ :: !found
                        | _ -> ());
                  }
                  form.definition
            | None -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main"));
      if List.sort compare !found <> [ "(fn() uses Console)"; "needs {Console}" ] then
        fail "found [%s]" (String.concat "; " !found));
  test "a capability parameter in a result type is inferred separately for each call" (fun () ->
      let text =
        "fn later[capability Granted](run: (fn() uses Granted)) -> (fn() uses Granted) {\n\
        \  run\n\
         }\n\n\
         fn g()\n\
        \  uses Console, Clock\n\
         {\n\
        \  let first = later(fn() { Console.print_line(\"x\") })\n\
        \  let second = later(fn() {\n\
        \    let _ = Clock.now()\n\
        \  })\n\
        \  first()\n\
        \  second()\n\
         }\n"
      in
      let database = setup [ ("app::main", text) ] in
      let found = ref [] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::g" then
            match Query.demand database Infer.core key with
            | Some form ->
                Core_walk.definition
                  {
                    Core_walk.ignore_all with
                    pattern =
                      (fun (node : Core.pattern) ->
                        match node.kind with
                        | Bind { name; _ } ->
                            found := (name ^ ": " ^ Types.show node.type_) :: !found
                        | _ -> ());
                  }
                  form.definition
            | None -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main"));
      if List.sort compare !found <> [ "first: (fn() uses Console)"; "second: (fn() uses Clock)" ]
      then fail "found [%s]" (String.concat "; " !found))

(* Origins *)

let () =
  test "a node's origin gives its source span" (fun () ->
      let text =
        "fn g(items: List[Int64]) -> Int64 {\n\
        \  var total = 0\n\
        \  for item in items {\n\
        \    total += item\n\
        \  }\n\
        \  total\n\
         }\n"
      in
      let database = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( Query.demand database Infer.core key,
              Query.demand database Resolve.Names.spans key,
              Query.demand database Resolve.Names.text key )
          with
          | Some form, Some spans, Some written ->
              let found = ref [] in
              Core_walk.definition
                {
                  Core_walk.ignore_all with
                  statement =
                    (fun (node : Core.statement) ->
                      match node.kind with
                      | Compound_assign _ ->
                          let span = spans.(node.origin) in
                          found := String.sub written span.start (span.stop - span.start) :: !found
                      | _ -> ());
                }
                form.definition;
              if !found <> [ "total += item" ] then fail "found [%s]" (String.concat "; " !found)
          | _ -> fail "no core form")
        (Query.demand database Resolve.Names.declarations (module_of "app::main")))

let () =
  expect_definition "a cost clause names its resource"
    "fn g(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
    \  uses Clock\n\
    \  cost calls(visit) == items.length()\n\
    \  cost calls(Clock.now) <= 1\n\
    \  cost time O(items.length() * time(visit))\n\
     {\n\
     }\n"
    "fn(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
     cost calls(visit) == standard::list::List.length[Int64](place items)\n\
     cost calls(standard::capabilities::Clock.now) <= 1\n\
     cost time O(multiply(to_integer(standard::list::List.length[Int64](place items)), time(visit)))\n\
     {  }"

let () =
  expect_definition "`log` and `power` are specification functions outside a cost bound too"
    "fn g(value: UInt64) -> USize\n\
    \  ensures result <= log(value) + 1\n\
    \  ensures power(2, result) >= 1\n\
     {\n\
    \  todo\n\
     }\n"
    "fn(value: UInt64)\n\
     ensures (to_integer(result) <= add(log(value), 1))\n\
     ensures (power(2, result) >= 1)\n\
     { todo }";
  expect_definition "a function of the file named `power` is called in a specification"
    "fn power(base: Int64, exponent: Int64) -> Int64\n\
    \  cost time finite\n\
     {\n\
    \  base\n\
     }\n\n\
     fn g(value: Int64) -> Int64\n\
    \  ensures result == power(value, exponent: 1)\n\
     {\n\
    \  value\n\
     }\n"
    "fn(value: Int64)\nensures (result == app::main::power(place value, 1))\n{ value }";
  expect_definition "the time of a method of a type parameter's bound names the trait method"
    "fn g[Element: Equal](items: List[Element], item: Element) -> Bool\n\
    \  cost time O(items.length() * time(Element.equal))\n\
     {\n\
    \  todo\n\
     }\n"
    "fn(items: List[Element], item: Element)\n\
     cost time O(multiply(to_integer(standard::list::List.length[Element](place items)), \
     time(Equal.equal for Element by a bound)))\n\
     { todo }";
  test "in a trait, `time(Self.method)` names the trait's own method" (fun () ->
      no_diagnostics
        ~check:(fun database module_ ->
          Resolve.diagnostics database module_
          @ Interface.diagnostics database module_
          @ Infer.diagnostics database module_)
        [
          ( "app::main",
            "trait Sized {\n\
            \  fn size(self) -> USize\n\n\
            \  fn double(self) -> USize\n\
            \    cost time O(time(Self.size))\n\
            \  {\n\
            \    self.size() + self.size()\n\
            \  }\n\
             }\n" );
        ])

let () =
  test "the origin of a cost is its cost clause" (fun () ->
      let text =
        "fn g(items: List[Int64]) -> USize\n  cost time O(items.length())\n{\n  items.length()\n}\n"
      in
      let database = setup [ ("app::main", text) ] in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          match
            ( Query.demand database Infer.core key,
              Query.demand database Resolve.Names.spans key,
              Query.demand database Resolve.Names.text key )
          with
          | ( Some { definition = Function { contract = { costs = [ cost ]; _ }; _ }; _ },
              Some spans,
              Some written ) ->
              let span = spans.(cost.origin) in
              let quoted = String.sub written span.start (span.stop - span.start) in
              if quoted <> "cost time O(items.length())" then fail "found `%s`" quoted
          | _ -> fail "no core form with exactly one cost")
        (Query.demand database Resolve.Names.declarations (module_of "app::main")))

(* The standard library's core forms satisfy the invariants. *)

let () =
  let database = setup [] in
  let forms = ref 0 in
  List.iter
    (fun ((module_ : Path.module_), _) ->
      test
        (Printf.sprintf "%s's core forms satisfy the invariants" (Path.show_module module_))
        (fun () -> forms := !forms + check_module_core_invariants database module_))
    Standard_library.modules;
  test "the standard library has core forms" (fun () ->
      if !forms < 500 then fail "only %d of its definitions have one" !forms)

(* Derived methods *)

let printed_derived text type_name trait name receiver =
  let database = setup [ ("app::main", text) ] in
  let path : Path.t =
    Method
      {
        owner =
          Derived
            {
              type_ = Top { module_ = module_of "app::main"; name = type_name };
              trait = Path.standard [ "core" ] trait;
            };
        name;
        receiver;
      }
  in
  match Query.demand database Infer.derived path with
  | Some form -> Core_print.show form
  | None -> failwith "the derived method has no core form"

let expect_derived what text type_name trait name receiver expected =
  test what (fun () ->
      let found = printed_derived text type_name trait name receiver in
      if found <> expected then fail "found:\n%s" found)

let pair =
  "type Pair[Second](first: Int64, second: Second)\n  derives Equal, Hash, Ordered, Default\n\n"

let light =
  "type Light =\n  | Off\n  | Dim(level: Int64)\n  | On\n  derives Equal, Hash, Ordered\n\n"

let () =
  expect_derived "a record's derived equal compares each field" pair "Pair" "Equal" "equal" Read
    "fn(self: Pair[Second], other: Pair[Second])\n\
     { (Equal.equal for Int64 by standard::numbers::signed::impl Equal for Int64(place self.first, \
     place other.first) && Equal.equal for Second by a bound(place self.second, place \
     other.second)) }";
  expect_derived
    "a sum type's derived equal compares the fields of matching variants, and is false for \
     different variants"
    light "Light" "Equal" "equal" Read
    "fn(self: Light, other: Light)\n\
     { match place self { Off => { (place other is Off) } Dim(level: level) => { match place other \
     { Dim(level: other_level) => { Equal.equal for Int64 by standard::numbers::signed::impl Equal \
     for Int64(place level, place other_level) } _ => { false } } } On => { (place other is On) } \
     } }";
  expect_derived "a derived hash writes the variant's index and then each field" light "Light"
    "Hash" "hash" Read
    "fn(self: Light, mut hasher: Hasher)\n\
     { match place self { Off => { standard::core::Hasher.write(mut self)(mut place hasher, 0) } \
     Dim(level: level) => { standard::core::Hasher.write(mut self)(mut place hasher, 1); Hash.hash \
     for Int64 by standard::numbers::signed::impl Hash for Int64(place level, mut place hasher) } \
     On => { standard::core::Hasher.write(mut self)(mut place hasher, 2) } } }";
  expect_derived
    "a record's derived compare compares the next field only if the previous fields are equal" pair
    "Pair" "Ordered" "compare" Read
    "fn(self: Pair[Second], other: Pair[Second])\n\
     { match Ordered.compare for Int64 by standard::numbers::signed::impl Ordered for Int64(place \
     self.first, place other.first) { Equal => { Ordered.compare for Second by a bound(place \
     self.second, place other.second) } own decided => { decided } } }";
  expect_derived "a sum type's derived compare orders by variant index, then by fields" light
    "Light" "Ordered" "compare" Read
    "fn(self: Light, other: Light)\n\
     { let own theirs = match place other { Off => { 0 } Dim => { 1 } On => { 2 } }; match place \
     self { Off => { match place other { Off => { Ordering.Equal() } _ => { if (0 < theirs) { \
     Ordering.Less() } else { Ordering.Greater() } } } } Dim(level: level) => { match place other \
     { Dim(level: other_level) => { Ordered.compare for Int64 by standard::numbers::signed::impl \
     Ordered for Int64(place level, place other_level) } _ => { if (1 < theirs) { Ordering.Less() \
     } else { Ordering.Greater() } } } } On => { match place other { On => { Ordering.Equal() } _ \
     => { if (2 < theirs) { Ordering.Less() } else { Ordering.Greater() } } } } } }";
  expect_derived "a derived default calls `default` for each field" pair "Pair" "Default" "default"
    Static
    "fn()\n\
     { Pair[Second](first: Default.default for Int64 by standard::numbers::signed::impl Default \
     for Int64(), second: Default.default for Second by a bound()) }";
  test "a `todo` type has no derived core form" (fun () ->
      let database = setup [ ("app::main", "type Later = todo\n  derives Equal\n") ] in
      let path : Path.t =
        Method
          {
            owner =
              Derived
                {
                  type_ = Top { module_ = module_of "app::main"; name = "Later" };
                  trait = Well_known.path Equal;
                };
            name = "equal";
            receiver = Read;
          }
      in
      if Query.demand database Infer.derived path <> None then fail "it has a core form");
  test "every method of a derived impl in the standard library has a core form" (fun () ->
      let database = setup [] in
      let derived =
        List.filter_map
          (fun (_, (impl : Path.t)) -> match impl with Derived _ -> Some impl | _ -> None)
          (Query.demand database Interface.Impls.index Path.standard_package)
      in
      if derived = [] then fail "the standard library derives nothing";
      List.iter
        (fun impl ->
          match Interface.Impls.impl_interface database impl with
          | None -> fail "`%s` has no interface" (Path.show impl)
          | Some interface ->
              let provided =
                match
                  Query.demand database Interface.Environment.trait_interface
                    interface.implements.trait
                with
                | Some trait ->
                    List.filter_map
                      (fun (method_ : Types.trait_method) ->
                        if method_.provided then Some method_.method_name else None)
                      trait.methods
                | None -> []
              in
              List.iter
                (fun (name, receiver, _) ->
                  match
                    Query.demand database Infer.derived (Method { owner = impl; name; receiver })
                  with
                  | Some _ -> ()
                  | None ->
                      if not (List.mem name provided) then
                        fail "`%s` has no core form for `%s`" (Path.show impl) name
                  | exception Compiler_bug.Bug bug ->
                      fail "`%s`, `%s`: %s" (Path.show impl) name (Compiler_bug.to_string bug))
                interface.impl_methods)
        derived)

(* [Infer.core_of_path] *)

let () =
  let text =
    "trait Described {\n\
    \  fn describe(self) -> Int64\n\n\
    \  fn twice(self) -> Int64 {\n\
    \    self.describe() + self.describe()\n\
    \  }\n\
     }\n\n\
     type Both[Value](first: Value, second: Value)\n\
    \  derives Equal\n\n\
     impl Described for Both[Value: Described] {\n\
    \  fn describe(self) -> Int64 {\n\
    \    self.first.describe()\n\
    \  }\n\
     }\n"
  in
  let both : Path.t = Top { module_ = module_of "app::main"; name = "Both" } in
  let described : Types.trait_reference =
    {
      trait = Top { module_ = module_of "app::main"; name = "Described" };
      trait_arguments = [];
      associated = [];
    }
  in
  let core_of_method name =
    let database = setup [ ("app::main", text) ] in
    let parameter : Types.parameter = { owner = both; name = "Value" } in
    let bounds (found : Types.parameter) = if found = parameter then [ described ] else [] in
    let owner =
      match
        Interface.Impls.implements database ~bounds
          (Types.named both [ Types.Parameter parameter ])
          described
      with
      | Some (From_impl { impl; _ }) -> impl
      | _ -> failwith "no impl"
    in
    match Query.demand database Infer.core_of_path (Method { owner; name; receiver = Read }) with
    | Some (form, substitution) ->
        ( List.hd (List.rev (String.split_on_char '\n' (Core_print.show form))),
          List.map
            (fun ((parameter : Types.parameter), argument) ->
              parameter.name ^ " = " ^ Types.show_argument argument)
            substitution )
    | None -> failwith "no core form"
  in
  test "a method defined in an impl has its own core form" (fun () ->
      match core_of_method "describe" with
      | "{ Described.describe for Value by a bound(place self.first) }", [] -> ()
      | found, _ -> fail "found %s" found);
  test
    "a method inherited from a trait has the default method's core form and a substitution for Self"
    (fun () ->
      match core_of_method "twice" with
      | ( "{ add(Described.describe for Self by a bound(place self), Described.describe for Self \
           by a bound(place self)) }",
          [ "Self = Both[Value]" ] ) ->
          ()
      | found, substitution -> fail "found %s with [%s]" found (String.concat "; " substitution));
  test "a method of a derived impl has the generated core form" (fun () ->
      let database = setup [ ("app::main", text) ] in
      let owner : Path.t = Derived { type_ = both; trait = Well_known.path Equal } in
      match
        ( Query.demand database Infer.core_of_path
            (Method { owner; name = "equal"; receiver = Read }),
          Query.demand database Infer.core_of_path
            (Method { owner; name = "not_equal"; receiver = Read }) )
      with
      | Some (_, []), Some (_, [ _ ]) -> ()
      | _ ->
          fail "expected the derived method with no substitution and the inherited method with one")

(* A law's proof *)

let pair_ordering =
  "type Pair(first: UInt8, second: UInt8)\n\
  \  derives Equal\n\n\
   theorem only_equal(first: Pair, second: Pair)\n\
  \  ensures (first.compare(second) == Ordering.Equal) == (first == second)\n\
   {\n\
   }\n\n\
   impl Ordered for Pair {\n\
  \  fn compare(self, other: Pair) -> Ordering {\n\
  \    let order = self.first.compare(other.first)\n\
  \    if order != Ordering.Equal { order } else { self.second.compare(other.second) }\n\
  \  }\n\
   }\n\n"

let () =
  test "a law's proof has the law's parameters, with the proof's type for Self" (fun () ->
      let found =
        printed_definition
          (pair_ordering
         ^ "proof Ordered.agrees_with_equal for Pair {\n  only_equal(first, second: second)\n}\n")
          "proof Ordered.agrees_with_equal for Pair"
      in
      let expected =
        "proof(first: Pair, second: Pair) { app::main::only_equal(place synthetic#0, place \
         synthetic#1) }"
      in
      if found <> expected then fail "found:\n%s" found)

(* [Infer.specification] *)

let () =
  let specification text name =
    let database = setup [ ("app::main", text) ] in
    let found =
      List.find_map
        (fun (declaration : Resolve.Names.declaration) ->
          let key = Resolve.Names.key_of declaration in
          if Path.show key.path = "app::main::" ^ name then
            Option.map
              (fun form -> (database, key, form))
              (Query.demand database Infer.specification key)
          else None)
        (Query.demand database Resolve.Names.declarations (module_of "app::main"))
    in
    match found with
    | Some found -> found
    | None -> failwith (Printf.sprintf "`%s` has no specification" name)
  in
  let equal first second name =
    let _, _, first = specification first name and _, _, second = specification second name in
    first = second
  in
  let bump body =
    "fn bump(counter: mut Int64, by: Int64)\n  requires by > 0\n  cost time O(1)\n{\n  " ^ body
    ^ "\n}\n"
  in
  let double body = "fn double(value: Int64) -> Int64\n  cost time O(1)\n{\n  " ^ body ^ "\n}\n" in
  test "editing the body of a function that mutates an argument leaves its specification equal"
    (fun () ->
      if not (equal (bump "counter += by") (bump "counter = counter + by + 0") "bump") then
        fail "the specification changed");
  test "editing the body of a function without a time clause leaves its specification equal"
    (fun () ->
      let slow body = "fn slow(value: Int64) -> Int64 {\n  " ^ body ^ "\n}\n" in
      if not (equal (slow "value") (slow "let same = value\n  same") "slow") then
        fail "the specification changed");
  test "editing a clause changes the specification" (fun () ->
      if
        equal (bump "counter += by")
          "fn bump(counter: mut Int64, by: Int64)\n\
          \  requires by > 1\n\
          \  cost time O(1)\n\
           {\n\
          \  counter += by\n\
           }\n"
          "bump"
      then fail "the specification did not change");
  test "editing the body of a function in the logic changes its specification" (fun () ->
      if equal (double "value + value") (double "value * 2") "double" then
        fail "the specification did not change");
  test "a specification without its body meets the core form's invariants" (fun () ->
      let database, key, form = specification (bump "counter += by") "bump" in
      (match form.definition with
      | Function { body = None; _ } -> ()
      | _ -> fail "the body is in the specification");
      check_core_invariants database key form);
  test "the specification that other packages read has the body of a transparent function only"
    (fun () ->
      let exported modifier =
        let database =
          setup
            [
              ( "app::main",
                Printf.sprintf
                  "public%s fn double(value: Int64) -> Int64\n\
                  \  cost time O(1)\n\
                   {\n\
                  \  value + value\n\
                   }\n"
                  modifier );
            ]
        in
        List.find_map
          (fun (declaration : Resolve.Names.declaration) ->
            Query.demand database Infer.exported_specification (Resolve.Names.key_of declaration))
          (Query.demand database Resolve.Names.declarations (module_of "app::main"))
      in
      (match exported " transparent" with
      | Some { definition = Function { body = Some _; _ }; _ } -> ()
      | _ -> fail "the body of a transparent function is not in the exported specification");
      match exported "" with
      | Some { definition = Function { body = None; _ }; _ } -> ()
      | _ -> fail "the body of a function that is not transparent is in the exported specification");
  test "a theorem's specification has no body" (fun () ->
      let _, _, form =
        specification "theorem doubled(value: Int64)\n  ensures value + value == 2 * value\n{\n}\n"
          "doubled"
      in
      match form.definition with
      | Function { body = None; _ } -> ()
      | _ -> fail "the body is in the specification");
  test "the body that a trait provides for a method is in the method's specification" (fun () ->
      let database =
        setup
          [
            ( "app::main",
              "trait Counted {\n\
              \  fn count(self) -> Int64\n\
              \  fn bump(mut self) -> Int64 {\n\
              \    self.count() + 1\n\
              \  }\n\
               }\n" );
          ]
      in
      let found =
        List.find_map
          (fun (declaration : Resolve.Names.declaration) ->
            match declaration.path with
            | Method { name = "bump"; _ } ->
                Query.demand database Infer.specification (Resolve.Names.key_of declaration)
            | _ -> None)
          (Query.demand database Resolve.Names.declarations (module_of "app::main"))
      in
      match found with
      | Some { definition = Function { body = Some _; _ }; _ } -> ()
      | _ -> fail "the provided body is not in the specification")

let () = finish ()
