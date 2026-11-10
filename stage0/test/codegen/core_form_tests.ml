(* Lowering from the core form: which bodies are lowered from it, and that
   the code lowered from it runs correctly. *)

open Codegen_support

let int64 = Monomorphic.builtin Int64

(* Checks that the module's test passes and that each named function, with
   the given type arguments, is lowered from its core form. With [tests],
   the tests' bodies must be lowered from their core forms too. *)
let lowers what ?(tests = false) functions source =
  test what (fun () ->
      let database, _ = load source in
      let context = Lower.context ~checks:true database target_64 in
      let from_core key =
        match Lower.core_fallback_reason context key with
        | None -> ()
        | Some reason ->
            fail "%s was lowered from the syntax tree because of %s" (Instance.to_string key) reason
      in
      List.iter
        (fun (name, type_arguments) ->
          from_core (Code { path = Top { module_ = example; name }; type_arguments }))
        functions;
      if tests then List.iter (fun path -> from_core (Lower.test_key path)) (tests_of database);
      expect_output source "test 0 passed\n")

let () =
  lowers "calls, operators, comparisons, a let, an if, and a return" ~tests:true
    [ ("double", []); ("larger", []); ("pick", []) ]
    {|fn double(value: Int64) -> Int64 {
  value + value
}

fn larger(first: Int64, second: Int64) -> Int64 {
  if first > second { first } else { second }
}

fn pick(first: Int64, second: Int64) -> Int64 {
  let most = larger(first, second: second)
  if most > 10 && first != second {
    return most * 2
  }
  most + double(second)
}

test "picks" {
  assert pick(3, second: 4) == 12
  assert pick(20, second: 4) == 40
  assert !(pick(1, second: 1) > 3) || pick(1, second: 1) == 3
}
|};
  lowers "`let x = own y` moves the value, and `let x = y` aliases the place"
    [ ("keep", []); ("count", []) ]
    {|fn keep(items: own List[Int64]) -> List[Int64] {
  let held = own items
  held
}

fn count(items: List[Int64]) -> USize {
  let seen = items
  seen.length()
}

test "moves" {
  let kept = keep([1, 2, 3])
  assert count(kept) == 3
}
|};
  lowers "a trait method call resolves to the type's impl, or to a bound in a generic function"
    [ ("same", [ Ground.Type int64 ]); ("equal_lengths", []) ]
    {|type Meters(value: Int64)
  derives Equal

fn same[Value: Equal](first: Value, second: Value) -> Bool {
  first.equal(second)
}

fn equal_lengths(first: Meters, second: Meters) -> Bool {
  first.equal(second)
}

test "equal" {
  assert same(4, second: 4)
  assert equal_lengths(Meters(value: 2), second: Meters(value: 2))
}
|};
  lowers "an assignment, a call that omits an argument with a default, and a field access"
    [ ("twice", []); ("width", []) ]
    {|type Box(width: Int64, height: Int64)

fn step(start: Int64, by: Int64 = 1) -> Int64 {
  start + by
}

fn twice(start: Int64) -> Int64 {
  var total = step(start)
  total = step(total, by: 5)
  total
}

fn width(box: Box) -> Int64 {
  box.width
}

test "steps" {
  assert twice(1) == 7
  assert width(Box(width: 3, height: 4)) == 3
}
|}

let () =
  lowers "a string literal, a constant, and a constructor call with every field" ~tests:true
    [ ("labelled", []) ]
    {|type Box(width: Int64, label: String)

let wide: Int64 = 40

fn labelled(width: Int64) -> Box {
  Box(width: width + wide, label: "box")
}

test "builds" {
  let box = labelled(2)
  assert box.width == 42
  assert box.label == "box"
}
|}

let () =
  lowers "a while loop with break and continue, and a for loop over an integer range" ~tests:true
    [ ("sum_of_odds_below", []); ("triangle", []) ]
    {|fn sum_of_odds_below(limit: Int64) -> Int64 {
  var total = 0
  var next = 0
  while true {
    next += 1
    if next >= limit {
      break
    }
    if next % 2 == 0 {
      continue
    }
    total = total + next
  }
  total
}

fn triangle(rows: Int64) -> Int64 {
  var total = 0
  for row in 1..=rows {
    total = total + row
  }
  total
}

test "loops" {
  assert sum_of_odds_below(8) == 16
  assert triangle(4) == 10
}
|};
  lowers "a for loop over a yielding method's call"
    [ ("total", []) ]
    {|fn total(items: List[Int64]) -> Int64 {
  var sum = 0
  for item in items {
    sum = sum + item
  }
  sum
}

test "sums" {
  assert total([1, 2, 3]) == 6
}
|}

let () =
  lowers "a match on literals, a range, strings, and two values at once" ~tests:true
    [ ("kind", []); ("greeting", []); ("both", []) ]
    {|fn kind(value: Int64) -> String {
  match value {
    0 => "zero"
    1 | 2 | 3 => "small"
    4..10 => "medium"
    _ => "large"
  }
}

fn greeting(word: String) -> Int64 {
  match word {
    "hello" => 1
    "bye" => 2
    _ => 0
  }
}

fn both(first: Option[Int64], second: Option[Int64]) -> Int64 {
  match first, second {
    Some(a), Some(b) => a + b
    Some(a), None => a
    None, Some(b) => b
    None, None => 0
  }
}

test "matches" {
  assert kind(0) == "zero"
  assert kind(2) == "small"
  assert kind(7) == "medium"
  assert kind(10) == "large"
  assert greeting("hello") == 1
  assert greeting("bye") == 2
  assert greeting("what") == 0
  assert both(Some(1), second: Some(2)) == 3
  assert both(Some(1), second: None) == 1
  assert both(None, second: Some(2)) == 2
  assert both(None, second: None) == 0
}
|};
  lowers "alternatives that bind a name bind it from the alternative that matched" ~tests:true
    [ ("size", []); ("text_length", []); ("take_text", []) ]
    {|type Shape =
  | Circle(radius: Int64)
  | Square(extra: Int64, side: Int64)
  | Labelled(label: String, inner: Int64)
  | Named(count: Int64, name: String)
  | Point

fn size(shape: Shape) -> Int64 {
  match shape {
    Circle(radius: n) | Square(side: n, ..) => n
    Labelled(inner: n, ..) | Named(count: n, ..) if n > 100 => 100
    Labelled(inner: n, ..) | Named(count: n, ..) => n
    Point => 0
  }
}

fn text_length(shape: Shape) -> USize {
  match shape {
    Labelled(label: text, ..) | Named(name: text, ..) => text.length()
    _ => 0
  }
}

fn take_text(shape: own Shape) -> String {
  match shape {
    Labelled(label: text, ..) | Named(name: text, ..) => text
    _ => "none"
  }
}

test "alternatives" {
  assert size(Shape.Circle(radius: 3)) == 3
  assert size(Shape.Square(extra: 9, side: 4)) == 4
  assert size(Shape.Labelled(label: "a", inner: 5)) == 5
  assert size(Shape.Named(count: 500, name: "b")) == 100
  assert size(Shape.Named(count: 6, name: "b")) == 6
  assert size(Shape.Point) == 0
  assert text_length(Shape.Labelled(label: "round", inner: 3)) == 5
  assert text_length(Shape.Named(count: 4, name: "box")) == 3
  assert text_length(Shape.Point) == 0
  assert take_text(Shape.Named(count: 4, name: "box")) == "box"
  assert take_text(Shape.Labelled(label: "round", inner: 3)) == "round"
  assert take_text(Shape.Point) == "none"
}
|};
  lowers "a let with an else, an is-test, a guard, and a pattern in a let and in a for loop"
    [ ("first_or", []); ("positive", []); ("sign", []); ("area", []); ("total_area", []) ]
    {|type Box(width: Int64, height: Int64)

fn first_or(value: Option[Int64], fallback: Int64) -> Int64 {
  let Some(found) = value else {
    return fallback
  }
  found
}

fn positive(value: Option[Int64]) -> Bool {
  if value is Some(found) && found > 0 {
    return true
  }
  false
}

fn sign(value: Option[Int64]) -> Int64 {
  match value {
    Some(found) if found < 0 => -1
    Some(found) if found > 0 => 1
    _ => 0
  }
}

fn area(box: Box) -> Int64 {
  let (width: across, height: up) = box
  across * up
}

fn total_area(boxes: List[Box]) -> Int64 {
  var total = 0
  for (width: across, height: up) in boxes {
    total += across * up
  }
  total
}

test "binds" {
  assert first_or(Some(4), fallback: 1) == 4
  assert first_or(None, fallback: 1) == 1
  assert positive(Some(3))
  assert !positive(Some(-3))
  assert !positive(None)
  assert sign(Some(-8)) == -1
  assert sign(Some(8)) == 1
  assert sign(Some(0)) == 0
  assert sign(None) == 0
  assert area(Box(width: 3, height: 4)) == 12
  assert total_area([Box(width: 1, height: 2), Box(width: 3, height: 4)]) == 14
}
|}

let () =
  lowers "a todo and an unreachable on paths not taken, and a proof block" ~tests:true
    [ ("checked", []) ]
    {|fn checked(value: Int64) -> Int64 {
  if value < 0 {
    todo
  }
  if value > 1000 {
    unreachable
  }
  proof {
    assert value >= 0
  }
  value
}

test "checks" {
  assert checked(4) == 4
}
|}

let () =
  lowers "an is-test on a call's result keeps the result for the names it binds" ~tests:true
    [ ("total_length", []); ("first_length", []) ]
    {|fn label(count: Int64) -> Option[String] {
  if count > 0 {
    return Some("label ${count}")
  }
  None
}

fn total_length(count: Int64) -> USize {
  var total: USize = 0
  var left = count
  while label(left) is Some(text) {
    if text != "label 0" {
      total += text.length()
    }
    left -= 1
  }
  total
}

fn first_length(count: Int64) -> USize {
  if label(count) is Some(text) && text == "label 12" {
    return text.length()
  }
  0
}

test "keeps" {
  assert total_length(3) == 21
  assert first_length(12) == 8
  assert first_length(0) == 0
}
|}

let () =
  lowers "defaults of a plain, a read-only, and an own parameter, and a requires clause" ~tests:true
    [ ("step", []); ("length", []); ("keep", []) ]
    {|fn step(start: Int64, by: Int64 = 2 * 3) -> Int64
  requires by > 0
{
  start + by
}

fn length(prefix: String = "item") -> USize {
  prefix.length()
}

fn keep(text: own String = "kept") -> String {
  text
}

test "defaults" {
  assert step(1) == 7
  assert step(1, by: 1) == 2
  assert length() == 4
  assert length("ab") == 2
  assert keep() == "kept"
  assert keep("mine") == "mine"
}
|};
  test "a requires clause lowered from the core form panics when it does not hold" (fun () ->
      expect_output
        {|fn step(start: Int64, by: Int64 = 1) -> Int64
  requires by > 0
{
  start + by
}

test "breaks" {
  let _ = step(1, by: 0)
}
|}
        "test 0 panicked\n\
         message 65\n\
         requirement not met: requires by > 0\n\
        \  at example/main.truss:2:12\n")

let () =
  lowers "an index, a lending method with a default, and a yielding method that returns early"
    ~tests:true
    [ ("second", []); ("corner", []); ("even_total", []); ("raise_corner", []) ]
    {|type Grid(cells: List[Int64], width: USize)

fn Grid.cell(self, row: USize, column: USize = 0) lends Int64
  requires row * self.width + column < self.cells.length()
{
  yield self.cells[row * self.width + column]
}

fn Grid.cell(mut self, row: USize, column: USize = 0) lends mut Int64
  requires row * self.width + column < self.cells.length()
{
  yield mut self.cells[row * self.width + column]
}

fn Grid.evens(self, limit: Int64 = 100) yields Int64 {
  for cell in self.cells {
    if cell > limit {
      return
    }
    if cell % 2 == 0 {
      yield cell
    }
  }
}

fn second(items: List[Int64]) -> Int64 {
  items[1]
}

fn corner(grid: Grid) -> Int64 {
  grid.cell(1, column: 1) + grid.cell(1)
}

fn raise_corner(grid: mut Grid) {
  mut grid.cell(1, column: 1) += 10
}

fn even_total(grid: Grid) -> Int64 {
  var total = 0
  for cell in grid.evens(limit: 10) {
    total += cell
  }
  total
}

test "lends and yields" {
  var grid = Grid(cells: [1, 2, 3, 4, 12, 6], width: 2)
  assert second([5, 6, 7]) == 6
  assert corner(grid) == 7
  assert even_total(grid) == 6
  raise_corner(mut grid)
  assert corner(grid) == 17
}
|}

let () = Harness.finish ()
