(* Lowering from the core form: a program for each kind of node, whose test
   passes when the code lowered from it runs correctly. *)

open Codegen_support

let () =
  passes "calls, operators, comparisons, a let, an if, and a return"
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
  passes "`let x = own y` moves the value, and `let x = y` aliases the place"
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
  passes "a trait method call resolves to the type's impl, or to a bound in a generic function"
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
  passes "an assignment, a call that omits an argument with a default, and a field access"
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
  passes "a string literal, a constant, and a constructor call with every field"
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
  passes "a while loop with break and continue, and a for loop over an integer range"
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
  passes "a for loop over a yielding method's call"
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
  passes "a match on literals, a range, strings, and two values at once"
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
  passes "alternatives that bind a name bind it from the alternative that matched"
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
  passes "a let with an else, an is-test, a guard, and a pattern in a let and in a for loop"
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
  passes "a todo and an unreachable on paths not taken, and a proof block"
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
  passes "an is-test on a call's result keeps the result for the names it binds"
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
  passes "defaults of a plain, a read-only, and an own parameter, and a requires clause"
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
  passes "an index, a lending method with a default, and a yielding method that returns early"
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

let () =
  passes "a capability method call, a provide, and a crash on a path not taken"
    {|capability Tally {
  fn add(amount: Int64)
  fn total() -> Int64
}

type Counter(sum: Int64)

impl Tally for Counter {
  fn add(mut self, amount: Int64) {
    self.sum += amount
  }

  fn total(self) -> Int64 {
    self.sum
  }
}

fn record(amount: Int64) -> Int64
  uses Tally
{
  Tally.add(amount)
  Tally.total()
}

fn counted() -> Int64 {
  var counter = Counter(sum: 1)
  let last = provide mut counter {
    let first = record(2)
    first + record(3)
  }
  last + counter.sum
}

fn checked(value: Int64) -> Int64
  uses Panic
{
  if value < 0 {
    Panic.crash("negative")
  }
  value
}

test "counts" {
  assert counted() == 15
  assert checked(3) == 3
}
|};
  passes "a value converted to an any value, from an impl and from a bound"
    {|trait Named {
  fn name(self) -> String
}

type Square(side: Int64)

impl Named for Square {
  fn name(self) -> String {
    "square"
  }
}

impl Named for Int64 {
  fn name(self) -> String {
    "integer"
  }
}

fn boxed(side: Int64) -> any Named {
  any Square(side: side)
}

fn boxed_from[Value: Named](value: own Value) -> any Named {
  any value
}

test "boxes" {
  let first = boxed(2)
  let second = boxed_from(7)
  assert first.name() == "square"
  assert second.name() == "integer"
}
|}

let () =
  passes "an interpolated string, a tagged string, and a copy"
    {|type Sum(pieces: USize, total: Int64)

impl FromTemplate for Sum {
  type Part = Int64

  fn from_template(template: Template[Int64]) -> Sum {
    var total = 0
    for part in template.parts {
      total += part
    }
    Sum(pieces: template.literals.length(), total: total)
  }
}

fn describe(count: Int64, label: String) -> String {
  "${count} ${label}s, ${count > 1}"
}

fn sum(first: Int64, second: Int64) -> Sum {
  Sum"a ${first} b ${second} c"
}

fn twice(text: String) -> String {
  let again = text.copy()
  "${text}${again}"
}

test "strings" {
  assert describe(2, label: "box") == "2 boxs, true"
  let total = sum(2, second: 40)
  assert total.pieces == 3
  assert total.total == 42
  assert twice("ab") == "abab"
}
|};
  passes "a set, a map, a record update, a field default, and a parallel block"
    {|type Settings(name: String = "default", retries: Int64 = 2 + 1, verbose: Bool = false)

type Shape =
  | Circle(radius: Int64 = 7)
  | Square(side: Int64)

fn colors() -> Set[String] {
  ["red", "green", "red"]
}

fn ages() -> Map[String, Int64] {
  ["ada": 36, "alan": 41]
}

fn renamed(settings: own Settings) -> Settings {
  settings with (name: "renamed", retries: 9)
}

fn defaults() -> Settings {
  Settings(verbose: true)
}

fn circle() -> Shape {
  Shape.Circle()
}

fn both(first: Int64, second: Int64) -> Int64 {
  var left = 0
  var right = 0
  parallel {
    left = first * 2
    right = second * 3
  }
  left + right
}

test "values" {
  assert colors().length() == 2
  assert ages().length() == 2
  let settings = defaults()
  assert settings.name == "default"
  assert settings.retries == 3
  assert settings.verbose
  let changed = renamed(own settings)
  assert changed.name == "renamed"
  assert changed.retries == 9
  assert changed.verbose
  assert circle() is Circle(radius: 7)
  assert both(1, second: 2) == 8
}
|}

let () =
  passes "an array literal and a generic value parameter used as a value"
    {|fn squares() -> Array[Int64, 3] {
  [1, 4, 9]
}

fn capacity[count: USize](items: Array[Int64, count]) -> USize {
  count
}

test "arrays" {
  assert capacity(squares()) == 3
  let four: Array[Int64, 4] = [0, 0, 0, 0]
  assert capacity(four) == 4
}
|}

let () =
  test "a call of a lending method that never yields compiles, and stops where the method does"
    (fun () ->
      expect_output
        {|type Grid(cells: List[Int64])

fn Grid.broken(self) lends Int64
  uses Panic
{
  Panic.crash("no cell")
}

fn read(grid: Grid) -> Int64
  uses Panic
{
  grid.broken() + 1
}

test "reads" {
  let grid = Grid(cells: [1])
  assert read(grid) == 2
}
|}
        "test 0 panicked\nmessage 35\nno cell\n  at example/main.truss:6:3\n")

let () =
  passes "a loop over a recursive yielding function pulls a cursor over it"
    {|fn descend(from: Int64) yields Int64 {
  if from > 0 {
    yield from
    for below in descend(from - 1) {
      yield below
    }
  }
}

fn total(from: Int64) -> Int64 {
  var sum = 0
  for value in descend(from) {
    sum += value
  }
  sum
}

test "descends" {
  assert total(4) == 10
  assert total(0) == 0
}
|};
  passes "a pulled yielding function copies the places it yields"
    {|fn labels(names: List[String], depth: Int64) yields String {
  for name in names {
    yield name
  }
  if depth > 0 {
    for inner in labels(names, depth: depth - 1) {
      yield inner
    }
  }
}

fn longest(names: List[String]) -> USize {
  var most: USize = 0
  for label in labels(names, depth: 2) {
    if label.length() > most && label != "" {
      most = label.length()
    }
  }
  most
}

test "labels" {
  assert longest(["a", "abc", "ab"]) == 3
}
|};
  passes "a named function as a value, at its own type and at a wider one"
    {|fn double(value: Int64) -> Int64 {
  value * 2
}

fn apply(transform: fn(Int64) -> Int64, value: Int64) -> Int64 {
  transform(value)
}

fn doubled(value: Int64) -> Int64 {
  apply(double, value: value)
}

fn named() -> fn(Int64) -> Int64 {
  double
}

test "function values" {
  assert doubled(4) == 8
  assert apply(named(), value: 5) == 10
}
|}

let () =
  passes "a lambda that captures a local and one that captures self, called through a value"
    {|type Scale(factor: Int64)

fn Scale.scaled(self, items: List[Int64]) -> List[Int64] {
  items.map(fn(item) { item * self.factor })
}

fn apply(transform: fn(Int64) -> Int64, value: Int64) -> Int64 {
  transform(value)
}

fn add_all(items: List[Int64], amount: Int64) -> List[Int64] {
  items.map(fn(item) { item + amount })
}

fn longest_over(names: List[String], least: USize) -> USize {
  var most = least
  let lengths = names.map(fn(name) { name.length() })
  for length in lengths {
    if length > most {
      most = length
    }
  }
  most
}

test "lambdas" {
  assert add_all([1, 2, 3], amount: 10) == [11, 12, 13]
  assert Scale(factor: 3).scaled([1, 2]) == [3, 6]
  let offset = 5
  assert apply(fn(value) { value - offset }, value: 12) == 7
  assert longest_over(["a", "abc"], least: 2) == 3
}
|};
  passes "a method called through an any value"
    {|trait Shape {
  fn area(self) -> Int64
  fn name(self) -> String
}

type Square(side: Int64)

type Rectangle(width: Int64, height: Int64)

impl Shape for Square {
  fn area(self) -> Int64 {
    self.side * self.side
  }

  fn name(self) -> String {
    "square ${self.side}"
  }
}

impl Shape for Rectangle {
  fn area(self) -> Int64 {
    self.width * self.height
  }

  fn name(self) -> String {
    "rectangle ${self.width}x${self.height}"
  }
}

fn total(shapes: List[any Shape]) -> Int64 {
  var sum = 0
  for shape in shapes {
    sum += shape.area()
  }
  sum
}

fn names(shapes: List[any Shape]) -> List[String] {
  var found: List[String] = []
  for shape in shapes {
    mut found.push(shape.name())
  }
  found
}

test "shapes" {
  let shapes: List[any Shape] = [any Square(side: 3), any Rectangle(width: 2, height: 5)]
  assert total(shapes) == 19
  assert names(shapes) == ["square 3", "rectangle 2x5"]
}
|};
  passes "next on a cursor and a loop over the rest of it"
    {|fn numbers(limit: Int64) yields Int64 {
  var next = 1
  while next <= limit {
    yield next
    next += 1
  }
}

fn first_and_rest(limit: Int64) -> Int64 {
  var cursor = numbers(limit)
  let first = match mut cursor.next() {
    Some(number) => number
    None => 0
  }
  var rest = 0
  for number in mut cursor {
    rest += number
  }
  first * 100 + rest
}

test "cursors" {
  assert first_and_rest(4) == 109
  assert first_and_rest(0) == 0
}
|}

(* Checks which of a module's constants fold and which are worked out by
   running their evaluators, and that the module's test passes. *)
let folds what ~folded ~run source =
  test what (fun () ->
      let database, _ = load source in
      let context = Lower.context ~checks:true database target_64 in
      let value path =
        match Lower.constant context path with Folded data -> Some data.value | Run _ -> None
      in
      context.constant := value;
      let constant name : Path.t = Top { module_ = example; name } in
      List.iter
        (fun name -> if value (constant name) = None then fail "%s is run, and should fold" name)
        folded;
      List.iter
        (fun name -> if value (constant name) <> None then fail "%s folds, and should be run" name)
        run;
      expect_output source "test 0 passed\n")

let () =
  folds "constants fold from their core forms, except a set, which is built by running"
    ~folded:[ "small"; "flag"; "names"; "rows"; "corner"; "primes" ]
    ~run:[ "colors" ]
    {|type Point(x: Int64, y: Int64)

let small: Int64 = 2 + 3 * 4
let flag: Bool = small > 10 && !false
let names: List[String] = ["a", "bc"]
let rows: List[List[Int64]] = [[1, 2], [3]]
let corner: Point = Point(x: 1, y: small)
let primes: Array[Int64, 3] = [2, 3, 5]
let colors: Set[String] = ["red", "green", "red"]

test "constants" {
  assert small == 14
  assert flag
  assert names.length() == 2 && names[1] == "bc"
  assert rows[0][1] == 2 && rows[1].length() == 1
  assert corner.y == 14
  assert colors.length() == 2
}
|}

let () = Harness.finish ()
