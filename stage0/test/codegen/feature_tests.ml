(* Truss source compiled with the standard library and run: each feature. *)

open Memory_layout
open Codegen_support

let () =
  passes "a pulled cursor yields each value and then None"
    {|fn count_to(limit: Int64) yields Int64 {
  var i = 1
  while i <= limit {
    yield i
    i += 1
  }
}

test "cursors" {
  var first = count_to(3)
  var second = count_to(2)
  var total = 0
  while mut first.next() is Some(left) && mut second.next() is Some(right) {
    total += left * right
  }
  assert total == 5
  assert mut first.next() == None
  var third = count_to(1)
  assert mut third.next() == Some(1)
  assert mut third.next() == None
}
|};
  passes "a cursor dropped before it ends drops what it holds"
    {|fn words(prefix: own String) yields String {
  yield "${prefix} one"
  yield "${prefix} two"
}

test "dropped early" {
  var each = words("a${1}")
  assert mut each.next() == Some("a1 one")
  let _ = words("b${2}")
}
|};
  passes "sets and maps keep one of each key, in order"
    {|test "collections" {
  var colors: Set[String] = ["red", "green", "red"]
  assert colors.length() == 2
  assert colors.contains("green")
  assert !colors.contains("blue")
  mut colors.insert("blue")
  mut colors.insert("${1}")
  assert colors.length() == 4
  var ages: Map[String, Int64] = ["ada": 36, "alan": 41, "ada": 37]
  assert ages.length() == 2
  assert ages.contains("ada")
  mut ages.insert("grace", value: 85)
  mut ages.insert("alan", value: 42)
  assert ages.length() == 3
  let empty: Map[Int64, Int64] = [:]
  assert empty.length() == 0
}
|};
  passes "strings, constants, and ranges of constants are patterns"
    {|let limit: Int64 = 10
let origin: Int64 = 0

fn command(text: String) -> Int64 {
  match text {
    "quit" => 0
    "help" => 1
    _ => 2
  }
}

fn sized(value: Int64) -> String {
  match value {
    origin => "origin"
    1..limit => "small"
    _ => "large"
  }
}

fn word(text: StringSlice) -> Bool {
  text is "yes" | "y"
}

test "patterns" {
  assert command("quit") == 0
  assert command("help") == 1
  assert command("${1}") == 2
  assert sized(0) == "origin"
  assert sized(5) == "small"
  assert sized(10) == "large"
  assert word("y".slice())
  assert !word("no".slice())
}
|};
  passes "floats display as the shortest decimal that reads back"
    {|test "floats" {
  let half: Float64 = 0.5
  let third: Float32 = 0.25
  let big: Float64 = 1e300
  assert "${half} ${third} ${big} ${2.0}" == "0.5 0.25 1e+300 2.0"
}
|};
  passes "a range is a value with its ends"
    {|fn width(span: Range[Int64]) -> Int64 {
  if span.inclusive { span.stop - span.start + 1 } else { span.stop - span.start }
}

test "ranges" {
  assert width(2..5) == 3
  assert width(2..=5) == 4
  let words = "${1}"..="${2}"
  assert words.start == "1"
}
|};
  passes "a loop that binds an owned value each time frees each one once"
    {|test "pop" {
  var items: List[String] = ["${1}", "${2}"]
  var count = 0
  while mut items.pop() is Some(item) {
    assert item.length() == 1
    count += 1
  }
  assert count == 2
}
|};
  passes "provide runs its body with the implementations given, nested and narrowed"
    {|type Recorded(lines: List[String])

impl Console for Recorded {
  fn print_line(mut self, text: StringSlice) {
    mut self.lines.push(text.to_string())
  }

  fn print_error(mut self, text: StringSlice) {
    mut self.lines.push("error: ${text}")
  }

  fn read_line(self) -> Option[String] {
    None
  }
}

type Quiet()

impl Console for Quiet {
  fn print_line(self, text: StringSlice) {}
  fn print_error(self, text: StringSlice) {}
  fn read_line(self) -> Option[String] { Some("typed") }
}

type Prefixed(prefix: String)

impl Console for Prefixed
  uses Console
{
  fn print_line(self, text: StringSlice) {
    Console.print_line("${self.prefix}${text}".slice())
  }

  fn print_error(self, text: StringSlice) {
    Console.print_error(text)
  }

  fn read_line(self) -> Option[String] {
    Console.read_line()
  }
}

fn greet(name: String) -> USize
  uses Console
{
  Console.print_line("hello ${name}".slice())
  Console.print_error("done".slice())
  name.length()
}

test "provide" {
  var console = Recorded(lines: [])
  let length = provide mut console {
    greet("ada")
  }
  assert length == 3
  assert console.lines == ["hello ada", "error: done"]
  let typed = provide Quiet() {
    Console.read_line()
  }
  assert typed == Some("typed")
  provide mut console {
    provide Prefixed(prefix: "> ") {
      let _ = greet("${1}")
    }
  }
  assert console.lines.length() == 4
  assert console.lines[2] == "> hello 1"
}
|};
  passes "tagged characters are numbers, in values, constants, and patterns"
    {|let newline: UInt8 = UInt8"\n"

fn kind(letter: Character) -> Int64 {
  match letter {
    Character"a"..=Character"z" => 1
    Character"_" => 2
    _ => 0
  }
}

test "characters" {
  assert newline == 10
  assert UInt8"A" == 65
  assert kind(Character"q") == 1
  assert kind(Character"_") == 2
  assert kind(Character"é") == 0
  let accented = Character"é"
  assert "${accented}${true}${Character"z"}" == "étruez"
}
|};
  passes "a tagged string gives its tag a template of its text and parts"
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

test "templates" {
  let small: Int8 = 2
  let large: Int64 = 40
  let sum = Sum"a ${small} b ${large} c"
  assert sum.pieces == 3
  assert sum.total == 42
  let plain = Sum"none"
  assert plain.pieces == 1 && plain.total == 0
}
|};
  passes "a method that yields through recursion drives a for loop"
    {|type Tree =
  | Leaf
  | indirect Node(left: Tree, value: Int64, right: Tree)

fn Tree.walk(self) yields Int64 {
  match self {
    Leaf => {}
    Node(left, value, right) => {
      for item in left.walk() {
        yield item
      }
      yield value
      for item in right.walk() {
        yield item
      }
    }
  }
}

fn countdown(from: Int64) yields String {
  if from > 0 {
    yield "${from}"
    for rest in countdown(from - 1) {
      yield rest
    }
  }
}

test "recursion" {
  let one = Tree.Node(left: Tree.Leaf, value: 1, right: Tree.Leaf)
  let four = Tree.Node(left: Tree.Leaf, value: 4, right: Tree.Leaf)
  let three = Tree.Node(left: Tree.Leaf, value: 3, right: own four)
  let tree = Tree.Node(left: own one, value: 2, right: own three)
  var total = 0
  var order = 0
  for item in tree.walk() {
    order = order * 10 + item
    total += item
  }
  assert total == 10
  assert order == 1234
  var seen = 0
  for item in tree.walk() {
    if item == 3 {
      break
    }
    seen += 1
  }
  assert seen == 2
  var words: USize = 0
  for word in countdown(3) {
    words += word.length()
  }
  assert words == 3
}
|};
  passes "a recursive loop over views of strings gives copies, and leaves the tree whole"
    {|type Tree =
  | Leaf
  | indirect Node(left: Tree, name: String, right: Tree)

fn Tree.names(self) yields String {
  match self {
    Leaf => {}
    Node(left, name, right) => {
      for inner in left.names() {
        yield inner
      }
      yield name
      for inner in right.names() {
        yield inner
      }
    }
  }
}

test "names" {
  let one = Tree.Node(left: Tree.Leaf, name: "${1}", right: Tree.Leaf)
  let three = Tree.Node(left: Tree.Leaf, name: "${3}", right: Tree.Leaf)
  let tree = Tree.Node(left: own one, name: "${2}", right: own three)
  var joined: List[String] = []
  for name in tree.names() {
    mut joined.push(name.copy())
  }
  assert joined == ["1", "2", "3"]
  for name in tree.names() {
    assert name.length() == 1
  }
}
|};
  passes "a constant that needs its code run is worked out while compiling"
    {|type Point(x: Int64, y: Int64)

fn square(value: Int64) -> Int64 {
  value * value
}

fn greeting(name: StringSlice) -> String {
  "hello ${name}"
}

let area: Int64 = square(7)
let corner: Point = Point(x: square(2), y: -3)
let ages: Map[String, Int64] = ["grace": 85, "ada": 36]
let colors: Set[String] = ["red", "green", "red"]
let welcome: String = greeting("ada".slice())
let maybe: Option[Int64] = Some(square(3))

test "constants" {
  assert area == 49
  assert corner.x == 4 && corner.y == -3
  assert ages.length() == 2
  assert ages.contains("ada")
  assert colors.length() == 2
  assert colors.contains("green")
  assert welcome == "hello ada"
  assert maybe == Some(9)
  let copied = welcome.copy()
  assert copied == "hello ada"
}
|};
  passes "a program of many features together: generics, any, lambdas, ?, Map, mut loops"
    {|type ParseError =
  | Empty
  | NotANumber(text: String)
  derives Equal

fn parse_digit(byte: UInt8) -> Option[Int64] {
  if byte >= 48 && byte <= 57 {
    let digit: Int64 = intrinsic_free_convert(byte - 48)
    Some(digit)
  } else {
    None
  }
}

fn intrinsic_free_convert(byte: UInt8) -> Int64 {
  var value = 0
  var left = byte
  while left > 0 {
    value += 1
    left -= 1
  }
  value
}

fn largest[Item: Ordered + Copyable](items: List[Item]) -> Option[Item] {
  var best: Option[Item] = None
  for item in items {
    if best is Some(current) && current >= item {
      continue
    }
    best = Some(item.copy())
  }
  best
}

trait Shape {
  fn area(self) -> Int64
  fn name(self) -> String
}

type Square(side: Int64)
type Rectangle(width: Int64, height: Int64)

impl Shape for Square {
  fn area(self) -> Int64 { self.side * self.side }
  fn name(self) -> String { "square ${self.side}" }
}

impl Shape for Rectangle {
  fn area(self) -> Int64 { self.width * self.height }
  fn name(self) -> String { "rectangle ${self.width}x${self.height}" }
}

fn checked(text: own String) -> Result[String, ParseError] {
  if text.is_empty() {
    return Err(ParseError.Empty)
  }
  Ok(own text)
}

fn twice(text: String) -> Result[USize, ParseError] {
  let value = checked(text.copy())?
  Ok(value.length() * 2)
}

test "everything" {
  assert parse_digit(55) == Some(7)
  assert parse_digit(65) == None
  assert largest([3, 9, 2]) == Some(9)
  assert largest(["b", "c", "a"]) == Some("c")
  let empty: List[Int64] = []
  assert largest(empty) == None
  let shapes: List[any Shape] = [any Square(side: 3), any Rectangle(width: 2, height: 5)]
  var total = 0
  var names: List[String] = []
  for shape in shapes {
    total += shape.area()
    mut names.push(shape.name())
  }
  assert total == 19
  assert names == ["square 3", "rectangle 2x5"]
  let doubled = [1, 2, 3].map(fn(x) { x * 2 })
  assert doubled == [2, 4, 6]
  let labels = [1, 2].map(fn(x) { "#${x}" })
  assert labels == ["#1", "#2"]
  assert twice("abc") == Ok(6)
  assert twice("") == Err(ParseError.Empty)
  var counts: Map[String, Int64] = [:]
  for word in ["a", "b", "a"] {
    mut counts.insert(word.copy(), value: 1)
  }
  assert counts.length() == 2
  var scores: List[Int64] = [1, 2, 3]
  for score in mut scores {
    score *= 10
  }
  assert scores == [10, 20, 30]
}
|};
  passes "a yielding method's defaults are filled when it is pulled or looped over"
    {|fn count(from: Int64, step: Int64 = 1, label: own String = "n") yields String {
  var at = from
  while at < from + 3 * step {
    yield "${label}${at}"
    at += step
  }
}

test "defaults pulled" {
  var plain = count(0)
  assert mut plain.next() == Some("n0")
  assert mut plain.next() == Some("n1")
  var stepped = count(10, step: 5, label: "${1}:")
  assert mut stepped.next() == Some("1:10")
  assert mut stepped.next() == Some("1:15")
  var words: USize = 0
  for word in count(1, step: 2) {
    words += word.length()
  }
  assert words == 6
}
|};
  passes "a read-only parameter's default with something to drop is dropped once"
    {|fn total(items: List[Int64] = [1, 2, 3]) -> Int64 {
  var sum = 0
  for item in items {
    sum += item
  }
  sum
}

fn first(names: List[String] = ["a", "b"]) -> USize {
  names[0].length()
}

test "defaults" {
  assert total() == 6
  assert total([4]) == 4
  assert first() == 1
}
|};
  passes "names an is test binds are used where it holds"
    {|fn describe(found: Option[String], limit: USize) -> String {
  if found is Some(text) && text.length() > limit {
    text
  } else if !(found is Some(_)) || limit == 0 {
    "nothing"
  } else {
    "short"
  }
}

fn longer(found: Option[String]) -> Bool {
  found is Some(text) && text.length() > 3
}

test "is" {
  assert describe(Some("long enough"), limit: 3) == "long enough"
  assert describe(Some("ab"), limit: 3) == "short"
  assert describe(None, limit: 3) == "nothing"
  assert longer(Some("four"))
  assert !longer(Some("abc"))
  assert !longer(None)
}
|};
  passes "a guard that fails leaves the value for the next arm"
    {|fn classify(found: Option[String]) -> String {
  match found {
    Some(text) if text.length() > 3 => text
    Some(text) => "short ${text}"
    None => "none"
  }
}

test "guards" {
  assert classify(Some("lengthy")) == "lengthy"
  assert classify(Some("ab")) == "short ab"
  assert classify(None) == "none"
}
|};
  passes "an expression a pattern looks into is evaluated once"
    {|fn next_index(counter: mut USize) -> USize {
  counter += 1
  counter - 1
}

test "once" {
  var counter: USize = 0
  let items = [Some(10), Some(20), None]
  let Some(first) = items[next_index(mut counter)] else {
    return
  }
  assert first == 10
  assert counter == 1
  if items[next_index(mut counter)] is Some(second) {
    assert second == 20
  }
  assert counter == 2
}
|}

let () = Harness.finish ()
