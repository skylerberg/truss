(* Truss source compiled with the standard library and run: each feature. *)

open Codegen_support

let () =
  passes
    "a derived ordering compares fields in declaration order, and a construction evaluates its \
     fields in the order written"
    {|type Entry(weight: Int64, label: Int64)
  derives Equal, Ordered

fn next(counter: mut Int64) -> Int64 {
  counter += 1
  counter
}

test "field order" {
  assert Entry(weight: 1, label: 9) < Entry(weight: 2, label: 0)
  assert Entry(label: 9, weight: 1) < Entry(label: 0, weight: 2)
  var counter = 0
  let entry = Entry(label: next(mut counter), weight: next(mut counter))
  assert entry.label == 1
  assert entry.weight == 2
}
|};
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
  passes "a cursor over a method whose receiver has no size keeps its arguments"
    {|type Quiet()

fn Quiet.count(self, limit: Int64) yields Int64 {
  var i = 1
  while i <= limit {
    yield i
    i += 1
  }
}

test "counted" {
  let quiet = Quiet()
  var each = quiet.count(2)
  assert mut each.next() == Some(1)
  assert mut each.next() == Some(2)
  assert mut each.next() == None
}
|};
  (* A cursor that held the evidence it was made with would read the
     [Table]'s list after the first block had dropped it. *)
  passes "a cursor's next uses the implementation provided where it is called"
    {|capability Meter {
  fn read() -> Int64
}

type Table(values: List[Int64])

impl Meter for Table {
  fn read(self) -> Int64 {
    var sum = 0
    for value in self.values {
      sum += value
    }
    sum
  }
}

fn readings(count: Int64) yields Int64
  uses Meter
{
  var index = 0
  while index < count {
    yield Meter.read() + index
    index += 1
  }
}

fn total(count: Int64) -> Int64
  uses Meter
{
  var cursor = readings(count)
  var sum = 0
  while mut cursor.next() is Some(reading) {
    sum += reading
  }
  sum
}

test "a cursor that outlives the block it was made in" {
  var cursor = provide Table(values: [1, 2, 4]) {
    var built = readings(4)
    assert mut built.next() == Some(7)
    own built
  }
  provide Table(values: [100]) {
    assert mut cursor.next() == Some(101)
    assert total(3) == 303
  }
  provide Table(values: [10, 10]) {
    assert mut cursor.next() == Some(22)
    var seen = 0
    for reading in own cursor {
      seen += reading
    }
    assert seen == 23
  }
  provide Table(values: [1]) {
    var inner = readings(3)
    provide Table(values: [2]) {
      assert mut inner.next() == Some(2)
    }
    assert mut inner.next() == Some(2)
  }
}
|};
  test "an associated capability set gives each instance the evidence that its type needs"
    (fun () ->
      expect_output
        {|capability Meter {
  fn read() -> Int64
}

type Table(values: List[Int64])

impl Meter for Table {
  fn read(self) -> Int64 {
    var total = 0
    for value in self.values {
      total += value
    }
    total
  }
}

trait Feed {
  capability Uses

  fn pull(mut self) -> Option[Int64]
    uses Self.Uses

  fn skip(mut self)
    uses Self.Uses
  {
    let _ = mut self.pull()
  }
}

type Counter(next: Int64)

impl Feed for Counter {
  fn pull(mut self) -> Option[Int64] {
    if self.next >= 3 {
      return None
    }
    self.next += 1
    Some(self.next)
  }
}

type Gauge(left: Int64)

impl Feed for Gauge {
  capability Uses = Meter

  fn pull(mut self) -> Option[Int64]
    uses Meter
  {
    if self.left == 0 {
      return None
    }
    self.left -= 1
    Some(Meter.read())
  }
}

type Twice[Source](source: Source)

impl Feed for Twice[Source: Feed] {
  capability Uses = Source.Uses

  fn pull(mut self) -> Option[Int64]
    uses Self.Uses
  {
    let _ = mut self.source.pull()
    mut self.source.pull()
  }
}

fn drain[Source: Feed](source: mut Source) -> Int64
  uses Source.Uses
{
  var total = 0
  while mut source.pull() is Some(value) {
    total += value
  }
  total
}

fn apply[Source: Feed](
  source: mut Source,
  run: (fn(mut Source) -> Option[Int64] uses Source.Uses),
) -> Option[Int64]
  uses Source.Uses
{
  run(mut source)
}

fn through(feed: mut any Feed) -> Option[Int64] {
  mut feed.skip()
  mut feed.pull()
}

fn readings(count: Int64) yields Int64
  uses Meter
{
  var index = 0
  while index < count {
    yield Meter.read() + index
    index += 1
  }
}

fn plain(count: Int64) yields Int64 {
  var index = 0
  while index < count {
    yield index
    index += 1
  }
}

fn doubled[Source: Cursor[Element = Int64]](source: own Source) yields Int64
  uses Source.Uses
{
  var cursor = own source
  while mut cursor.next() is Some(value) {
    yield value * 2
  }
}

fn added[Source: Cursor[Element = Int64]](source: own Source) -> Int64
  uses Source.Uses
{
  var total = 0
  for value in own source {
    total += value
  }
  total
}

fn first[Source: Cursor](source: mut Source) -> Option[Source.Element]
  uses Source.Uses
{
  mut source.next()
}

test "a generic function takes the evidence that its instance's type needs" {
  var counter = Counter(next: 0)
  assert drain(mut counter) == 6
  provide Table(values: [3, 4]) {
    var gauge = Gauge(left: 3)
    assert drain(mut gauge) == 21
  }
}

test "a method that a trait gives a body takes the evidence of its impl's set" {
  var counter = Counter(next: 0)
  mut counter.skip()
  assert mut counter.pull() == Some(2)
  provide Table(values: [5]) {
    var gauge = Gauge(left: 2)
    mut gauge.skip()
    assert mut gauge.pull() == Some(5)
    assert mut gauge.pull() == None
  }
}

test "a set that an impl defines from a parameter's set" {
  var pure = Twice(source: Twice(source: Counter(next: 0)))
  assert drain(mut pure) == 0
  provide Table(values: [7]) {
    var twice = Twice(source: Gauge(left: 5))
    mut twice.skip()
    assert drain(mut twice) == 7
    var nested = Twice(source: Twice(source: Gauge(left: 4)))
    assert drain(mut nested) == 7
  }
}

test "a function value whose type uses a set" {
  var counter = Counter(next: 0)
  assert apply(mut counter, run: fn(feed) { mut feed.pull() }) == Some(1)
  provide Table(values: [9]) {
    var gauge = Gauge(left: 1)
    assert apply(mut gauge, run: fn(feed) { mut feed.pull() }) == Some(9)
  }
}

test "a call through any passes no evidence for a set" {
  var boxed: any Feed = any Counter(next: 0)
  assert through(mut boxed) == Some(2)
  var cursor: any Cursor[Element = Int64] = any plain(3)
  assert mut cursor.next() == Some(0)
  assert own cursor.last() == Some(2)
}

test "the methods of Cursor on a cursor that uses a capability" {
  provide Table(values: [10]) {
    assert readings(3).count() == 3
    assert readings(3).to_list() == [10, 11, 12]
    assert readings(3).last() == Some(12)
    assert readings(3).fold(0, combine: fn(total, value) { total + value }) == 33
    var cursor = readings(4)
    assert mut cursor.find(fn(value) { value > 10 }) == Some(11)
    assert mut cursor.next() == Some(12)
  }
  assert plain(3).count() == 3
}

test "a generic function over a cursor passes the evidence where it calls next" {
  assert added(plain(4)) == 6
  provide Table(values: [1, 1]) {
    assert added(readings(3)) == 9
    var cursor = readings(2)
    assert first(mut cursor) == Some(2)
    provide Table(values: [5]) {
      assert first(mut cursor) == Some(6)
    }
    assert first(mut cursor) == None
  }
}

test "a yielding function that uses its source's set" {
  assert doubled(plain(3)).to_list() == [0, 2, 4]
  assert added(doubled(doubled(plain(3)))) == 12
  provide Table(values: [10]) {
    assert doubled(readings(3)).to_list() == [20, 22, 24]
    assert added(doubled(doubled(readings(2)))) == 84
    var total = 0
    for value in doubled(readings(2)) {
      total += value
    }
    assert total == 42
  }
}
|}
        (String.concat "" (List.init 8 (Printf.sprintf "test %d passed\n"))));
  passes "a lending method resumes after its caller's statement"
    {|type Counted(value: Int64, reads: Int64)

fn Counted.current(mut self) lends Int64 {
  yield self.value
  self.value = 99
}

test "lent" {
  var counted = Counted(value: 1, reads: 0)
  let got = mut counted.current() + 0
  assert got == 1
  assert counted.value == 99
}
|};
  passes "a lending method lends a local it owns, which lives until the caller's statement ends"
    {|type Holder(id: Int64)

fn Holder.label(self) lends String {
  let text = "label ${self.id}"
  yield text
}

test "lent" {
  let holder = Holder(id: 1)
  assert holder.label() == "label 1"
}
|};
  (* The caller continues from either [yield], and only the first has
     [label] in scope. *)
  passes "a lending method owns a value at one of its yields and not at another"
    {|type Pair(first: String, second: String)

fn Pair.chosen(self, pick: Bool) lends String {
  if pick {
    let label = "picked ${self.first}"
    yield self.first
    let _ = label.length()
  } else {
    yield self.second
  }
}

test "lent from either yield" {
  let pair = Pair(first: "one", second: "two")
  assert pair.chosen(true) == "one"
  assert pair.chosen(false) == "two"
  var seen = 0
  for pick in [true, false, true] {
    if pair.chosen(pick).length() == 3 {
      seen += 1
    }
  }
  assert seen == 3
}
|};
  passes "a lending method yields inside a loop over a yielding method that owns a value"
    {|type Bag(items: List[String])

fn Bag.matching(self, prefix: StringSlice) yields String {
  let wanted = prefix.to_string()
  for item in self.items {
    if item.slice().starts_with(wanted.slice()) {
      yield item
    }
  }
}

fn Bag.first_matching(self, prefix: StringSlice) lends Option[String] {
  for item in self.matching(prefix) {
    yield Some(item)
    return
  }
  yield None
}

test "the first match, and none" {
  let bag = Bag(items: ["pear", "fig", "plum"])
  assert bag.first_matching("f") == Some("fig")
  assert bag.first_matching("p") == Some("pear")
  assert bag.first_matching("x") is None
}
|};
  passes "a `lends mut` method yields on two paths, and owns a local at one of them"
    {|type Slots(first: List[Int64], second: Int64)

fn Slots.slot(mut self, pick: Bool) lends mut Int64 {
  if pick {
    let label = "slot ${self.second}"
    yield mut self.first[0]
    let _ = label.length()
  } else {
    yield mut self.second
  }
}

test "changed through either yield" {
  var slots = Slots(first: [1, 2], second: 5)
  mut slots.slot(true) += 10
  mut slots.slot(false) += 100
  assert slots.first[0] == 11
  assert slots.second == 105
}
|};
  passes "a lending method resumes when its caller's statement exits early"
    {|type Counted(value: Int64, finished: Int64)

fn Counted.current(mut self) lends Int64 {
  yield self.value
  self.finished += 1
}

fn read(counted: mut Counted, stop: Bool) -> Int64 {
  let got = mut counted.current() + (if stop { return 0 } else { 1 })
  got
}

test "lent" {
  var counted = Counted(value: 5, finished: 0)
  assert read(mut counted, stop: true) == 0
  assert counted.finished == 1
  assert read(mut counted, stop: false) == 6
  assert counted.finished == 2
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
  var ages: Map[String, Int64] = ["ada": 36, "alan": 41]
  mut ages.insert("ada", value: 37)
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
    {|use standard::console

type Recorded(lines: List[String])

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

  fn print(self, text: StringSlice) {}

  fn input(self) -> console::Input { todo }

  fn output(self) -> console::Output { todo }

  fn error_output(self) -> console::Output { todo }

  fn terminal(self) -> console::Terminal { todo }
}

type Quiet()

impl Console for Quiet {
  fn print_line(self, text: StringSlice) {}
  fn print_error(self, text: StringSlice) {}
  fn read_line(self) -> Option[String] { Some("typed") }

  fn print(self, text: StringSlice) {}

  fn input(self) -> console::Input { todo }

  fn output(self) -> console::Output { todo }

  fn error_output(self) -> console::Output { todo }

  fn terminal(self) -> console::Terminal { todo }
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

  fn print(self, text: StringSlice) {
    Console.print(text)
  }

  fn input(self) -> console::Input {
    Console.input()
  }

  fn output(self) -> console::Output {
    Console.output()
  }

  fn error_output(self) -> console::Output {
    Console.error_output()
  }

  fn terminal(self) -> console::Terminal {
    Console.terminal()
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

let side: Int64 = 7
let area: Int64 = side * side
let corner: Point = Point(x: 2 * 2, y: -3)
let ages: Map[String, Int64] = ["grace": 85, "ada": 36]
let colors: Set[String] = ["red", "green", "red"]
let welcome: String = "hello ada"
let maybe: Option[Int64] = Some(3 * 3)

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
    {|fn describe(present: Option[String], limit: USize) -> String {
  if present is Some(text) && text.length() > limit {
    text.copy()
  } else if !(present is Some(_)) || limit == 0 {
    "nothing"
  } else {
    "short"
  }
}

fn longer(present: Option[String]) -> Bool {
  present is Some(text) && text.length() > 3
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
    {|fn classify(present: Option[String]) -> String {
  match present {
    Some(text) if text.length() > 3 => text.copy()
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

let () =
  passes "a list grows as it is pushed and keeps what it held"
    {|test "grown" {
  var numbers: List[Int64] = []
  var next = 0
  while next < 1000 {
    mut numbers.push(next)
    next += 1
  }
  var total = 0
  for number in numbers {
    total += number
  }
  assert numbers.length() == 1000
  assert total == 499500
}
|};
  passes "text that started as a literal is copied before it is added to"
    {|test "added to" {
  var first = "abc"
  mut first.push("def")
  let second = "abc"
  assert first == "abcdef"
  assert second == "abc"
}
|}

let () =
  test "values echo as Truss writes them" (fun () ->
      expect_output
        {|type Point(x: Float64, y: Float32)

test "echoes" {
  let _ = echo Some(true)
  let _ = echo Some(1.5)
  let _ = echo [1, 2, 3]
  let _ = echo "hi\n \${x} \u{1}"
  let _ = echo Point(x: 0.1, y: 2.0)
  let _ = echo -7
  let _ = echo Character"é"
}
|}
        "test 0 passed\n\
         echo 265\n\
         example/main.truss:4:11: Some(true)\n\
         example/main.truss:5:11: Some(1.5)\n\
         example/main.truss:6:11: [1, 2, 3]\n\
         example/main.truss:7:11: \"hi\\n \\${x} \\u{1}\"\n\
         example/main.truss:8:11: Point(x: 0.1, y: 2.0)\n\
         example/main.truss:9:11: -7\n\
         example/main.truss:10:11: Character\"\195\169\"\n\n")
