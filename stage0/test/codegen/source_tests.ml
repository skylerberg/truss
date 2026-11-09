(* Truss source compiled with the standard library and run: the basics. *)

open Memory_layout
open Codegen_support

let () =
  test "a test calls a function that uses the standard library's arithmetic" (fun () ->
      expect_output
        {|fn square(value: Int64) -> Int64 {
  value * value
}

test "squares" {
  assert square(3) == 9
}

test "squares wrongly" {
  assert square(3) == 10
}
|}
        "test 0 passed\n\
         test 1 failed\n\
         message 51\n\
         assert square(3) == 10\n\
        \  at example/main.truss:10:3\n")

let () =
  passes "loops, variables, and comparisons run"
    {|fn sum_to(limit: Int64) -> Int64 {
  var total = 0
  var i = 1
  while i <= limit {
    total += i
    i += 1
  }
  total
}

test "sums" {
  assert sum_to(10) == 55
}
|};
  passes "a counted for loop runs once per value"
    {|fn sum_below(limit: Int64) -> Int64 {
  var total = 0
  for i in 0..limit {
    total += i
  }
  total
}

test "sums" {
  assert sum_below(5) == 10
}
|};
  passes "records are built and read, and sums matched"
    {|type Point(x: Int64, y: Int64)

type Shape =
  | Circle(radius: Int64)
  | Rectangle(width: Int64, height: Int64)
  | Empty

fn area(shape: Shape) -> Int64 {
  match shape {
    Circle(radius) => 3 * radius * radius
    Rectangle(width, height) => width * height
    Empty => 0
  }
}

test "areas" {
  let origin = Point(x: 1, y: 2)
  assert origin.x + origin.y == 3
  assert area(Shape.Rectangle(width: 2, height: 5)) == 10
  assert area(Shape.Circle(radius: 2)) == 12
  assert area(Shape.Empty) == 0
}
|};
  passes "an if is a value, and a return leaves early"
    {|fn sign(value: Int64) -> Int64 {
  if value < 0 {
    return -1
  }
  if value == 0 { 0 } else { 1 }
}

test "signs" {
  assert sign(-5) == -1
  assert sign(0) == 0
  assert sign(7) == 1
}
|};
  passes "the standard library's Option methods run"
    {|fn first_positive(a: Int64, b: Int64) -> Option[Int64] {
  if a > 0 { Some(a) } else if b > 0 { Some(b) } else { None }
}

test "options" {
  assert first_positive(-1, b: 4) == Some(4)
  assert first_positive(-1, b: -2).is_none()
}
|}

let () =
  passes "lists are built, pushed onto, indexed, and looped over"
    {|fn total(items: List[Int64]) -> Int64 {
  var sum = 0
  for item in items {
    sum += item
  }
  sum
}

test "lists" {
  var items: List[Int64] = [1, 2, 3]
  mut items.push(4)
  assert items.length() == 4
  assert items[0] == 1
  assert items[3] == 4
  assert total(items) == 10
}
|};
  passes "a question mark returns an error early"
    {|type ParseError = Empty | TooLarge
  derives Equal

fn check(value: Int64) -> Result[Int64, ParseError] {
  if value > 100 { Err(ParseError.TooLarge) } else { Ok(value) }
}

fn doubled(value: Int64) -> Result[Int64, ParseError] {
  let checked = check(value)?
  Ok(checked * 2)
}

test "results" {
  assert doubled(4) == Ok(8)
  assert doubled(400) == Err(ParseError.TooLarge)
}
|}

let () =
  passes "a string interpolates its parts"
    {|test "interpolation" {
  let count = 3
  let name = "apples"
  assert "${count} ${name}" == "3 apples"
}
|};
  passes "a record is updated with with"
    {|type Point(x: Int64, y: Int64)
  derives Equal

test "updates" {
  let origin = Point(x: 0, y: 0)
  let moved = origin with (x: 5)
  assert moved == Point(x: 5, y: 0)
}
|};
  passes "a lambda reads its caller's locals"
    {|fn apply(value: Int64, transform: fn(Int64) -> Int64) -> Int64 {
  transform(value)
}

test "lambdas" {
  let offset = 10
  assert apply(5, transform: fn(value) { value + offset }) == 15
}
|}

let () =
  passes "integers display in decimal, negative ones too"
    {|test "display" {
  let small: Int8 = -128
  let large: UInt64 = 18446744073709551615
  let least: Int64 = -9223372036854775808
  assert "${small} ${large} ${least} ${0}" == "-128 18446744073709551615 -9223372036854775808 0"
}
|};
  passes "strings compare, order, and trim"
    {|test "strings" {
  let padded = "  hello \n"
  assert padded.trim().to_string() == "hello"
  assert "apple" < "banana"
  assert "apple" != "apples"
}
|}

let () =
  passes "constants are static data, worked out exactly"
    {|type Point(x: Int64, y: Int64)
  derives Equal

let seconds_per_day: Int64 = 24 * 60 * 60
let origin: Point = Point(x: -1, y: 2)
let greeting: String = "hello"
let primes: List[Int64] = [2, 3, 5, 7]

test "constants" {
  assert seconds_per_day == 86400
  assert origin == Point(x: -1, y: 2)
  assert greeting == "hello"
  assert primes[3] == 7
  assert primes.length() == 4
  assert ExitCode.failure.code == 1
}
|}

let () =
  passes "a named function is passed as a function value"
    {|fn double(value: Int64) -> Int64 {
  value * 2
}

fn apply(value: Int64, transform: fn(Int64) -> Int64) -> Int64 {
  transform(value)
}

test "named functions" {
  assert apply(21, transform: double) == 42
}
|};
  passes "a field left out takes its default"
    {|type Request(path: String, retries: Int64 = 3, secure: Bool = true)

test "defaults" {
  let request = Request(path: "/")
  assert request.retries == 3
  assert request.secure
  let other = Request(path: "/", retries: 5)
  assert other.retries == 5
}
|};
  passes "a parameter left out takes its default"
    {|fn connect(port: Int64 = 443, secure: Bool = true) -> Int64 {
  if secure { port } else { 0 }
}

test "parameter defaults" {
  assert connect() == 443
  assert connect(port: 80) == 80
  assert connect(secure: false) == 0
}
|};
  passes "an any value calls its implementation's method"
    {|trait Shape {
  fn area(self) -> Int64
}

type Square(side: Int64)
type Rectangle(width: Int64, height: Int64)

impl Shape for Square {
  fn area(self) -> Int64 { self.side * self.side }
}

impl Shape for Rectangle {
  fn area(self) -> Int64 { self.width * self.height }
}

fn total(shapes: List[any Shape]) -> Int64 {
  var sum = 0
  for shape in shapes {
    sum += shape.area()
  }
  sum
}

test "any" {
  let shapes: List[any Shape] = [any Square(side: 2), any Rectangle(width: 3, height: 4)]
  assert total(shapes) == 16
}
|}

let () = Harness.finish ()
