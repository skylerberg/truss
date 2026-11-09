(* The prover, against the pinned solver. Each test gives a few small
   definitions and states which obligation is proven or is not. See
   PROVER.md, "Testing". *)

open Harness

let solver =
  match Solver.find () with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

let check database module_ =
  match Type_checker.diagnostics database module_ with
  | [] -> Prover.diagnostics database solver module_
  | errors -> errors

let proven text = Support.no_diagnostics ~check [ ("app::main", text) ]
let not_proven text code = Support.one_diagnostic ~check text code

(* The message of a file's one diagnostic. *)
let message text =
  let database = Support.setup [ ("app::main", text) ] in
  match check database (Support.module_of "app::main") with
  | [ diagnostic ] -> diagnostic.message
  | found ->
      Printf.sprintf "%d diagnostics: %s" (List.length found)
        (String.concat "; " (Support.codes found))

let contains text fragment =
  let length = String.length fragment in
  let rec at i =
    i + length <= String.length text && (String.sub text i length = fragment || at (i + 1))
  in
  at 0

(* Operations that could fail *)

let () =
  test "an addition that can overflow" (fun () ->
      not_proven "fn f(count: UInt8) -> UInt8 {\n  count + 1\n}\n" "prover.overflow");
  test "an overflow's counterexample names the value" (fun () ->
      let found = message "fn f(count: UInt8) -> UInt8 {\n  count + 1\n}\n" in
      if not (contains found "`count` is 255") then fail "message %S" found);
  test "a requires rules out the overflow" (fun () ->
      proven "fn f(count: UInt8) -> UInt8\n  requires count < 255\n{\n  count + 1\n}\n");
  test "a check in an if rules out the overflow" (fun () ->
      proven "fn f(count: UInt8) -> UInt8 {\n  if count < 255 { count + 1 } else { count }\n}\n");
  test "a division by a value that may be zero" (fun () ->
      not_proven "fn f(value: UInt32, divisor: UInt32) -> UInt32 {\n  value / divisor\n}\n"
        "prover.division");
  test "a signed division by -1 can overflow" (fun () ->
      not_proven
        "fn f(value: Int64, divisor: Int64) -> Int64\n\
        \  requires divisor != 0\n\
         {\n\
        \  value / divisor\n\
         }\n"
        "prover.overflow");
  test "a shift amount must be less than the width" (fun () ->
      not_proven "fn f(value: UInt32, amount: UInt32) -> UInt32 {\n  value << amount\n}\n"
        "prover.shift");
  test "negating the least signed value overflows" (fun () ->
      not_proven "fn f(value: Int8) -> Int8 {\n  -value\n}\n" "prover.overflow");
  test "an unreachable that can be reached" (fun () ->
      not_proven "fn f(flag: Bool) -> Int64 {\n  if flag { 1 } else { unreachable }\n}\n"
        "prover.unreachable");
  test "an unreachable after a check" (fun () ->
      proven
        "fn f(value: Int64) -> Int64\n\
        \  requires value > 0\n\
         {\n\
        \  if value > 0 { 1 } else { unreachable }\n\
         }\n")

(* Contracts *)

let () =
  test "a call must meet its callee's requires" (fun () ->
      not_proven
        "fn g(count: UInt8) -> UInt8\n\
        \  requires count < 10\n\
         {\n\
        \  count\n\
         }\n\n\
         fn f() -> UInt8 {\n\
        \  g(10)\n\
         }\n"
        "prover.requires");
  test "a call that meets its callee's requires" (fun () ->
      proven
        "fn g(count: UInt8) -> UInt8\n\
        \  requires count < 10\n\
         {\n\
        \  count\n\
         }\n\n\
         fn f() -> UInt8 {\n\
        \  g(9)\n\
         }\n");
  test "an ensures is shown" (fun () ->
      proven
        "fn absolute(value: Int64) -> Int64\n\
        \  requires value > -1000\n\
        \  ensures result >= 0\n\
         {\n\
        \  if value < 0 { -value } else { value }\n\
         }\n");
  test "an ensures that does not hold" (fun () ->
      not_proven "fn f(value: Int64) -> Int64\n  ensures result > value\n{\n  value\n}\n"
        "prover.ensures");
  test "an ensures holds at an early return" (fun () ->
      not_proven
        "fn f(value: Int64) -> Int64\n\
        \  ensures result >= 0\n\
         {\n\
        \  if value < 0 { return value }\n\
        \  value\n\
         }\n"
        "prover.ensures");
  test "a callee's ensures is a fact after the call" (fun () ->
      proven
        "fn bump(count: mut Int64)\n\
        \  requires count < 100\n\
        \  ensures count == old(count) + 1\n\
         {\n\
        \  count += 1\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result == 5\n\
         {\n\
        \  var value: Int64 = 3\n\
        \  bump(mut value)\n\
        \  bump(mut value)\n\
        \  value\n\
         }\n");
  test "a mut argument changes only through the callee's ensures" (fun () ->
      not_proven
        "fn touch(count: mut Int64) {\n\
        \  count = 0\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result == 3\n\
         {\n\
        \  var value: Int64 = 3\n\
        \  touch(mut value)\n\
        \  value\n\
         }\n"
        "prover.ensures")

(* Loops and recursion *)

let () =
  test "a loop with an invariant" (fun () ->
      proven
        "fn f(count: UInt32) -> UInt64\n\
        \  requires count <= 1000\n\
         {\n\
        \  var total: UInt64 = 0\n\
        \  var i: UInt32 = 0\n\
        \  while i < count\n\
        \    invariant i <= count\n\
        \    invariant total <= 1000 * i\n\
        \  {\n\
        \    total += 1000\n\
        \    i += 1\n\
        \  }\n\
        \  total\n\
         }\n");
  test "a loop invariant that an iteration breaks" (fun () ->
      not_proven
        "fn f(count: UInt32) {\n\
        \  var i: UInt32 = 0\n\
        \  while i < count\n\
        \    invariant i < 5\n\
        \  {\n\
        \    i += 1\n\
        \  }\n\
         }\n"
        "prover.invariant");
  test "a loop in a function with a time clause must end" (fun () ->
      not_proven
        "fn f(count: UInt32)\n\
        \  cost time finite\n\
         {\n\
        \  var i: UInt32 = 0\n\
        \  while i < count {\n\
        \    i = i\n\
        \  }\n\
         }\n"
        "prover.termination");
  test "a loop that counts up to its bound ends" (fun () ->
      proven
        "fn f(count: UInt32)\n\
        \  cost time finite\n\
         {\n\
        \  var i: UInt32 = 0\n\
        \  while i < count {\n\
        \    i += 1\n\
        \  }\n\
         }\n");
  test "a for loop over a range knows its index is in range" (fun () ->
      proven "fn f(count: UInt32) {\n  for i in 0..count {\n    let _ = i + 1\n  }\n}\n");
  test "recursion that decreases" (fun () ->
      proven
        "fn f(steps: UInt32) -> UInt32\n\
        \  decreases steps\n\
        \  cost time finite\n\
         {\n\
        \  if steps == 0 { return 0 }\n\
        \  f(steps - 1)\n\
         }\n");
  test "recursion that does not decrease" (fun () ->
      not_proven
        "fn f(steps: UInt32) -> UInt32\n  decreases steps\n  cost time finite\n{\n  f(steps)\n}\n"
        "prover.termination")

let () =
  test "mutual recursion without measures cannot be shown to end" (fun () ->
      let database =
        Support.setup
          [
            ( "app::main",
              "fn even(n: UInt32) -> Bool\n\
              \  cost time finite\n\
               {\n\
              \  if n == 0 { true } else { odd(n - 1) }\n\
               }\n\n\
               fn odd(n: UInt32) -> Bool\n\
              \  cost time finite\n\
               {\n\
              \  if n == 0 { false } else { even(n - 1) }\n\
               }\n" );
          ]
      in
      match Support.codes (check database (Support.module_of "app::main")) with
      | [ "prover.termination"; "prover.termination" ] -> ()
      | codes -> fail "codes %s" (String.concat ", " codes));
  test "mutual recursion that decreases" (fun () ->
      proven
        "fn even(n: UInt32) -> Bool\n\
        \  decreases n\n\
        \  cost time finite\n\
         {\n\
        \  if n == 0 { true } else { odd(n - 1) }\n\
         }\n\n\
         fn odd(n: UInt32) -> Bool\n\
        \  decreases n\n\
        \  cost time finite\n\
         {\n\
        \  if n == 0 { false } else { even(n - 1) }\n\
         }\n");
  test "a function with a time clause cannot call one without" (fun () ->
      not_proven
        "fn forever() -> Int64 {\n\
        \  forever()\n\
         }\n\n\
         fn f() -> Int64\n\
        \  cost time finite\n\
         {\n\
        \  forever()\n\
         }\n"
        "prover.termination");
  test "an impl that reaches itself through a generic function cannot be shown to end" (fun () ->
      not_proven
        "trait Check {\n\
        \  fn check(self) -> Bool\n\
        \    cost time finite\n\
         }\n\n\
         fn run[Item: Check](item: Item) -> Bool\n\
        \  cost time finite\n\
         {\n\
        \  item.check()\n\
         }\n\n\
         type Loop()\n\n\
         impl Check for Loop {\n\
        \  fn check(self) -> Bool\n\
        \    cost time finite\n\
        \  {\n\
        \    !run(self)\n\
        \  }\n\
         }\n"
        "prover.termination")

let tree = "type Tree =\n  | Leaf\n  | indirect Node(left: Tree, value: Int64, right: Tree)\n\n"

let () =
  test "recursion on a part of a parameter ends" (fun () ->
      proven
        (tree
       ^ "fn leftmost(tree: Tree) -> Int64\n\
         \  cost time finite\n\
          {\n\
         \  match tree {\n\
         \    Leaf => 0\n\
         \    Node(left, value, ..) => if left is Leaf { value } else { leftmost(left) }\n\
         \  }\n\
          }\n"));
  test "recursion on the parameter itself does not end" (fun () ->
      not_proven
        (tree ^ "fn spin(tree: Tree) -> Int64\n  cost time finite\n{\n  spin(tree)\n}\n")
        "prover.termination");
  test "a match with guards ends in an unreachable that is proven" (fun () ->
      proven
        "fn f(value: Int64) -> Int64 {\n\
        \  match value {\n\
        \    x if x > 0 => 1\n\
        \    x if x <= 0 => 2\n\
        \    _ => unreachable\n\
        \  }\n\
         }\n")

(* Proofs *)

let () =
  test "a theorem the solver proves alone" (fun () ->
      proven
        "theorem squares_grow(value: Int64)\n\
        \  requires value >= 0\n\
        \  requires value < 1000\n\
        \  ensures value * value >= value\n\
         {\n\
         }\n");
  test "a quantifier over a range" (fun () ->
      not_proven "theorem wrong()\n  ensures forall i in 0..=10 => i < 10\n{\n}\n" "prover.ensures");
  test "an assert in a test is a fact, not an obligation" (fun () ->
      proven "test \"a\" {\n  let x: Int64 = 5\n  assert x == 6\n}\n");
  test "an assert in a theorem is an obligation" (fun () ->
      not_proven "theorem t(value: Int64)\n  ensures true\n{\n  assert value > 0\n}\n"
        "prover.assertion")

(* Data *)

let shape = "type Shape =\n  | Circle(radius: Int64)\n  | Square(side: Int64)\n  | Empty\n\n"
let point = "type Point(x: Int64, y: Int64)\n  derives Equal\n\n"

let () =
  test "match binds a variant's fields" (fun () ->
      proven
        (shape
       ^ "fn f(shape: Shape) -> Int64\n\
         \  ensures result >= 0\n\
          {\n\
         \  match shape {\n\
         \    Circle(radius) => if radius < 0 { 0 } else { radius }\n\
         \    Square(side) => if side < 0 { 0 } else { side }\n\
         \    Empty => 0\n\
         \  }\n\
          }\n"));
  test "a variant's field is in its type's range, and no further" (fun () ->
      not_proven
        (shape
       ^ "fn f(shape: Shape) -> Int64 {\n\
         \  match shape {\n\
         \    Circle(radius) => radius * radius\n\
         \    _ => 0\n\
         \  }\n\
          }\n")
        "prover.overflow");
  test "a counterexample shows a variant by its name" (fun () ->
      let found =
        message
          (shape
         ^ "fn f(shape: Shape) -> Int64 {\n\
           \  match shape {\n\
           \    Circle(radius) => radius + 1\n\
           \    _ => 0\n\
           \  }\n\
            }\n")
      in
      if not (contains found "`shape` is Circle(radius: 9223372036854775807)") then
        fail "message %S" found);
  test "a requires can match on a parameter" (fun () ->
      proven
        (shape
       ^ "fn f(shape: Shape) -> Int64\n\
         \  requires match shape {\n\
         \    Circle(radius) => radius < 100\n\
         \    _ => true\n\
         \  }\n\
          {\n\
         \  match shape {\n\
         \    Circle(radius) => radius + 1\n\
         \    _ => 0\n\
         \  }\n\
          }\n"));
  test "with replaces one field and keeps the others" (fun () ->
      proven
        (point
       ^ "fn f(point: Point) -> Point\n\
         \  requires point.x < 100\n\
         \  ensures result.x == point.x + 1\n\
         \  ensures result.y == point.y\n\
          {\n\
         \  point with (x: point.x + 1)\n\
          }\n"));
  test "derived equality is the solver's equality" (fun () ->
      proven
        (point
       ^ "fn f(point: Point) -> Bool\n\
         \  ensures result\n\
          {\n\
         \  Point(x: point.x, y: point.y) == point\n\
          }\n"));
  test "is binds the parts it matches, where it is true" (fun () ->
      proven
        "fn f(value: Option[Int64]) -> Int64\n\
        \  ensures result >= 0\n\
         {\n\
        \  if value is Some(inner) && inner > 0 { inner } else { 0 }\n\
         }\n");
  test "? goes on with what is inside" (fun () ->
      not_proven
        "fn f(value: Option[UInt8]) -> Option[UInt8] {\n\
        \  let inner = value?\n\
        \  Some(inner + 1)\n\
         }\n"
        "prover.overflow");
  test "? returns an error unchanged" (fun () ->
      proven
        "fn f(value: Result[Int64, Bool]) -> Result[Int64, Bool]\n\
        \  ensures match value {\n\
        \    Err(error) => result == Err(error)\n\
        \    Ok(_) => true\n\
        \  }\n\
         {\n\
        \  let inner = value?\n\
        \  Ok(inner)\n\
         }\n")

(* Collections, definitions, and impls *)

let () =
  test "an index must be in bounds" (fun () ->
      not_proven "fn f(items: List[Int64], index: USize) -> Int64 {\n  items[index]\n}\n"
        "prover.requires");
  test "an index the requires bounds" (fun () ->
      proven
        "fn f(items: List[Int64], index: USize) -> Int64\n\
        \  requires index < items.length()\n\
         {\n\
        \  items[index]\n\
         }\n");
  test "an index a range loop bounds" (fun () ->
      proven
        "fn f(items: List[Int64]) -> Int64 {\n\
        \  var total: Int64 = 0\n\
        \  for i in 0..items.length() {\n\
        \    total = total.saturating_add(items[i])\n\
        \  }\n\
        \  total\n\
         }\n");
  test "assigning to an element checks its index" (fun () ->
      not_proven "fn f(items: mut List[Int64]) {\n  items[0] = 5\n}\n" "prover.requires");
  test "a functional body is its function's definition" (fun () ->
      proven
        "fn is_small(value: Int64) -> Bool\n\
        \  cost time finite\n\
         {\n\
        \  value < 10\n\
         }\n\n\
         fn f() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  is_small(3)\n\
         }\n");
  test "a body with a loop is not a definition" (fun () ->
      not_proven
        "fn is_small(value: Int64) -> Bool\n\
        \  cost time finite\n\
         {\n\
        \  var small = value < 10\n\
        \  small\n\
         }\n\n\
         fn f() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  is_small(3)\n\
         }\n"
        "prover.ensures");
  test "a function without a time clause is not a definition" (fun () ->
      not_proven
        "fn is_small(value: Int64) -> Bool {\n\
        \  value < 10\n\
         }\n\n\
         fn f() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  is_small(3)\n\
         }\n"
        "prover.ensures");
  test "an impl method's contract is read at a call" (fun () ->
      proven
        "type Counter(count: Int64)\n\n\
         trait Next {\n\
        \  fn next(self) -> Int64\n\
         }\n\n\
         impl Next for Counter {\n\
        \  fn next(self) -> Int64\n\
        \    ensures result == self.count\n\
        \  {\n\
        \    self.count\n\
        \  }\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result == 5\n\
         {\n\
        \  Counter(count: 5).next()\n\
         }\n");
  test "a mut argument that is part of a value leaves its value unknown" (fun () ->
      not_proven
        "type Point(x: Int64, y: Int64)\n\n\
         fn bump(value: mut Int64)\n\
        \  requires value < 100\n\
        \  ensures value == old(value) + 1\n\
         {\n\
        \  value += 1\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result == 2\n\
         {\n\
        \  var point = Point(x: 1, y: 2)\n\
        \  bump(mut point.x)\n\
        \  point.y\n\
         }\n"
        "prover.ensures");
  test "assigning a field keeps the other fields" (fun () ->
      proven
        "type Point(x: Int64, y: Int64)\n\n\
         fn f() -> Int64\n\
        \  ensures result == 2\n\
         {\n\
        \  var point = Point(x: 1, y: 2)\n\
        \  point.x = 7\n\
        \  point.y\n\
         }\n")

let measured =
  "type Box(size: Int64)\n\n\
   trait Measured {\n\
  \  fn measure(self) -> Int64\n\
  \    requires true\n\
  \    ensures result >= 0\n\
   }\n\n"

let () =
  test "an impl's method must keep its trait's ensures" (fun () ->
      not_proven
        (measured
       ^ "impl Measured for Box {\n  fn measure(self) -> Int64 {\n    self.size\n  }\n}\n")
        "prover.ensures");
  test "an impl's method that keeps its trait's ensures" (fun () ->
      proven
        (measured
       ^ "impl Measured for Box {\n\
         \  fn measure(self) -> Int64 {\n\
         \    if self.size < 0 { 0 } else { self.size }\n\
         \  }\n\
          }\n"));
  test "an impl's requires may not be stronger than its trait's" (fun () ->
      not_proven
        (measured
       ^ "impl Measured for Box {\n\
         \  fn measure(self) -> Int64\n\
         \    requires self.size >= 0\n\
         \  {\n\
         \    self.size\n\
         \  }\n\
          }\n")
        "prover.requires")

(* Lambdas and callbacks *)

let each_index =
  "fn each_index(count: USize, visit: (fn(index: USize) -> Int64 requires index < count)) -> Int64 {\n\
  \  todo\n\
   }\n\n"

let () =
  test "a lambda's body is proven where it is written" (fun () ->
      not_proven
        "fn apply(transform: fn(UInt8) -> UInt8) -> UInt8 {\n\
        \  todo\n\
         }\n\n\
         fn f() -> UInt8 {\n\
        \  apply(fn(value) { value + 1 })\n\
         }\n"
        "prover.overflow");
  test "a lambda may rely on what its callee promises to pass it" (fun () ->
      proven
        (each_index
       ^ "fn f(items: List[Int64]) -> Int64 {\n\
         \  each_index(items.length(), visit: fn(i) { items[i] })\n\
          }\n"));
  test "a lambda without such a promise knows nothing of its arguments" (fun () ->
      not_proven
        "fn each(count: USize, visit: fn(USize) -> Int64) -> Int64 {\n\
        \  todo\n\
         }\n\n\
         fn f(items: List[Int64]) -> Int64 {\n\
        \  each(items.length(), visit: fn(i) { items[i] })\n\
         }\n"
        "prover.requires");
  test "a function must meet what it promises its callback" (fun () ->
      not_proven
        "fn each_index(count: USize, visit: (fn(index: USize) -> Int64 requires index < count)) -> \
         Int64 {\n\
        \  visit(count)\n\
         }\n"
        "prover.requires");
  test "a function that meets what it promises its callback" (fun () ->
      proven
        "fn each_index(count: USize, visit: (fn(index: USize) -> Int64 requires index < count)) -> \
         Int64 {\n\
        \  if count > 0 { visit(count - 1) } else { 0 }\n\
         }\n")

(* Type invariants *)

let span = "type Span(low: Int64, high: Int64)\n  invariant low <= high\n\n"

let () =
  test "building a value must meet its invariant" (fun () ->
      not_proven (span ^ "fn f(low: Int64) -> Span {\n  Span(low, high: 0)\n}\n") "prover.invariant");
  test "building a value that meets its invariant" (fun () ->
      proven (span ^ "fn f(low: Int64) -> Span\n  requires low <= 0\n{\n  Span(low, high: 0)\n}\n"));
  test "a parameter meets its invariant" (fun () ->
      proven (span ^ "fn f(range: Span)\n  ensures range.low <= range.high\n{\n}\n"));
  test "a mut parameter must meet its invariant when the function returns" (fun () ->
      not_proven
        (span
       ^ "fn f(range: mut Span)\n  requires range.low > 0\n{\n  range.high = range.low - 1\n}\n")
        "prover.invariant");
  test "a body may break an invariant between calls" (fun () ->
      proven
        (span
       ^ "fn f(range: mut Span)\n\
         \  requires range.high < 1000\n\
          {\n\
         \  range.low = range.high + 1\n\
         \  range.low = range.high\n\
          }\n"));
  test "a value passed to a call must meet its invariant" (fun () ->
      not_proven
        (span
       ^ "fn use_span(range: Span) {}\n\n\
          fn f(range: mut Span)\n\
         \  requires range.high < 1000\n\
          {\n\
         \  range.low = range.high + 1\n\
         \  use_span(range)\n\
         \  range.low = range.high\n\
          }\n")
        "prover.invariant");
  test "a private method that takes mut self is a step of an update" (fun () ->
      proven
        (span
       ^ "fn Span.restore(mut self)\n\
         \  ensures self.low <= self.high\n\
          {\n\
         \  self.low = self.high\n\
          }\n\n\
          public fn Span.shift(mut self)\n\
         \  requires self.high < 1000\n\
          {\n\
         \  self.low = self.high + 1\n\
         \  mut self.restore()\n\
          }\n"))

(* What is not proven yet *)

let () =
  test "a construct the prover cannot read yet" (fun () ->
      not_proven "fn f(text: String) -> String {\n  \"${text}!\"\n}\n" "prover.unsupported");
  test "a cost bound is reported as not proven yet" (fun () ->
      not_proven "fn f() -> Int64\n  cost time O(1)\n{\n  0\n}\n" "prover.unsupported")

(* Queries *)

let () =
  test "a query's text names nothing by its Truss name" (fun () ->
      let database =
        Support.setup [ ("app::main", "fn f(count: UInt8) -> UInt8 {\n  count + 1\n}\n") ]
      in
      let key =
        List.hd (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))
      in
      match Query.demand database Prover.proof (Resolve.Names.key_of key) with
      | Obligations { obligations = [ obligation ]; _ } ->
          let text = Logic.text obligation.query in
          if contains text "count" then fail "the text names `count`: %s" text
      | _ -> fail "expected one obligation");
  test "renaming a function and its parameter gives the same query" (fun () ->
      let key_of text =
        let database = Support.setup [ ("app::main", text) ] in
        let key =
          List.hd (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))
        in
        match Query.demand database Prover.proof (Resolve.Names.key_of key) with
        | Obligations { obligations = [ obligation ]; _ } -> Solver.key obligation.query
        | _ -> "none"
      in
      let first = key_of "fn f(count: UInt8) -> UInt8 {\n  count + 1\n}\n" in
      let second = key_of "fn g(total: UInt8) -> UInt8 {\n  total + 1\n}\n" in
      if first <> second || first = "none" then fail "%s and %s" first second)

let () = finish ()
