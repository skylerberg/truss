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

(* The codes of a file's diagnostics. *)
let codes text =
  let database = Support.setup [ ("app::main", text) ] in
  Support.codes (check database (Support.module_of "app::main"))

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

(* Models *)

let () =
  test "a push's contract, through the list's model" (fun () ->
      proven
        "fn f(items: mut List[Int64])\n\
        \  ensures items.length() == old(items.length()) + 1\n\
        \  ensures items[old(items.length())] == 5\n\
         {\n\
        \  mut items.push(5)\n\
         }\n");
  test "a push does not keep the length" (fun () ->
      not_proven
        "fn f(items: mut List[Int64])\n\
        \  ensures items.length() == old(items.length())\n\
         {\n\
        \  mut items.push(5)\n\
         }\n"
        "prover.ensures");
  test "an index into a list after a push is in bounds" (fun () ->
      proven
        "fn f(items: mut List[Int64]) -> Int64\n\
        \  requires items.length() == 0\n\
         {\n\
        \  mut items.push(7)\n\
        \  items[0]\n\
         }\n");
  test "identical is the same value, for any type" (fun () ->
      proven "fn f[Item](value: Item) -> Bool\n  ensures identical(value, value)\n{\n  true\n}\n")

let () =
  test "a loop over a list runs once per element" (fun () ->
      proven
        "fn f(items: List[Int64]) -> USize\n\
        \  ensures result == items.length()\n\
         {\n\
        \  var seen: USize = 0\n\
        \  for item in items\n\
        \    invariant seen == yielded.length()\n\
        \  {\n\
        \    let _ = item\n\
        \    seen += 1\n\
        \  }\n\
        \  seen\n\
         }\n");
  test "a loop's element is the list's element at its position" (fun () ->
      proven
        "fn f(items: List[Int64]) -> Bool\n\
        \  ensures result ==> (forall i in 0..items.length() => items[i] > 0)\n\
         {\n\
        \  for item in items\n\
        \    invariant forall i in 0..yielded.length() => items[i] > 0\n\
        \  {\n\
        \    if item <= 0 { return false }\n\
        \  }\n\
        \  true\n\
         }\n");
  test "a loop over a list does not run once more" (fun () ->
      not_proven
        "fn f(items: List[Int64]) -> USize\n\
        \  ensures result == items.length() + 1\n\
         {\n\
        \  var seen: USize = 0\n\
        \  for item in items\n\
        \    invariant seen == yielded.length()\n\
        \  {\n\
        \    let _ = item\n\
        \    seen += 1\n\
        \  }\n\
        \  seen\n\
         }\n"
        "prover.ensures")

let couple =
  "type Couple(first: Int64, second: Int64)\n\n\
   fn Couple.each(self) yields Int64\n\
  \  ensures result == self.first || result == self.second\n\
  \  ensures yielded.length() <= 2\n\
  \  ensures finished ==> yielded.length() == 2\n\
  \  cost time finite\n\
   {\n\
  \  yield self.first\n\
  \  yield self.second\n\
   }\n\n"

let () =
  test "a yielding method keeps its contract at each yield and at its end" (fun () -> proven couple);
  test "a yielding method that hands out more than it promises" (fun () ->
      not_proven
        "type Couple(first: Int64, second: Int64)\n\n\
         fn Couple.each(self) yields Int64\n\
        \  ensures yielded.length() <= 1\n\
        \  cost time finite\n\
         {\n\
        \  yield self.first\n\
        \  yield self.second\n\
         }\n"
        "prover.ensures");
  test "a loop over a user's yielding method gets its facts" (fun () ->
      proven
        (couple
       ^ "fn f(couple: Couple) -> USize\n\
         \  ensures result == 2\n\
          {\n\
         \  var seen: USize = 0\n\
         \  for value in couple\n\
         \    invariant seen == yielded.length()\n\
         \  {\n\
         \    let _ = value\n\
         \    seen += 1\n\
         \  }\n\
         \  seen\n\
          }\n"));
  test "a loop over a range has its indexes as yielded" (fun () ->
      proven
        "fn f(count: UInt32) -> UInt32\n\
        \  ensures result == count\n\
         {\n\
        \  var seen: UInt32 = 0\n\
        \  for _ in 0..count\n\
        \    invariant seen == yielded.length()\n\
        \  {\n\
        \    seen += 1\n\
        \  }\n\
        \  seen\n\
         }\n");
  test "a while loop in a yielding method names what the method handed out" (fun () ->
      proven
        "type Counter(limit: UInt32)\n\n\
         fn Counter.each(self) yields UInt32\n\
        \  ensures yielded.length() <= self.limit\n\
        \  cost time finite\n\
         {\n\
        \  var next: UInt32 = 0\n\
        \  while next < self.limit\n\
        \    invariant next <= self.limit\n\
        \    invariant next == yielded.length()\n\
        \  {\n\
        \    yield next\n\
        \    next += 1\n\
        \  }\n\
         }\n");
  test "a pull of a cursor meets its method's clauses for each part" (fun () ->
      proven
        (couple
       ^ "fn f(couple: Couple) -> Int64\n\
         \  requires couple.first == 1 && couple.second == 1\n\
         \  ensures result == 1\n\
          {\n\
         \  var cursor = couple.each()\n\
         \  match mut cursor.next() {\n\
         \    Some(value) => value\n\
         \    None => 1\n\
         \  }\n\
          }\n"));
  test "a cursor ends where its method says it has handed out all it will" (fun () ->
      proven
        (couple
       ^ "fn f(couple: Couple) -> Bool\n\
         \  ensures result\n\
          {\n\
         \  var cursor = couple.each()\n\
         \  let _ = mut cursor.next()\n\
         \  let _ = mut cursor.next()\n\
         \  mut cursor.next() is None\n\
          }\n"));
  test "a cursor's next pull is not known to end early" (fun () ->
      not_proven
        (couple
       ^ "fn f(couple: Couple) -> Bool\n\
         \  ensures result\n\
          {\n\
         \  var cursor = couple.each()\n\
         \  let _ = mut cursor.next()\n\
         \  mut cursor.next() is None\n\
          }\n")
        "prover.ensures");
  test "a loop over a cursor gets its method's facts" (fun () ->
      proven
        (couple
       ^ "fn f(couple: Couple) -> USize\n\
         \  ensures result <= 2\n\
          {\n\
         \  var cursor = couple.each()\n\
         \  var seen: USize = 0\n\
         \  for value in cursor\n\
         \    invariant seen <= yielded.length()\n\
         \  {\n\
         \    let _ = value\n\
         \    seen += 1\n\
         \  }\n\
         \  seen\n\
          }\n"));
  test "a loop over a type's own cursor calls its next" (fun () ->
      proven
        "type Countdown(left: UInt8)\n\n\
         impl Cursor for Countdown {\n\
        \  type Element = UInt8\n\n\
        \  fn next(mut self) -> Option[UInt8]\n\
        \    ensures result != None ==> self.left < old(self.left)\n\
        \    ensures result != None ==> result == Some(self.left)\n\
        \    cost time finite\n\
        \  {\n\
        \    if self.left == 0 { None } else {\n\
        \      self.left -= 1\n\
        \      Some(self.left)\n\
        \    }\n\
        \  }\n\
         }\n\n\
         fn f(start: Countdown) -> UInt8\n\
        \  cost time finite\n\
         {\n\
        \  var left = start\n\
        \  var last: UInt8 = 0\n\
        \  for value in left\n\
        \    decreases left.left\n\
        \  {\n\
        \    last = value\n\
        \  }\n\
        \  last\n\
         }\n");
  test "assigning an element changes only that element" (fun () ->
      proven
        "fn f(items: mut List[Int64])\n\
        \  requires items.length() > 1\n\
        \  ensures items.length() == old(items.length())\n\
        \  ensures items[0] == 0\n\
        \  ensures items[1] == old(items[1])\n\
         {\n\
        \  items[0] = 0\n\
         }\n");
  test "a compound assignment to an element" (fun () ->
      proven
        "fn f(items: mut List[UInt8])\n\
        \  requires items.length() > 0\n\
        \  requires items[0] < 255\n\
        \  ensures items[0] == old(items[0]) + 1\n\
         {\n\
        \  items[0] += 1\n\
         }\n")

(* Laws *)

let monoid =
  "trait Monoid: Equal {\n\
  \  fn empty() -> Self\n\
  \    cost time finite\n\
  \  fn combine(self, other: Self) -> Self\n\
  \    cost time finite\n\n\
  \  law left_identity(value: Self) {\n\
  \    Self.empty().combine(value) == value\n\
  \  }\n\
   }\n\n\
   type Flag(on: Bool)\n\
  \  derives Equal\n\n"

let flag_impl empty =
  Printf.sprintf
    "impl Monoid for Flag {\n\
    \  fn empty() -> Flag\n\
    \    cost time finite\n\
    \  {\n\
    \    Flag(on: %s)\n\
    \  }\n\n\
    \  fn combine(self, other: Flag) -> Flag\n\
    \    cost time finite\n\
    \  {\n\
    \    Flag(on: self.on || other.on)\n\
    \  }\n\
     }\n"
    empty

let () =
  test "an impl's methods keep its trait's law" (fun () -> proven (monoid ^ flag_impl "false"));
  test "an impl whose methods break its trait's law" (fun () ->
      not_proven (monoid ^ flag_impl "true") "prover.law");
  test "generic code relies on a bound's laws" (fun () ->
      proven
        (monoid ^ flag_impl "false"
       ^ "\n\
          fn f[Item: Monoid](value: Item) -> Bool\n\
         \  ensures result\n\
          {\n\
         \  Item.empty().combine(value) == value\n\
          }\n"))

let () =
  test "an impl's method keeps its trait's time clause, so its body is its definition" (fun () ->
      proven
        (monoid
       ^ "impl Monoid for Int64 {\n\
         \  fn empty() -> Int64 {\n\
         \    0\n\
         \  }\n\n\
         \  fn combine(self, other: Int64) -> Int64 {\n\
         \    self.wrapping_add(other)\n\
         \  }\n\
          }\n"))

(* The standard library's integer methods, by the intrinsic operations
   they call *)

let () =
  test "wrapping arithmetic is a remainder" (fun () ->
      proven
        "fn f(first: Int64, second: Int64, third: Int64) -> Bool\n\
        \  ensures result\n\
        \  cost time O(1)\n\
         {\n\
        \  first.wrapping_add(second).wrapping_add(third)\n\
        \    == first.wrapping_add(second.wrapping_add(third))\n\
         }\n");
  test "wrapping subtraction wraps below zero" (fun () ->
      proven
        "fn f(value: UInt8) -> UInt8\n\
        \  requires value == 1\n\
        \  ensures result == 255\n\
         {\n\
        \  value.wrapping_subtract(2)\n\
         }\n");
  test "saturating addition stops at the bound" (fun () ->
      proven
        "fn f(value: Int8) -> Int8\n\
        \  requires value >= 0\n\
        \  ensures result == Int8.maximum\n\
         {\n\
        \  value.saturating_add(127)\n\
         }\n");
  test "saturating addition is exact where it fits" (fun () ->
      proven
        "fn f(first: Int8, second: Int8) -> Int8\n\
        \  requires first + second <= Int8.maximum\n\
        \  requires first + second >= Int8.minimum\n\
        \  ensures result == first + second\n\
         {\n\
        \  first.saturating_add(second)\n\
         }\n");
  test "a checked addition is none exactly when it overflows" (fun () ->
      proven
        "fn f(value: UInt8) -> Bool\n\
        \  ensures result == (value > 0)\n\
         {\n\
        \  value.checked_add(255).is_none()\n\
         }\n");
  test "a conversion succeeds exactly when the value fits" (fun () ->
      proven
        "fn f(value: Int64) -> Bool\n\
        \  ensures result == (0 <= value && value <= 255)\n\
         {\n\
        \  UInt8.try_from(value).is_ok()\n\
         }\n");
  test "wrapping is not exact arithmetic" (fun () ->
      not_proven
        "fn f(value: UInt8) -> UInt8\n  ensures result > value\n{\n  value.wrapping_add(1)\n}\n"
        "prover.ensures")

let doubling =
  "trait Doubling {\n\
  \  fn value(self) -> Int64\n\
  \    cost time finite\n\n\
  \  fn doubled(self) -> Bool\n\
  \    cost time finite\n\
  \  {\n\
  \    self.value() > 0\n\
  \  }\n\
   }\n\n\
   type Amount(cents: Int64)\n\n"

let amount_impl replacement =
  Printf.sprintf
    "impl Doubling for Amount {\n\
    \  fn value(self) -> Int64\n\
    \    cost time finite\n\
    \  {\n\
    \    self.cents\n\
    \  }\n\n\
    \  fn doubled(self) -> Bool\n\
    \    cost time finite\n\
    \  {\n\
    \    %s\n\
    \  }\n\
     }\n"
    replacement

let () =
  test "a replacement that gives the provided body's result" (fun () ->
      proven (doubling ^ amount_impl "self.cents > 0"));
  test "a replacement that gives another result" (fun () ->
      not_proven (doubling ^ amount_impl "self.cents >= 0") "prover.ensures")

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

(* Functions named as values *)

let run =
  "fn run(transform: (fn(UInt32) -> UInt32 cost time O(1))) -> UInt32\n\
  \  cost time O(1)\n\
   {\n\
  \  transform(1)\n\
   }\n\n"

let () =
  test "a named function that keeps its parameter type's cost" (fun () ->
      proven
        (run
       ^ "fn same(value: UInt32) -> UInt32\n\
         \  cost time O(1)\n\
          {\n\
         \  value\n\
          }\n\n\
          fn f() -> UInt32\n\
         \  cost time O(1)\n\
          {\n\
         \  run(same)\n\
          }\n"));
  test "a named function that does not keep its parameter type's cost" (fun () ->
      not_proven
        (run
       ^ "fn spin(value: UInt32) -> UInt32\n\
         \  cost time O(value)\n\
          {\n\
         \  for _ in 0..value {\n\
         \  }\n\
         \  value\n\
          }\n\n\
          fn f() -> UInt32 {\n\
         \  run(spin)\n\
          }\n")
        "prover.cost");
  test "a named function must accept what its parameter's type promises" (fun () ->
      not_proven
        "fn apply(limit: USize, visit: (fn(index: USize) requires index < limit)) {\n\
        \  if limit > 0 {\n\
        \    visit(0)\n\
        \  }\n\
         }\n\n\
         fn check(index: USize)\n\
        \  requires index < 5\n\
         {\n\
         }\n\n\
         fn f() {\n\
        \  apply(10, visit: check)\n\
         }\n"
        "prover.requires");
  test "a named function that accepts what its parameter's type promises" (fun () ->
      proven
        "fn apply(limit: USize, visit: (fn(index: USize) requires index < limit)) {\n\
        \  if limit > 0 {\n\
        \    visit(0)\n\
        \  }\n\
         }\n\n\
         fn check(index: USize)\n\
        \  requires index < 10\n\
         {\n\
         }\n\n\
         fn f() {\n\
        \  apply(10, visit: check)\n\
         }\n");
  test "naming a function that reaches back is recursion that cannot be shown to end" (fun () ->
      not_proven
        (run ^ "fn again(value: UInt32) -> UInt32\n  cost time O(1)\n{\n  run(again)\n}\n")
        "prover.termination")

(* Sequences *)

let () =
  test "a list literal has its elements in order" (fun () ->
      proven
        "fn f() -> Int64\n\
        \  ensures result == 2\n\
         {\n\
        \  let items: List[Int64] = [1, 2, 3]\n\
        \  items[1]\n\
         }\n");
  test "a list literal has its length" (fun () ->
      proven "fn f() -> List[Int64]\n  ensures result.length() == 3\n{\n  [1, 2, 3]\n}\n");
  test "a non-empty list literal is one allocation" (fun () ->
      proven "fn f() -> List[Int64]\n  cost allocations == 1\n{\n  [1, 2, 3]\n}\n");
  test "sequences with the same elements are identical" (fun () ->
      proven
        "fn f(items: mut List[Int64])\n\
        \  requires items.length() > 0\n\
        \  ensures identical(items.model(), old(items.model()))\n\
         {\n\
        \  let first = items[0]\n\
        \  items[0] = first\n\
         }\n");
  test "sequences that differ in one element are not identical" (fun () ->
      not_proven
        "fn f(items: mut List[Int64])\n\
        \  requires items.length() > 0\n\
        \  ensures identical(items.model(), old(items.model()))\n\
         {\n\
        \  items[0] = 7\n\
         }\n"
        "prover.ensures")

(* Bitwise operations *)

let () =
  test "a value or itself is itself, bit for bit" (fun () ->
      proven "fn f(value: UInt32) -> UInt32\n  ensures result == value\n{\n  value | value\n}\n");
  test "a value xor itself is zero" (fun () ->
      proven "fn f(value: UInt64) -> UInt64\n  ensures result == 0\n{\n  value ^ value\n}\n");
  test "signed bitwise operations are two's complement" (fun () ->
      proven "fn f(value: Int8) -> Int8\n  ensures result == -1\n{\n  value | -1\n}\n");
  test "a shift by a literal is a multiplication" (fun () ->
      proven
        "fn f(value: UInt8) -> UInt8\n\
        \  requires value < 16\n\
        \  ensures result == value * 16\n\
         {\n\
        \  value << 4\n\
         }\n");
  test "a bitwise fact that does not hold has a counterexample" (fun () ->
      not_proven "fn f(value: UInt32) -> Bool\n  ensures result\n{\n  (value & 1) == 0\n}\n"
        "prover.ensures")

(* Slices *)

let () =
  test "a slice's elements are its collection's, from its start" (fun () ->
      proven
        "fn f(items: List[Int64]) -> Int64\n\
        \  requires items.length() > 3\n\
        \  ensures result == items[2]\n\
         {\n\
        \  let part = items[1..3]\n\
        \  part[1]\n\
         }\n");
  test "a list passed as a slice is a view with its model" (fun () ->
      proven
        "fn count(items: Slice[Int64]) -> USize\n\
        \  ensures result == items.length()\n\
        \  cost time O(1)\n\
         {\n\
        \  items.length()\n\
         }\n\n\
         fn f(items: List[Int64]) -> USize\n\
        \  ensures result == items.length()\n\
         {\n\
        \  count(items)\n\
         }\n");
  test "a slice must be within its collection" (fun () ->
      not_proven "fn f(items: List[Int64]) -> Slice[Int64] {\n  items[0..5]\n}\n" "prover.requires");
  test "two slices lent together must not overlap" (fun () ->
      not_proven
        "fn both(first: mut Slice[Int64], second: mut Slice[Int64]) {}\n\n\
         fn f(items: mut List[Int64])\n\
        \  requires items.length() > 3\n\
         {\n\
        \  both(mut items[0..2], second: mut items[1..3])\n\
         }\n"
        "prover.disjoint");
  test "two halves of a list can be lent together" (fun () ->
      proven
        "fn both(first: mut Slice[Int64], second: mut Slice[Int64]) {}\n\n\
         fn f(items: mut List[Int64], middle: USize)\n\
        \  requires middle <= items.length()\n\
         {\n\
        \  both(mut items[..middle], second: mut items[middle..])\n\
         }\n")

(* Strings *)

let () =
  test "a string literal's length is its bytes'" (fun () ->
      proven "fn f() -> USize\n  ensures result == 4\n{\n  \"abcé\".length() - 1\n}\n");
  test "pushing text onto a string adds its length" (fun () ->
      proven
        "fn f() -> USize\n\
        \  ensures result == 5\n\
         {\n\
        \  var text = \"ab\"\n\
        \  mut text.push(\"cde\")\n\
        \  text.length()\n\
         }\n");
  test "a string pattern matches text with its bytes" (fun () ->
      proven
        "fn f(text: String) -> USize\n\
        \  ensures result <= 3\n\
         {\n\
        \  match text {\n\
        \    \"yes\" => text.length()\n\
        \    _ => 0\n\
        \  }\n\
         }\n");
  test "an interpolated string is a string about which little is known" (fun () ->
      not_proven
        "fn f(count: Int64) -> USize\n  ensures result == 1\n{\n  \"${count}\".length()\n}\n"
        "prover.ensures")

(* Tagged templates *)

let shout =
  "type Shout(text: String)\n\n\
   impl FromTemplate for Shout {\n\
  \  type Part = String\n\n\
  \  fn from_template(template: Template[String]) -> Shout\n\
  \    requires template.literals.length() == 1\n\
  \  {\n\
  \    todo\n\
  \  }\n\
   }\n\n"

let () =
  test "a tagged template meets its tag's requires" (fun () ->
      proven (shout ^ "fn f() -> Shout {\n  Shout\"hey\"\n}\n"));
  test "a call of from_template through a bound cannot see the tag's requires" (fun () ->
      not_proven
        "fn make[Made: FromTemplate](template: Template[Made.Part]) -> Made {\n\
        \  Made.from_template(template)\n\
         }\n"
        "prover.requires");
  test "a tagged template that does not meet its tag's requires" (fun () ->
      not_proven
        (shout ^ "fn f(name: String) -> Shout {\n  Shout\"hey ${name}\"\n}\n")
        "prover.requires")

(* Floats *)

let () =
  test "float equality is reflexive, even for NaN" (fun () ->
      proven "fn f(value: Float64) -> Bool\n  ensures result\n{\n  value == value\n}\n");
  test "every float is ordered, NaN last" (fun () ->
      proven "fn f(value: Float64) -> Bool\n  ensures result\n{\n  value <= value\n}\n");
  test "float arithmetic is exact where IEEE 754 is" (fun () ->
      proven "fn f() -> Float64\n  ensures result == 0.5\n{\n  0.25 + 0.25\n}\n");
  test "adding zero keeps a float equal, with -0.0 equal to 0.0" (fun () ->
      proven "fn f(value: Float64) -> Bool\n  ensures result\n{\n  value + 0.0 == value\n}\n");
  test "adding one does not always make a float larger" (fun () ->
      not_proven "fn f(value: Float64) -> Float64\n  ensures result > value\n{\n  value + 1.0\n}\n"
        "prover.ensures");
  test "a derived equality over floats compares field by field" (fun () ->
      proven
        "type Point(x: Float64, y: Float64)\n\
        \  derives Equal\n\n\
         fn f() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  Point(x: 0.0, y: 1.0) == Point(x: -0.0, y: 1.0)\n\
         }\n");
  test "equal points have equal fields" (fun () ->
      proven
        "type Point(x: Float64, y: Float64)\n\
        \  derives Equal\n\n\
         fn f(a: Point, b: Point) -> Bool\n\
        \  requires a == b\n\
        \  ensures result\n\
         {\n\
        \  a.x == b.x\n\
         }\n");
  test "points equal by their fields are not identical" (fun () ->
      not_proven
        "type Point(x: Float64, y: Float64)\n\
        \  derives Equal\n\n\
         fn f(a: Point, b: Point) -> Bool\n\
        \  requires a == b\n\
        \  ensures result\n\
         {\n\
        \  1.0 / a.x == 1.0 / b.x\n\
         }\n"
        "prover.ensures");
  test "a float counterexample is written as Truss writes floats" (fun () ->
      let found =
        message "fn f(value: Float32) -> Bool\n  ensures result\n{\n  value * 0.0 == 0.0\n}\n"
      in
      if not (contains found "infinity" || contains found "NaN") then fail "message %S" found)

(* Capabilities *)

let dice = "capability Dice {\n  fn roll() -> UInt8\n    ensures result >= 1 && result <= 6\n}\n\n"

let () =
  test "a capability's method keeps its ensures" (fun () ->
      proven (dice ^ "fn f() -> UInt8\n  uses Dice\n  ensures result <= 6\n{\n  Dice.roll()\n}\n"));
  test "two calls of a capability's method may differ" (fun () ->
      not_proven
        (dice
       ^ "fn f() -> Bool\n  uses Dice\n  ensures result\n{\n  Dice.roll() == Dice.roll()\n}\n")
        "prover.ensures");
  test "a call must meet a capability method's requires" (fun () ->
      not_proven
        "capability Store {\n\
        \  fn put(slot: UInt8)\n\
        \    requires slot < 4\n\
         }\n\n\
         fn f() uses Store {\n\
        \  Store.put(9)\n\
         }\n"
        "prover.requires")

(* Sets and maps *)

let () =
  test "a set contains what was inserted" (fun () ->
      proven
        "fn f(items: mut Set[Int64]) -> Bool\n\
        \  ensures result\n\
         {\n\
        \  mut items.insert(5)\n\
        \  items.contains(5)\n\
         }\n");
  test "inserting what a set contains leaves it as it was" (fun () ->
      proven
        "fn f(items: mut Set[Int64])\n\
        \  requires items.model().contains(5)\n\
        \  ensures identical(items.model(), old(items.model()))\n\
         {\n\
        \  mut items.insert(5)\n\
         }\n");
  test "inserting into a set may change it" (fun () ->
      not_proven
        "fn f(items: mut Set[Int64])\n\
        \  ensures identical(items.model(), old(items.model()))\n\
         {\n\
        \  mut items.insert(5)\n\
         }\n"
        "prover.ensures");
  test "a map holds what was inserted under its key" (fun () ->
      proven
        "fn f(table: mut Map[Int64, Int64])\n\
        \  ensures table.model().contains_key(1) && table.model().get(1) == 2\n\
         {\n\
        \  mut table.insert(1, value: 2)\n\
         }\n");
  test "a map keeps its other keys' values" (fun () ->
      proven
        "fn f(table: mut Map[Int64, Int64])\n\
        \  requires table.model().contains_key(3)\n\
        \  ensures table.model().contains_key(3)\n\
        \  ensures table.model().get(3) == old(table.model().get(3))\n\
         {\n\
        \  mut table.insert(1, value: 2)\n\
         }\n")

(* Literals of maps and sets, any, provide, and let else *)

let () =
  test "a map literal holds each key's value" (fun () ->
      proven
        "fn f() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  let table: Map[Int64, Int64] = [1: 2, 3: 4]\n\
        \  table.contains(3)\n\
         }\n");
  test "a map literal's keys must be distinct" (fun () ->
      not_proven "fn f() -> Map[Int64, Int64] {\n  [1: 2, 1: 3]\n}\n" "prover.disjoint");
  test "a set literal contains what it lists and nothing else" (fun () ->
      proven
        "fn f() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  let colors: Set[Int64] = [1, 2]\n\
        \  colors.contains(2) && !colors.contains(5)\n\
         }\n");
  test "any is one allocation" (fun () ->
      proven "fn f(value: Int64) -> any Display\n  cost allocations == 1\n{\n  any value\n}\n");
  test "a provided implementation's calls keep the capability's contract" (fun () ->
      proven
        (dice
       ^ "type Fixed()\n\n\
          impl Dice for Fixed {\n\
         \  fn roll(self) -> UInt8 {\n\
         \    4\n\
         \  }\n\
          }\n\n\
          fn f() -> UInt8\n\
         \  ensures result <= 6\n\
          {\n\
         \  provide Fixed() {\n\
         \    Dice.roll()\n\
         \  }\n\
          }\n"));
  test "let else continues where its pattern matched" (fun () ->
      proven
        "fn f(found: Option[UInt8]) -> UInt8 {\n\
        \  let Some(value) = found else {\n\
        \    return 0\n\
        \  }\n\
        \  if value < 255 { value + 1 } else { value }\n\
         }\n");
  test "a quantifier's pattern takes each element apart" (fun () ->
      proven
        "type Span(low: Int64, high: Int64)\n\n\
         fn f(spans: List[Span]) -> Bool\n\
        \  requires forall (low, high) in spans => low <= high\n\
        \  ensures result\n\
         {\n\
        \  spans.length() == 0 || spans[0].low <= spans[0].high\n\
         }\n");
  test "a quantifier over a range may ignore its index" (fun () ->
      proven "fn f(count: Int64) -> Bool\n  ensures result\n{\n  forall _ in 0..count => true\n}\n");
  test "a quantifier over a list ranges over its elements" (fun () ->
      proven
        "fn f(items: List[Int64]) -> Bool\n\
        \  requires forall item in items => item > 0\n\
        \  ensures result\n\
         {\n\
        \  items.length() == 0 || items[0] > 0\n\
         }\n")

(* Places lent together *)

let swap =
  "fn exchange(first: mut Int64, second: mut Int64) {\n\
  \  let kept = first\n\
  \  first = second\n\
  \  second = kept\n\
   }\n\n"

let () =
  test "two elements lent together must be different elements" (fun () ->
      not_proven
        (swap
       ^ "fn f(items: mut List[Int64], first: USize, second: USize)\n\
         \  requires first < items.length() && second < items.length()\n\
          {\n\
         \  exchange(mut items[first], second: mut items[second])\n\
          }\n")
        "prover.disjoint");
  test "two different elements can be lent together" (fun () ->
      proven
        (swap
       ^ "fn f(items: mut List[Int64], first: USize, second: USize)\n\
         \  requires first < items.length() && second < items.length() && first != second\n\
          {\n\
         \  exchange(mut items[first], second: mut items[second])\n\
          }\n"));
  test "parallel branches that change elements must change different ones" (fun () ->
      not_proven
        "fn f(items: mut List[Int64], first: USize, second: USize)\n\
        \  requires first < items.length() && second < items.length()\n\
         {\n\
        \  parallel {\n\
        \    items[first] = 1\n\
        \    items[second] = 2\n\
        \  }\n\
         }\n"
        "prover.disjoint")

(* Where paths join *)

let () =
  test "self changed on one path is joined with the other" (fun () ->
      not_proven
        "type Box(value: Int64)\n\n\
         fn Box.set(mut self, flag: Bool)\n\
        \  ensures self.value == old(self.value)\n\
         {\n\
        \  if flag {\n\
        \    self.value = 1\n\
        \  }\n\
         }\n"
        "prover.ensures");
  test "what a method hands out on one path is joined with the other" (fun () ->
      not_proven
        "type Maybe(present: Bool)\n\n\
         fn Maybe.each(self) yields Int64\n\
        \  ensures yielded.length() == 0\n\
        \  cost time finite\n\
         {\n\
        \  if self.present {\n\
        \    yield 1\n\
        \  }\n\
         }\n"
        "prover.ensures")

(* What a loop changes *)

let () =
  test "a loop forgets a list it changes through a method" (fun () ->
      not_proven
        "fn f(count: UInt32) -> USize {\n\
        \  var items: List[UInt32] = List.with_capacity(0)\n\
        \  for index in 0..count {\n\
        \    mut items.push(index)\n\
        \  }\n\
        \  proof {\n\
        \    assert items.length() == 0\n\
        \  }\n\
        \  items.length()\n\
         }\n"
        "prover.assertion");
  test "a loop forgets a record whose field it assigns" (fun () ->
      not_proven
        "type Box(value: Int64)\n\n\
         fn f(count: UInt32) -> Int64 {\n\
        \  var box = Box(value: 0)\n\
        \  for _ in 0..count {\n\
        \    box.value = 1\n\
        \  }\n\
        \  proof {\n\
        \    assert box.value == 0\n\
        \  }\n\
        \  box.value\n\
         }\n"
        "prover.assertion");
  test "a loop forgets self when it changes it" (fun () ->
      not_proven
        "type Box(value: Int64)\n\n\
         fn Box.fill(mut self, count: UInt32)\n\
        \  requires self.value == 0\n\
         {\n\
        \  for _ in 0..count {\n\
        \    self.value = 1\n\
        \  }\n\
        \  proof {\n\
        \    assert self.value == 0\n\
        \  }\n\
         }\n"
        "prover.assertion")

(* Costs *)

let constant_step = "fn step(value: UInt32) -> UInt32\n  cost time O(1)\n{\n  value\n}\n\n"

let () =
  test "a body with no calls is O(1)" (fun () ->
      proven "fn f() -> Int64\n  cost time O(1)\n{\n  0\n}\n");
  test "calls to O(1) functions are O(1)" (fun () ->
      proven
        (constant_step
       ^ "fn f(value: UInt32) -> UInt32\n  cost time O(1)\n{\n  step(step(value))\n}\n"));
  test "a call to a function with no bound on its time" (fun () ->
      not_proven
        "fn g() -> Int64\n\
        \  cost time finite\n\
         {\n\
        \  0\n\
         }\n\n\
         fn f() -> Int64\n\
        \  cost time O(1)\n\
         {\n\
        \  g()\n\
         }\n"
        "prover.cost");
  test "a loop over a range is linear" (fun () ->
      proven
        (constant_step
       ^ "fn f(count: UInt32)\n\
         \  cost time O(count)\n\
          {\n\
         \  for index in 0..count {\n\
         \    let _ = step(index)\n\
         \  }\n\
          }\n"));
  test "a loop over a range is not constant" (fun () ->
      not_proven
        (constant_step
       ^ "fn f(count: UInt32)\n\
         \  cost time O(1)\n\
          {\n\
         \  for index in 0..count {\n\
         \    let _ = step(index)\n\
         \  }\n\
          }\n")
        "prover.cost");
  test "nested loops over ranges are quadratic" (fun () ->
      proven
        (constant_step
       ^ "fn f(count: UInt32)\n\
         \  cost time O(count * count)\n\
          {\n\
         \  for row in 0..count {\n\
         \    for _ in 0..count {\n\
         \      let _ = step(row)\n\
         \    }\n\
         \  }\n\
          }\n"));
  test "a loop whose iterations cost their index is quadratic" (fun () ->
      proven
        "fn work(size: UInt32)\n\
        \  cost time O(size)\n\
         {\n\
        \  for _ in 0..size {\n\
        \  }\n\
         }\n\n\
         fn f(count: UInt32)\n\
        \  cost time O(count * count)\n\
         {\n\
        \  for index in 0..count {\n\
        \    work(index)\n\
        \  }\n\
         }\n");
  test "a loop over a list runs once per element" (fun () ->
      proven
        (constant_step
       ^ "fn f(items: List[UInt32])\n\
         \  cost time O(items.length())\n\
          {\n\
         \  for item in items {\n\
         \    let _ = step(item)\n\
         \  }\n\
          }\n"));
  test "an iteration's cost is the larger of its branches'" (fun () ->
      proven
        "fn work(size: UInt32)\n\
        \  cost time O(size)\n\
         {\n\
        \  for _ in 0..size {\n\
        \  }\n\
         }\n\n\
         fn f(items: List[UInt32], size: UInt32)\n\
        \  cost time O(items.length() * (size + 1))\n\
         {\n\
        \  for item in items {\n\
        \    if item > 3 {\n\
        \      work(size)\n\
        \    } else {\n\
        \      work(1)\n\
        \    }\n\
        \  }\n\
         }\n");
  test "a while loop runs at most its measure's times" (fun () ->
      proven
        "fn f(count: UInt32)\n\
        \  cost time O(count)\n\
         {\n\
        \  var index: UInt32 = 0\n\
        \  while index < count {\n\
        \    index = index + 1\n\
        \  }\n\
         }\n");
  test "recursion on one less is linear" (fun () ->
      proven
        "fn f(count: UInt32) -> UInt32\n\
        \  decreases count\n\
        \  cost time O(count)\n\
         {\n\
        \  if count == 0 { 0 } else { f(count - 1) }\n\
         }\n");
  test "recursion on one less is not constant" (fun () ->
      not_proven
        "fn f(count: UInt32) -> UInt32\n\
        \  decreases count\n\
        \  cost time O(1)\n\
         {\n\
        \  if count == 0 { 0 } else { f(count - 1) }\n\
         }\n"
        "prover.cost");
  test "recursion on half is logarithmic" (fun () ->
      proven
        "fn f(count: UInt64) -> UInt64\n\
        \  decreases count\n\
        \  cost time O(log(count))\n\
         {\n\
        \  if count == 0 { 0 } else { f(count / 2) }\n\
         }\n");
  test "functions that call each other in a cycle share their constants" (fun () ->
      proven
        "fn even(count: UInt32) -> Bool\n\
        \  decreases count\n\
        \  cost time O(count)\n\
         {\n\
        \  if count == 0 { true } else { odd(count - 1) }\n\
         }\n\n\
         fn odd(count: UInt32) -> Bool\n\
        \  decreases count\n\
        \  cost time O(count)\n\
         {\n\
        \  if count == 0 { false } else { even(count - 1) }\n\
         }\n");
  test "a quantifier in code runs over its range" (fun () ->
      proven
        "fn all_positive(items: List[Int64]) -> Bool\n\
        \  cost time O(items.length())\n\
         {\n\
        \  forall index in 0..items.length() => items[index] > 0\n\
         }\n");
  test "calls through a function value are counted exactly" (fun () ->
      proven
        "fn each(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
        \  cost calls(visit) == items.length()\n\
        \  cost time O(items.length() * time(visit))\n\
         {\n\
        \  for item in items {\n\
        \    visit(item)\n\
        \  }\n\
         }\n");
  test "calling a function value twice per element is not once" (fun () ->
      not_proven
        "fn each(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
        \  cost calls(visit) == items.length()\n\
         {\n\
        \  for item in items {\n\
        \    visit(item)\n\
        \    visit(item)\n\
        \  }\n\
         }\n"
        "prover.cost");
  test "a caller counts the calls its callee promises" (fun () ->
      proven
        "fn each(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
        \  cost calls(visit) == items.length()\n\
         {\n\
        \  for item in items {\n\
        \    visit(item)\n\
        \  }\n\
         }\n\n\
         fn twice(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
        \  cost calls(visit) == items.length() + items.length()\n\
         {\n\
        \  each(items, visit)\n\
        \  each(items, visit)\n\
         }\n");
  test "a loop's cost clause bounds what it has spent" (fun () ->
      proven
        "fn f(count: UInt32)\n\
        \  cost time O(count)\n\
         {\n\
        \  var index: UInt32 = 0\n\
        \  while index < count\n\
        \    invariant index <= count\n\
        \    cost time O(index)\n\
        \  {\n\
        \    index = index + 1\n\
        \  }\n\
         }\n");
  test "a function value with an O(1) type is one unit" (fun () ->
      proven
        "fn run(transform: (fn(Int64) -> Int64 cost time O(1))) -> Int64\n\
        \  cost time O(1)\n\
         {\n\
        \  transform(1)\n\
         }\n\n\
         fn f() -> Int64\n\
        \  cost time O(1)\n\
         {\n\
        \  run(fn(value) { value })\n\
         }\n");
  test "a lambda must meet its type's cost" (fun () ->
      not_proven
        "fn run(count: UInt32, transform: (fn(UInt32) -> UInt32 cost time O(1))) -> UInt32 {\n\
        \  transform(count)\n\
         }\n\n\
         fn spin(size: UInt32)\n\
        \  cost time O(size)\n\
         {\n\
        \  for _ in 0..size {\n\
        \  }\n\
         }\n\n\
         fn f(count: UInt32) -> UInt32 {\n\
        \  run(count, transform: fn(value) {\n\
        \    spin(value)\n\
        \    value\n\
        \  })\n\
         }\n"
        "prover.cost");
  test "nothing allocates without a block to allocate" (fun () ->
      proven "fn f(value: Int64) -> Int64\n  cost allocations == 0\n{\n  value + 0\n}\n");
  test "building an indirect variant allocates" (fun () ->
      not_proven
        "type Tree =\n\
        \  | Leaf\n\
        \  | indirect Node(left: Tree, right: Tree)\n\n\
         fn f() -> Tree\n\
        \  cost allocations == 0\n\
         {\n\
        \  Tree.Node(left: Tree.Leaf, right: Tree.Leaf)\n\
         }\n"
        "prover.cost");
  test "an indirect variant is one allocation" (fun () ->
      proven
        "type Tree =\n\
        \  | Leaf\n\
        \  | indirect Node(left: Tree, right: Tree)\n\n\
         fn f() -> Tree\n\
        \  cost allocations == 1\n\
         {\n\
        \  Tree.Node(left: Tree.Leaf, right: Tree.Leaf)\n\
         }\n");
  test "nested loops are not linear" (fun () ->
      not_proven
        (constant_step
       ^ "fn f(count: UInt32)\n\
         \  cost time O(count)\n\
          {\n\
         \  for row in 0..count {\n\
         \    for _ in 0..count {\n\
         \      let _ = step(row)\n\
         \    }\n\
         \  }\n\
          }\n")
        "prover.cost");
  test "two recursive calls on one less are not linear" (fun () ->
      not_proven
        "fn f(count: UInt32) -> UInt32\n\
        \  decreases count\n\
        \  cost time O(count)\n\
         {\n\
        \  if count == 0 { 0 } else {\n\
        \    let _ = f(count - 1)\n\
        \    f(count - 1)\n\
        \  }\n\
         }\n"
        "prover.cost");
  test "functions in a cycle that branch are not linear" (fun () ->
      not_proven
        "fn ping(count: UInt32) -> UInt32\n\
        \  decreases count\n\
        \  cost time O(count)\n\
         {\n\
        \  if count == 0 { 0 } else {\n\
        \    let _ = pong(count - 1)\n\
        \    pong(count - 1)\n\
        \  }\n\
         }\n\n\
         fn pong(count: UInt32) -> UInt32\n\
        \  decreases count\n\
        \  cost time O(count)\n\
         {\n\
        \  if count == 0 { 0 } else { ping(count - 1) }\n\
         }\n"
        "prover.cost");
  test "a callback's time is not free" (fun () ->
      not_proven
        "fn each(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
        \  cost time O(items.length())\n\
         {\n\
        \  for item in items {\n\
        \    visit(item)\n\
        \  }\n\
         }\n"
        "prover.cost");
  test "calls through a lambda that captures the function value are not known" (fun () ->
      not_proven
        "fn each(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
        \  cost calls(visit) == items.length()\n\
         {\n\
        \  for item in items {\n\
        \    visit(item)\n\
        \  }\n\
         }\n\n\
         fn twice(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
        \  cost calls(visit) == items.length()\n\
         {\n\
        \  each(items, visit: fn(item) {\n\
        \    visit(item)\n\
        \    visit(item)\n\
        \  })\n\
         }\n"
        "prover.cost");
  test "a quantifier over a costly body is not linear" (fun () ->
      not_proven
        "fn spin(items: List[Int64]) -> Bool\n\
        \  cost time O(items.length())\n\
         {\n\
        \  for _ in items {\n\
        \  }\n\
        \  true\n\
         }\n\n\
         fn f(items: List[Int64]) -> Bool\n\
        \  cost time O(items.length())\n\
         {\n\
        \  forall index in 0..items.length() => index >= 0 && spin(items)\n\
         }\n"
        "prover.cost");
  test "a loop with no measure has no bound" (fun () ->
      let found =
        codes
          "fn f(count: UInt32)\n\
          \  cost time O(count)\n\
           {\n\
          \  var index: UInt32 = 0\n\
          \  while index != count {\n\
          \    index = index + 1\n\
          \  }\n\
           }\n"
      in
      if not (List.mem "prover.cost" found && List.mem "prover.termination" found) then
        fail "%s" (String.concat ", " found));
  test "a loop's cost clause that is too small" (fun () ->
      not_proven
        "fn f(count: UInt32)\n\
        \  cost time O(count)\n\
         {\n\
        \  var index: UInt32 = 0\n\
        \  while index < count\n\
        \    invariant index <= count\n\
        \    cost time O(1)\n\
        \  {\n\
        \    index = index + 1\n\
        \  }\n\
         }\n"
        "prover.cost");
  test "calls of a capability's method are counted" (fun () ->
      proven
        "capability Meter {\n\
        \  fn tick()\n\
         }\n\n\
         fn f(items: List[Int64])\n\
        \  uses Meter\n\
        \  cost calls(Meter.tick) == items.length()\n\
         {\n\
        \  for _ in items {\n\
        \    Meter.tick()\n\
        \  }\n\
         }\n");
  test "a callee's allocations add up" (fun () ->
      proven
        "type Tree =\n\
        \  | Leaf\n\
        \  | indirect Node(left: Tree, right: Tree)\n\n\
         fn node() -> Tree\n\
        \  cost allocations == 1\n\
         {\n\
        \  Tree.Node(left: Tree.Leaf, right: Tree.Leaf)\n\
         }\n\n\
         fn pair() -> Tree\n\
        \  cost allocations == 2\n\
         {\n\
        \  let _ = node()\n\
        \  node()\n\
         }\n");
  test "a lambda's time is bounded where it is written" (fun () ->
      proven
        "fn each(items: List[Int64], visit: (fn(Int64) cost time finite))\n\
        \  cost time O(items.length() * time(visit))\n\
         {\n\
        \  for item in items {\n\
        \    visit(item)\n\
        \  }\n\
         }\n\n\
         fn f(items: List[Int64])\n\
        \  cost time O(items.length())\n\
         {\n\
        \  each(items, visit: fn(item) {\n\
        \    let _ = item\n\
        \  })\n\
         }\n");
  test "a lambda that loops over its argument has no bound" (fun () ->
      let found =
        codes
          "fn each(items: List[UInt32], visit: (fn(UInt32) cost time finite))\n\
          \  cost time O(items.length() * time(visit))\n\
           {\n\
          \  for item in items {\n\
          \    visit(item)\n\
          \  }\n\
           }\n\n\
           fn f(items: List[UInt32])\n\
          \  cost time O(items.length())\n\
           {\n\
          \  each(items, visit: fn(item) {\n\
          \    for _ in 0..item {\n\
          \    }\n\
          \  })\n\
           }\n"
      in
      if not (List.mem "prover.cost" found) then fail "%s" (String.concat ", " found));
  test "a loop's cost clause over what it has received" (fun () ->
      proven
        (constant_step
       ^ "fn f(items: List[UInt32])\n\
         \  cost time O(items.length())\n\
          {\n\
         \  for item in items\n\
         \    cost time O(yielded.length())\n\
         \  {\n\
         \    let _ = step(item)\n\
         \  }\n\
          }\n"));
  test "an impl's method keeps its trait's cost" (fun () ->
      not_proven
        "trait Sized {\n\
        \  fn size(self) -> Int64\n\
        \    cost time O(1)\n\
         }\n\n\
         type Box(count: UInt32)\n\n\
         fn spin(size: UInt32)\n\
        \  cost time O(size)\n\
         {\n\
        \  for _ in 0..size {\n\
        \  }\n\
         }\n\n\
         impl Sized for Box {\n\
        \  fn size(self) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    spin(self.count)\n\
        \    0\n\
        \  }\n\
         }\n"
        "prover.cost")

(* Amortized costs *)

let meter =
  "type Meter(credit: UInt32)\n\
  \  cost potential credit\n\n\
   fn work(size: UInt32)\n\
  \  cost time O(size)\n\
   {\n\
  \  for _ in 0..size {\n\
  \  }\n\
   }\n\n\
   fn Meter.save(mut self)\n\
  \  requires self.credit < 1000\n\
  \  cost amortized time O(1)\n\
   {\n\
  \  self.credit = self.credit + 1\n\
   }\n\n\
   fn Meter.spend(mut self)\n\
  \  cost amortized time O(1)\n\
   {\n\
  \  work(self.credit)\n\
  \  self.credit = 0\n\
   }\n\n"

let () =
  test "saving and spending potential are amortized O(1)" (fun () -> proven meter);
  test "spending potential is not O(1) without it" (fun () ->
      not_proven
        "type Meter(credit: UInt32)\n\
        \  cost potential credit\n\n\
         fn work(size: UInt32)\n\
        \  cost time O(size)\n\
         {\n\
        \  for _ in 0..size {\n\
        \  }\n\
         }\n\n\
         fn Meter.spend(mut self)\n\
        \  cost time O(1)\n\
         {\n\
        \  work(self.credit)\n\
        \  self.credit = 0\n\
         }\n"
        "prover.cost");
  test "a plain bound pays for the potential it is given" (fun () ->
      proven
        (meter
       ^ "fn f(meter: mut Meter)\n  cost time O(1 + meter.credit)\n{\n  mut meter.spend()\n}\n"));
  test "a plain bound that does not pay for the potential it uses" (fun () ->
      not_proven
        (meter ^ "fn f(meter: mut Meter)\n  cost time O(1)\n{\n  mut meter.spend()\n}\n")
        "prover.cost");
  test "a loop that spends potential telescopes" (fun () ->
      proven
        (meter
       ^ "fn f(meter: mut Meter, count: UInt32)\n\
         \  cost time O(count + meter.credit)\n\
          {\n\
         \  for _ in 0..count {\n\
         \    mut meter.spend()\n\
         \  }\n\
          }\n"));
  test "a loop that spends potential it was given is not linear in its count" (fun () ->
      let found =
        codes
          (meter
         ^ "fn f(meter: mut Meter, count: UInt32)\n\
           \  cost time O(count)\n\
            {\n\
           \  for _ in 0..count {\n\
           \    mut meter.spend()\n\
           \  }\n\
            }\n")
      in
      if found <> [ "prover.cost" ] then fail "%s" (String.concat ", " found));
  test "a potential below zero" (fun () ->
      not_proven "type Debt(owed: Int64)\n  cost potential owed\n" "prover.cost");
  test "a potential its invariant keeps at or above zero" (fun () ->
      proven "type Debt(owed: Int64)\n  invariant owed >= 0\n  cost potential owed\n")

(* Holes *)

(* The number of holes in a file's proofs. *)
let holes text =
  let database = Support.setup [ ("app::main", text) ] in
  List.fold_left
    (fun total declaration ->
      match Query.demand database Prover.proof (Resolve.Names.key_of declaration) with
      | Obligations outcome -> total + List.length outcome.holes
      | Unsupported _ | Not_proven_here -> total)
    0
    (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))

let () =
  test "a todo in a theorem is a hole, not a failure" (fun () ->
      let text = "theorem t(count: Int64)\n  ensures count > count\n{\n  todo\n}\n" in
      proven text;
      if holes text <> 1 then fail "%d holes" (holes text));
  test "a todo in a proof block leaves what follows on its path to it" (fun () ->
      let text =
        "fn f(items: List[Int64], index: USize) -> Int64 {\n\
        \  proof {\n\
        \    todo\n\
        \  }\n\
        \  items[index]\n\
         }\n"
      in
      proven text;
      if holes text <> 1 then fail "%d holes" (holes text));
  test "a todo in code is no hole" (fun () ->
      let text = "fn f(value: Int64) -> Int64\n  ensures result > value\n{\n  todo\n}\n" in
      not_proven text "prover.ensures";
      if holes text <> 0 then fail "%d holes" (holes text))

(* What is not proven yet *)

let () =
  test "a construct the prover cannot read yet" (fun () ->
      not_proven "fn f() -> Range[Int64] {\n  0..3\n}\n" "prover.unsupported");
  test "alternatives bind each name to the part that matched" (fun () ->
      proven
        "type Side =\n\
        \  | Left(value: Int64)\n\
        \  | Right(value: Int64)\n\
        \  derives Equal\n\n\
         fn f(side: Side) -> Int64\n\
        \  requires side == Side.Left(value: 3) || side == Side.Right(value: 3)\n\
        \  ensures result == 3\n\
         {\n\
        \  match side {\n\
        \    Left(value) | Right(value) => value\n\
        \  }\n\
         }\n")

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

(* Incremental work: after an edit, which definitions are proven again,
   and how many queries reach the solver rather than its cache. Each test's
   definitions are its own, so no other test has solved its queries. *)

let again before after =
  let solver =
    match Solver.find () with Ok solver -> solver | Error message -> failwith message
  in
  let database = Support.setup [ ("app::main", before) ] in
  let module_ = Support.module_of "app::main" in
  let engine = Engine.of_context database in
  let prove () =
    match Type_checker.diagnostics database module_ with
    | [] -> Prover.diagnostics database solver module_
    | errors -> errors
  in
  (match prove () with
  | [] -> ()
  | found -> fail "before the edit: %s" (String.concat "; " (Support.codes found)));
  Engine.set engine Workspace.file_text module_ after;
  Engine.clear_log engine;
  let solved = Solver.solved solver in
  (match prove () with
  | [] -> ()
  | found -> fail "after the edit: %s" (String.concat "; " (Support.codes found)));
  let prefix = "proof(app::main::" in
  let proven =
    List.filter_map
      (fun name ->
        let length = String.length prefix in
        if String.length name > length && String.sub name 0 length = prefix then
          Some (String.sub name length (String.length name - length - 1))
        else None)
      (Engine.executed engine)
  in
  (List.sort_uniq compare proven, Solver.solved solver - solved)

let expect_again before after ~proven ~solved =
  let found, count = again before after in
  if found <> proven || count <> solved then
    fail "proven again: [%s], with %d queries solved; expected [%s], with %d"
      (String.concat ", " found) count (String.concat ", " proven) solved

let () =
  test "editing a body proves that definition again and no other" (fun () ->
      let text index =
        Printf.sprintf
          "fn last_reading(readings: List[Int32]) -> Int32\n\
          \  requires readings.length() > 2\n\
           {\n\
          \  readings[%s]\n\
           }\n\n\
           fn next_reading(reading: UInt16) -> UInt16\n\
          \  requires reading < 900\n\
           {\n\
          \  reading + 7\n\
           }\n"
          index
      in
      expect_again (text "1") (text "2") ~proven:[ "last_reading" ] ~solved:1);
  test "renaming a local solves nothing again" (fun () ->
      let text name =
        Printf.sprintf
          "fn first_sample(samples: List[Int16]) -> Int16\n\
          \  requires samples.length() > 0\n\
           {\n\
          \  let %s = samples[0]\n\
          \  %s\n\
           }\n"
          name name
      in
      expect_again (text "first") (text "head") ~proven:[ "first_sample" ] ~solved:0);
  test "editing a callee's ensures proves its callers again" (fun () ->
      let text ensures =
        Printf.sprintf
          "fn halve(amount: UInt32) -> UInt32\n\
          \  ensures %s\n\
           {\n\
          \  amount / 2\n\
           }\n\n\
           fn halve_and_add(amount: UInt32) -> UInt32 {\n\
          \  halve(amount) + 1\n\
           }\n\n\
           fn unrelated(level: UInt32) -> UInt32\n\
          \  requires level < 10\n\
           {\n\
          \  level + 1\n\
           }\n"
          ensures
      in
      expect_again (text "result < 4000000000") (text "result <= amount / 2")
        ~proven:[ "halve"; "halve_and_add" ] ~solved:2)

let () = finish ()
