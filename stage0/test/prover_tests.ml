(* The prover, against the pinned solver. Each test gives a few small
   definitions and states which obligation is proven or is not. *)

open Harness

let solver =
  match Solver.find () with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

let check database module_ =
  match Type_checker.diagnostics database module_ with
  | [] -> Prover.diagnostics ~record:(Support.record database) database solver module_
  | errors -> errors

let proven text = Support.no_diagnostics ~check [ ("app::main", text) ]
let not_proven text code = Support.one_diagnostic ~check text code

(* The codes of a file's diagnostics. *)
let codes text =
  let database = Support.setup [ ("app::main", text) ] in
  Support.codes (check database (Support.module_of "app::main"))

(* A file with diagnostics, all of one code, as a cycle of the call graph
   gives at each call in it. *)
let only_code text code =
  match codes text with
  | [] -> fail "no diagnostics"
  | found ->
      if List.exists (fun other -> other <> code) found then fail "%s" (String.concat ", " found)

(* The message of a file's one diagnostic. *)
let message text =
  let database = Support.setup [ ("app::main", text) ] in
  match check database (Support.module_of "app::main") with
  | [ diagnostic ] -> diagnostic.message
  | found ->
      Printf.sprintf "%d diagnostics: %s" (List.length found)
        (String.concat "; " (Support.codes found))

let contains = Substring.contains

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
      only_code
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
  test "a mut argument that is a field leaves the rest of its value as it was" (fun () ->
      proven
        "type Point(x: Int64, y: Int64)\n\n\
         fn bump(value: mut Int64)\n\
        \  requires value < 100\n\
        \  ensures value == old(value) + 1\n\
         {\n\
        \  value += 1\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result == 4\n\
         {\n\
        \  var point = Point(x: 1, y: 2)\n\
        \  bump(mut point.x)\n\
        \  point.x + point.y\n\
         }\n");
  test "a mut argument that is a field is known only by what the callee promises" (fun () ->
      not_proven
        "type Point(x: Int64, y: Int64)\n\n\
         fn reset(value: mut Int64) {\n\
        \  value = 0\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result == 0\n\
         {\n\
        \  var point = Point(x: 1, y: 2)\n\
        \  reset(mut point.x)\n\
        \  point.x\n\
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
  let tagged ensures =
    "type Pair(first: Int64, second: Int64)\n\n\
     type Tagged(tag: Int64, value: Int64)\n\n\
     fn Pair.tagged(mut self) lends mut Tagged\n" ^ ensures
    ^ "{\n  yield Tagged(tag: 0, value: mut self.second)\n}\n"
  in
  test "a constructor lent `mut` leaves the places it does not lend" (fun () ->
      proven (tagged "  ensures self.first == old(self.first)\n"));
  test "a constructor lent `mut` stores the caller's change in the place it lends" (fun () ->
      not_proven (tagged "  ensures self.second == old(self.second)\n") "prover.ensures");
  test "a variant lent `mut` stores back only into the place it lends" (fun () ->
      let maybe ensures =
        "type Pair(first: Int64, second: Int64)\n\n\
         fn Pair.maybe(mut self) lends mut Option[Int64]\n" ^ ensures
        ^ "{\n  yield Some(mut self.second)\n}\n"
      in
      proven (maybe "  ensures self.first == old(self.first)\n");
      not_proven (maybe "  ensures self.second == old(self.second)\n") "prover.ensures");
  test "a caller of a constructor lent `mut` keeps what the method's contract says" (fun () ->
      proven
        (tagged "  ensures self.first == old(self.first)\n"
        ^ "\n\
           fn f(pair: mut Pair)\n\
          \  requires pair.first == 1\n\
          \  ensures pair.first == 1\n\
           {\n\
          \  mut pair.tagged().value = 2\n\
           }\n"));
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
  test "a loop over a cursor in a field calls its next" (fun () ->
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
         type Timer(countdown: Countdown, ticks: UInt8)\n\n\
         fn f(timer: mut Timer) -> UInt8\n\
        \  ensures timer.ticks == old(timer.ticks)\n\
        \  cost time finite\n\
         {\n\
        \  var last: UInt8 = 0\n\
        \  for value in timer.countdown\n\
        \    invariant timer.ticks == old(timer.ticks)\n\
        \    decreases timer.countdown.left\n\
        \  {\n\
        \    last = value\n\
        \  }\n\
        \  last\n\
         }\n");
  test "a later arm sees what an earlier arm's guard changed" (fun () ->
      proven
        "fn bump(count: mut Int64) -> Bool\n\
        \  requires count < 100\n\
        \  ensures count == old(count) + 1\n\
        \  ensures !result\n\
        \  cost time O(1)\n\
         {\n\
        \  count += 1\n\
        \  false\n\
         }\n\n\
         fn f(value: Int64) -> Int64\n\
        \  ensures value == 1 ==> result == 1\n\
        \  ensures value != 1 ==> result == 0\n\
         {\n\
        \  var count: Int64 = 0\n\
        \  match value {\n\
        \    1 if bump(mut count) => 5\n\
        \    _ => count\n\
        \  }\n\
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
  test "an array literal has its elements" (fun () ->
      proven
        "fn f() -> Int64\n\
        \  ensures result == 2\n\
         {\n\
        \  let numbers: Array[Int64, 3] = [1, 2, 3]\n\
        \  numbers[1]\n\
         }\n");
  test "an index below an array's count is within it" (fun () ->
      proven "fn f(numbers: Array[Int64, 4]) -> Int64 {\n  numbers[3]\n}\n");
  test "an index at an array's count is not" (fun () ->
      not_proven "fn f(numbers: Array[Int64, 4]) -> Int64 {\n  numbers[4]\n}\n" "prover.requires");
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
        (shout ^ "fn f(name: String) -> Shout {\n  Shout\"hey ${name.copy()}\"\n}\n")
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
      not_proven "fn f() -> Map[Int64, Int64] {\n  [1: 2, 1: 3]\n}\n" "prover.requires");
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
  test "an implementation of a capability keeps the capability's contract" (fun () ->
      not_proven
        (dice
       ^ "type Loaded()\n\nimpl Dice for Loaded {\n  fn roll(self) -> UInt8 {\n    9\n  }\n}\n")
        "prover.ensures");
  test "a capability's broken contract is named as the capability's" (fun () ->
      let found =
        message
          (dice
         ^ "type Loaded()\n\nimpl Dice for Loaded {\n  fn roll(self) -> UInt8 {\n    9\n  }\n}\n")
      in
      if not (contains found "The capability's `result >= 1 && result <= 6`") then
        fail "found: %s" found);
  test "an implementation of a capability that keeps its contract proves" (fun () ->
      proven
        (dice
       ^ "type Fair(face: UInt8)\n\
         \  invariant face >= 1 && face <= 6\n\n\
          impl Dice for Fair {\n\
         \  fn roll(self) -> UInt8 {\n\
         \    self.face\n\
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
  test "a list's potential is its elements', through its model" (fun () ->
      proven (meter ^ "fn keep(meters: mut List[Meter])\n  cost amortized time O(1)\n{\n}\n"));
  let encoder = "type Encoder(bytes: List[UInt8])\n\n" in
  test "a record with no potential clause holds its parts'" (fun () ->
      proven
        (encoder
       ^ "fn Encoder.uint8(mut self, value: UInt8)\n\
         \  cost amortized time O(1)\n\
          {\n\
         \  mut self.bytes.push(value)\n\
          }\n"));
  test "a loop that pushes into a record's list is amortized linear" (fun () ->
      proven
        (encoder
       ^ "fn Encoder.bytes(mut self, bytes: Slice[UInt8])\n\
         \  cost amortized time O(bytes.length())\n\
          {\n\
         \  for index in 0..bytes.length() {\n\
         \    mut self.bytes.push(bytes[index])\n\
         \  }\n\
          }\n"));
  let bag =
    "type Bag[Value](first: Value, second: Value)\n\n\
     fn Bag[Value].first(mut self) lends mut Value\n\
    \  cost amortized time O(1)\n\
     {\n\
    \  yield mut self.first\n\
     }\n\n"
  in
  test "a method that lends a part mut does not pay for what is done to it" (fun () -> proven bag);
  test "a caller that raises a lent part's potential pays for it" (fun () ->
      let found =
        codes
          (meter ^ bag
         ^ "fn raise(bag: mut Bag[Meter], credit: UInt32)\n\
           \  cost amortized time O(1)\n\
            {\n\
           \  mut bag.first().credit = credit\n\
            }\n")
      in
      if found <> [ "prover.cost" ] then fail "%s" (String.concat ", " found));
  test "a caller that lowers a lent part's potential is paid by it" (fun () ->
      proven
        (meter ^ bag
       ^ "fn spent(bag: mut Bag[Meter])\n\
         \  cost amortized time O(1)\n\
          {\n\
         \  mut bag.first().credit = 0\n\
          }\n"));
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
  test "a contract on a body that is not written waits for it, and is no hole" (fun () ->
      let text = "fn f(value: Int64) -> Int64\n  ensures result > value\n{\n  todo\n}\n" in
      proven text;
      if holes text <> 0 then fail "%d holes" (holes text));
  test "what is before a todo in code is still proven" (fun () ->
      not_proven
        "fn f(items: List[Int64], index: USize) -> Int64\n\
        \  ensures result > 0\n\
         {\n\
        \  let first = items[index]\n\
        \  first + todo\n\
         }\n"
        "prover.requires");
  test "an impl's laws wait while one of its methods is not written" (fun () ->
      proven
        "type Meters(value: Int64)\n\n\
         impl Equal for Meters {\n\
        \  fn equal(self, other: Meters) -> Bool {\n\
        \    todo\n\
        \  }\n\
         }\n");
  test "a type that contains itself through a map's values is read" (fun () ->
      proven
        "type Tree =\n\
        \  | Leaf\n\
        \  | Branch(children: Map[String, Tree])\n\n\
         fn is_leaf(tree: Tree) -> Bool {\n\
        \  tree is Leaf\n\
         }\n")

(* Code that does not run *)

let () =
  test "a lambda's result is in range only for arguments in range" (fun () ->
      not_proven
        "fn f() -> Int64\n\
        \  ensures result == 1\n\
         {\n\
        \  let same: (fn(Int64) -> Int64 cost time finite) = fn(x) { x }\n\
        \  same(0)\n\
         }\n"
        "prover.ensures");
  test "a proof block's assignments do not reach the program" (fun () ->
      not_proven
        "fn f() -> Int64\n\
        \  ensures result == 5\n\
         {\n\
        \  var x: Int64 = 0\n\
        \  proof {\n\
        \    x = 5\n\
        \  }\n\
        \  x\n\
         }\n"
        "prover.ensures");
  test "a proof block's return does not end the program's path" (fun () ->
      not_proven
        "fn f(x: USize, divisor: USize) -> USize {\n\
        \  proof {\n\
        \    return 1\n\
        \  }\n\
        \  x / divisor\n\
         }\n"
        "prover.division");
  test "a proof block that never ends shows nothing" (fun () ->
      not_proven
        "fn f(x: Int64) -> Int64\n\
        \  ensures result == 0\n\
         {\n\
        \  proof {\n\
        \    while true {}\n\
        \  }\n\
        \  x\n\
         }\n"
        "prover.ensures");
  test "an uncalled lambda's calls show nothing of the path" (fun () ->
      not_proven
        "fn hang() -> Int64\n\
        \  ensures false\n\
         {\n\
        \  while true {}\n\
         }\n\n\
         fn f(x: Int64) -> Int64\n\
        \  ensures result <= 0\n\
         {\n\
        \  if x > 0 {\n\
        \    let _: fn() -> Int64 = fn() { hang() }\n\
        \  }\n\
        \  x\n\
         }\n"
        "prover.ensures");
  test "a lambda whose arguments cannot meet its requires shows nothing of the path" (fun () ->
      not_proven
        "fn each_index(count: USize, visit: (fn(index: USize) -> USize requires index < count)) -> \
         USize {\n\
        \  if count > 0 { visit(count - 1) } else { 0 }\n\
         }\n\n\
         fn f(x: Int64) -> Int64\n\
        \  ensures result <= 0\n\
         {\n\
        \  if x > 0 {\n\
        \    let _ = each_index(0, visit: fn(i) { i })\n\
        \  }\n\
        \  x\n\
         }\n"
        "prover.ensures");
  test "a quantifier over an empty range shows nothing of the path" (fun () ->
      not_proven
        "fn hang() -> Bool\n\
        \  ensures false\n\
         {\n\
        \  while true {}\n\
         }\n\n\
         fn f(x: Int64) -> Int64\n\
        \  ensures result <= 0\n\
         {\n\
        \  if x > 0 {\n\
        \    let _ = exists _ in 0..0 => hang()\n\
        \  }\n\
        \  x\n\
         }\n"
        "prover.ensures");
  test "a lambda over a type no value has shows nothing of the path" (fun () ->
      not_proven
        "type Empty(value: Int64)\n\
        \  invariant value > 0\n\
        \  invariant value < 0\n\n\
         fn ignore(visit: fn(Empty) -> Int64) -> Int64 {\n\
        \  0\n\
         }\n\n\
         fn f(x: Int64) -> Int64\n\
        \  ensures result <= 0\n\
         {\n\
        \  if x > 0 {\n\
        \    let _ = ignore(fn(e) { e.value })\n\
        \  }\n\
        \  x\n\
         }\n"
        "prover.ensures");
  test "a law's proof that never ends shows nothing" (fun () ->
      not_proven
        (monoid ^ flag_impl "true" ^ "\nproof Monoid.left_identity for Flag {\n  while true {}\n}\n")
        "prover.law");
  test "a todo in a law's proof is a hole that stands for the law" (fun () ->
      let text =
        monoid ^ flag_impl "true" ^ "\nproof Monoid.left_identity for Flag {\n  todo\n}\n"
      in
      proven text;
      if holes text <> 1 then fail "%d holes" (holes text))

(* What a caller assumes is what was shown *)

let () =
  test "a trait's ensures holds of an impl's method only where the trait's requires does" (fun () ->
      not_proven
        "trait Scaled {\n\
        \  fn scale(self, n: Int64) -> Int64\n\
        \    requires n > 0\n\
        \    ensures result > 0\n\
         }\n\n\
         type Box()\n\n\
         impl Scaled for Box {\n\
        \  fn scale(self, n: Int64) -> Int64\n\
        \    requires n >= 0\n\
        \  {\n\
        \    n\n\
        \  }\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result > 0\n\
         {\n\
        \  Box().scale(0)\n\
         }\n"
        "prover.ensures");
  test "a law of an unfinished impl is a hole where it is assumed" (fun () ->
      let text =
        "trait Sized {\n\
        \  fn measure(self) -> Int64\n\
        \    cost time finite\n\
        \  fn label(self) -> Int64\n\
        \    cost time finite\n\n\
        \  law positive(value: Self) { value.measure() > 0 }\n\
         }\n\n\
         type Box(size: Int64)\n\n\
         impl Sized for Box {\n\
        \  fn measure(self) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    self.size\n\
        \  }\n\n\
        \  fn label(self) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    todo\n\
        \  }\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result > 0\n\
         {\n\
        \  Box(size: 0).measure()\n\
         }\n"
      in
      if holes text <> 1 then fail "%d holes" (holes text));
  test "a law whose proof holds a todo is a hole where it is assumed" (fun () ->
      let text =
        "trait Zero {\n\
        \  fn zero(self) -> UInt8\n\
        \    cost time finite\n\n\
        \  law is_zero(value: Self) { value.zero() == 0 }\n\
         }\n\n\
         impl Zero for UInt8 {\n\
        \  fn zero(self) -> UInt8\n\
        \    cost time finite\n\
        \  {\n\
        \    self\n\
        \  }\n\
         }\n\n\
         proof Zero.is_zero for UInt8 {\n\
        \  todo\n\
         }\n\n\
         fn f(x: UInt8) -> UInt8\n\
        \  ensures result == 0\n\
         {\n\
        \  x.zero()\n\
         }\n"
      in
      if holes text <> 2 then fail "%d holes" (holes text));
  test "each impl of a trait with arguments keeps its own laws" (fun () ->
      not_proven
        "trait Scale[Factor] {\n\
        \  fn scale(self, by: Factor) -> Int64\n\
        \    cost time finite\n\n\
        \  law zero(value: Self, by: Factor) { value.scale(by) == 0 }\n\
         }\n\n\
         type Box()\n\n\
         impl Scale[Int64] for Box {\n\
        \  fn scale(self, by: Int64) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    0\n\
        \  }\n\
         }\n\n\
         impl Scale[Bool] for Box {\n\
        \  fn scale(self, by: Bool) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    1\n\
        \  }\n\
         }\n"
        "prover.law");
  test "an element changed through a lend meets its invariant when the lend ends" (fun () ->
      not_proven
        "type Span(low: Int64, high: Int64)\n\
        \  invariant low <= high\n\n\
         fn f() -> Int64\n\
        \  ensures result == 1\n\
         {\n\
        \  var spans: List[Span] = [Span(low: 0, high: 0)]\n\
        \  spans[0].low = 1\n\
        \  spans[0].high\n\
         }\n"
        "prover.invariant");
  test "an element changed through a lend that keeps its invariant proves" (fun () ->
      proven
        "type Span(low: Int64, high: Int64)\n\
        \  invariant low <= high\n\n\
         fn f() -> Int64\n\
        \  ensures result == 5\n\
         {\n\
        \  var spans: List[Span] = [Span(low: 0, high: 0)]\n\
        \  spans[0].high = 5\n\
        \  spans[0].high\n\
         }\n");
  test "a yielded part meets its invariant" (fun () ->
      not_proven
        "type Positive(n: Int64)\n\
        \  invariant n > 0\n\n\
         type Source()\n\n\
         fn Source.each(self) yields Positive {\n\
        \  var p = Positive(n: 1)\n\
        \  p.n = -5\n\
        \  yield p\n\
         }\n"
        "prover.invariant");
  test "a loop keeps the validity of each value it changes" (fun () ->
      proven
        "type Positive(n: Int64)\n\
        \  invariant n > 0\n\n\
         fn take(item: Positive) -> Int64 {\n\
        \  item.n\n\
         }\n\n\
         fn f(count: USize) -> Int64 {\n\
        \  var item = Positive(n: 1)\n\
        \  for _ in 0..count {\n\
        \    item.n = 0\n\
        \    item.n = 5\n\
        \  }\n\
        \  take(item)\n\
         }\n");
  test "an iteration must keep the validity of each value the loop changes" (fun () ->
      not_proven
        "type Positive(n: Int64)\n\
        \  invariant n > 0\n\n\
         fn take(item: Positive) -> Int64 {\n\
        \  item.n\n\
         }\n\n\
         fn f(count: USize) -> Int64 {\n\
        \  var item = Positive(n: 2)\n\
        \  for _ in 0..count {\n\
        \    item.n = 0\n\
        \  }\n\
        \  1\n\
         }\n"
        "prover.invariant")

(* Each expression runs once, and its changes are kept *)

let () =
  test "a guessed measure is not read from a condition with a mut argument" (fun () ->
      not_proven
        "fn take(count: mut Int64) -> Int64\n\
        \  requires count > -1000\n\
        \  ensures count == old(count) - 1\n\
        \  ensures result == old(count)\n\
        \  cost time O(1)\n\
         {\n\
        \  count -= 1\n\
        \  count + 1\n\
         }\n\n\
         fn f()\n\
        \  cost time finite\n\
         {\n\
        \  var i: Int64 = 0\n\
        \  while take(mut i) < 10\n\
        \    invariant i > -100\n\
        \  {\n\
        \    i += 1\n\
        \  }\n\
         }\n"
        "prover.termination");
  test "a mut slice's bounds are evaluated once" (fun () ->
      not_proven
        "fn set(items: mut Slice[Int64])\n\
        \  requires items.length() >= 1\n\
        \  ensures items[0] == 7\n\
         {\n\
        \  items[0] = 7\n\
         }\n\n\
         fn f(items: mut List[Int64])\n\
        \  requires items.length() >= 4\n\
        \  ensures items[1] == old(items[1])\n\
         {\n\
        \  var k: USize = 0\n\
        \  set(mut items[{\n\
        \    k += 1\n\
        \    k\n\
        \  }..3])\n\
         }\n"
        "prover.ensures");
  test "a while condition's mut argument changes the loop's state" (fun () ->
      not_proven
        "fn step(count: mut Int64) -> Bool {\n\
        \  count = count.saturating_add(1)\n\
        \  count < 3\n\
         }\n\n\
         fn f() -> Int64\n\
        \  ensures result == 0\n\
         {\n\
        \  var value: Int64 = 0\n\
        \  while step(mut value) {}\n\
        \  value\n\
         }\n"
        "prover.ensures");
  test "a match mut binding is written back to the scrutinee" (fun () ->
      not_proven
        "fn f() -> Int64\n\
        \  ensures result == 1\n\
         {\n\
        \  var option: Option[Int64] = Some(1)\n\
        \  match mut option {\n\
        \    Some(value) => { value = 5 }\n\
        \    None => {}\n\
        \  }\n\
        \  option.unwrap_or(0)\n\
         }\n"
        "prover.ensures");
  test "a while condition's cost is the iteration's" (fun () ->
      not_proven
        "capability Hits {\n\
        \  fn hit()\n\
        \    cost time finite\n\
         }\n\n\
         type Counter(count: Int64)\n\n\
         impl Hits for Counter {\n\
        \  fn hit(mut self) {\n\
        \    self.count = self.count.saturating_add(1)\n\
        \  }\n\
         }\n\n\
         fn f(count: UInt32, visit: (fn() -> Bool uses Hits cost time finite))\n\
        \  uses Hits\n\
        \  cost calls(visit) <= 1\n\
         {\n\
        \  var index: UInt32 = 0\n\
        \  while index < count && visit()\n\
        \    invariant index <= count\n\
        \    decreases count - index\n\
        \  {\n\
        \    index = index + 1\n\
        \  }\n\
         }\n"
        "prover.cost");
  test "the right operand of || spends what it spends" (fun () ->
      not_proven
        "capability Hits {\n\
        \  fn hit()\n\
        \    cost time finite\n\
         }\n\n\
         type Counter(count: Int64)\n\n\
         impl Hits for Counter {\n\
        \  fn hit(mut self) {\n\
        \    self.count = self.count.saturating_add(1)\n\
        \  }\n\
         }\n\n\
         fn f(flag: Bool, visit: (fn() -> Bool uses Hits cost time finite)) -> Bool\n\
        \  uses Hits\n\
        \  cost calls(visit) == 0\n\
         {\n\
        \  flag || visit()\n\
         }\n"
        "prover.cost");
  test "a call through an alias of a function value counts as a call of it" (fun () ->
      not_proven
        "capability Hits {\n\
        \  fn hit()\n\
        \    cost time finite\n\
         }\n\n\
         type Counter(count: Int64)\n\n\
         impl Hits for Counter {\n\
        \  fn hit(mut self) {\n\
        \    self.count = self.count.saturating_add(1)\n\
        \  }\n\
         }\n\n\
         fn f(flag: Bool, visit: (fn() uses Hits cost time finite), other: (fn() uses Hits cost \
         time finite))\n\
        \  uses Hits\n\
        \  cost calls(visit) == 0\n\
         {\n\
        \  let g = if flag { visit } else { other }\n\
        \  g()\n\
         }\n"
        "prover.cost");
  test "a match mut binding's new value is in the scrutinee after the arm" (fun () ->
      proven
        "fn f() -> Int64\n\
        \  ensures result == 5\n\
         {\n\
        \  var option: Option[Int64] = Some(1)\n\
        \  match mut option {\n\
        \    Some(value) => { value = 5 }\n\
        \    None => {}\n\
        \  }\n\
        \  option.unwrap_or(0)\n\
         }\n")

(* A function value's requires *)

let () =
  test "a function with a requires bound to a local must accept every argument" (fun () ->
      not_proven
        "fn below_three(index: USize) -> USize\n\
        \  requires index < 3\n\
         {\n\
        \  index\n\
         }\n\n\
         fn f() -> USize {\n\
        \  let g = below_three\n\
        \  g(5)\n\
         }\n"
        "prover.requires");
  test "a function with a requires passed through a local must accept every argument" (fun () ->
      not_proven
        "fn below_one(index: Int64) -> Int64\n\
        \  requires index < 1\n\
         {\n\
        \  index\n\
         }\n\n\
         fn call(visit: (fn(index: Int64) -> Int64 requires index < 2)) -> Int64 {\n\
        \  visit(1)\n\
         }\n\n\
         fn f() -> Int64 {\n\
        \  let g: fn(Int64) -> Int64 = below_one\n\
        \  call(visit: g)\n\
         }\n"
        "prover.requires");
  test "a callback's requires names a mut parameter as the caller passed it" (fun () ->
      not_proven
        "fn grow(limit: mut USize, visit: (fn(index: USize) -> Int64 requires index < limit)) -> \
         Int64 {\n\
        \  if limit < 100 { limit = limit + 1 }\n\
        \  visit(limit - 1)\n\
         }\n\n\
         fn f(items: List[Int64]) -> Int64 {\n\
        \  var n: USize = 0\n\
        \  grow(mut n, visit: fn(i) { items[i] })\n\
         }\n"
        "prover.requires");
  test "a forwarded callback must be promised what it requires" (fun () ->
      not_proven
        "fn call(visit: (fn(index: Int64) -> Int64 requires index < 2)) -> Int64 {\n\
        \  visit(1)\n\
         }\n\n\
         fn forward(visit: (fn(index: Int64) -> Int64 requires index < 1)) -> Int64 {\n\
        \  call(visit: visit)\n\
         }\n"
        "prover.requires");
  test "a call through a function value gives a valid result" (fun () ->
      proven
        "type Positive(n: Int64)\n\
        \  invariant n > 0\n\n\
         fn take(make: fn() -> Positive) -> Int64\n\
        \  ensures result > 0\n\
         {\n\
        \  make().n\n\
         }\n");
  test "a lambda returns a valid value" (fun () ->
      not_proven
        "type Positive(n: Int64)\n\
        \  invariant n > 0\n\n\
         fn apply(change: fn(Positive) -> Positive, value: Positive) -> Positive {\n\
        \  change(value)\n\
         }\n\n\
         fn f() -> Positive {\n\
        \  apply(fn(p) {\n\
        \    var q = p\n\
        \    q.n = 0\n\
        \    q\n\
        \  }, value: Positive(n: 1))\n\
         }\n"
        "prover.invariant");
  test "a callback with a requires bound to a local must accept every argument" (fun () ->
      not_proven
        "fn keep(visit: (fn(index: Int64) -> Int64 requires index < 1)) -> Int64 {\n\
        \  let g: fn(Int64) -> Int64 = visit\n\
        \  g(5)\n\
         }\n"
        "prover.requires")

(* Recursion through traits *)

let () =
  test "provided methods that call each other are recursion" (fun () ->
      only_code
        "trait Ping {\n\
        \  fn ping(self) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    self.pong()\n\
        \  }\n\n\
        \  fn pong(self) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    self.ping()\n\
        \  }\n\
         }\n\n\
         type Foo()\n\n\
         impl Ping for Foo {}\n"
        "prover.termination");
  test "a call through any that reaches back is recursion" (fun () ->
      only_code
        "trait Step {\n\
        \  fn step(own self) -> Int64\n\
        \    cost time finite\n\
         }\n\n\
         fn run(value: own any Step) -> Int64\n\
        \  cost time finite\n\
         {\n\
        \  own value.step()\n\
         }\n\n\
         type Foo()\n\n\
         impl Step for Foo {\n\
        \  fn step(own self) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    let value: any Step = any self\n\
        \    run(own value)\n\
        \  }\n\
         }\n"
        "prover.termination");
  test "a method that calls itself through any is recursion" (fun () ->
      not_proven
        "trait Check {\n\
        \  fn check(self) -> Bool\n\
        \    cost time finite\n\
         }\n\n\
         type Loop()\n\n\
         impl Check for Loop {\n\
        \  fn check(self) -> Bool\n\
        \    cost time finite\n\
        \  {\n\
        \    let other: any Check = any Loop()\n\
        \    !other.check()\n\
        \  }\n\
         }\n\n\
         fn f() -> Bool\n\
        \  cost time finite\n\
         {\n\
        \  Loop().check()\n\
         }\n"
        "prover.termination")

(* Constants *)

let () =
  test "a constant's value is well defined" (fun () ->
      not_proven "let shifted: UInt8 = 1 << 8\n" "prover.shift");
  test "a constant whose value is in range proves" (fun () ->
      proven "let shifted: UInt8 = 1 << 7\n")

(* Integer operations of the intrinsic module *)

let () =
  test "generic negation needs what the trait requires" (fun () ->
      not_proven "fn negate[Number: Negate](value: Number) -> Number.Output {\n  -value\n}\n"
        "prover.requires");
  test "generic negation proves where what the trait requires holds" (fun () ->
      proven
        "fn negate[Number: Negate](value: Number) -> Number.Output\n\
        \  requires value.negate_is_defined()\n\
         {\n\
        \  -value\n\
         }\n")

(* Text literals *)

let () =
  test "two literals with the same text are the same value" (fun () ->
      proven "fn f() -> String\n  ensures identical(result, \"a\")\n{\n  \"a\"\n}\n");
  test "two literals with different text are different values" (fun () ->
      not_proven "fn f() -> String\n  ensures identical(result, \"b\")\n{\n  \"a\"\n}\n"
        "prover.ensures");
  test "a map built with a literal key contains the same literal" (fun () ->
      proven
        "fn built() -> Map[String, Int64]\n\
        \  ensures result.contains(\"a\")\n\
         {\n\
        \  var made: Map[String, Int64] = [:]\n\
        \  mut made.insert(\"a\", value: 1)\n\
        \  made\n\
         }\n")

(* Bitwise operations *)

let () =
  test "a bit set below a symbolic width keeps the bits above it clear" (fun () ->
      proven
        "theorem a_written_bit_keeps_the_unused_bits_clear(word: UInt64, used: USize, position: \
         USize)\n\
        \  requires used < 64\n\
        \  requires position < used\n\
        \  requires (word >> used) == 0\n\
        \  ensures ((word ^ (1 << position)) >> used) == 0\n\
        \  ensures ((word | (1 << position)) >> used) == 0\n\
         {\n\
         }\n\n\
         theorem a_union_keeps_the_unused_bits_clear(first: UInt64, second: UInt64, used: USize)\n\
        \  requires used < 64\n\
        \  requires (first >> used) == 0\n\
        \  requires (second >> used) == 0\n\
        \  ensures ((first | second) >> used) == 0\n\
         {\n\
         }\n");
  test "an exclusive or may be below its first operand" (fun () ->
      not_proven
        "theorem at_least_the_first(first: UInt64, second: UInt64)\n\
        \  ensures (first ^ second) >= first\n\
         {\n\
         }\n"
        "prover.ensures")

(* Derived implementations *)

let () =
  test "a derived ordering is the one a law of another trait reads" (fun () ->
      proven
        "use standard::core\n\n\
         type Day(count: Int32)\n\
        \  derives Equal, Ordered\n\n\
         impl core::Countable for Day {\n\
        \  fn successor(self) -> Option[Day]\n\
        \    cost time O(1)\n\
        \  {\n\
        \    self.advanced(1)\n\
        \  }\n\n\
        \  fn predecessor(self) -> Option[Day]\n\
        \    cost time O(1)\n\
        \  {\n\
        \    self.retreated(1)\n\
        \  }\n\n\
        \  fn advanced(self, by: USize) -> Option[Day]\n\
        \    cost time O(1)\n\
        \  {\n\
        \    match self.count.advanced(by: by) {\n\
        \      Some(count) => Some(Day(count: count))\n\
        \      None => None\n\
        \    }\n\
        \  }\n\n\
        \  fn retreated(self, by: USize) -> Option[Day]\n\
        \    cost time O(1)\n\
        \  {\n\
        \    match self.count.retreated(by: by) {\n\
        \      Some(count) => Some(Day(count: count))\n\
        \      None => None\n\
        \    }\n\
        \  }\n\n\
        \  fn steps_to(self, other: Day) -> Option[USize]\n\
        \    cost time O(1)\n\
        \  {\n\
        \    self.count.steps_to(other.count)\n\
        \  }\n\
         }\n")

(* Equality through written impls *)

let () =
  test "a derived equality compares a list field as the list's equal does" (fun () ->
      proven
        "type Limbs(limbs: List[UInt64])\n\
        \  derives Equal\n\n\
         theorem the_same_limbs(first: Limbs, second: Limbs)\n\
        \  requires first.limbs == second.limbs\n\
        \  ensures first == second\n\
         {\n\
         }\n");
  test "a law reads an impl of Equal whose bounds hold in the impl it is proven for" (fun () ->
      proven
        "trait Named: Equal {\n\
        \  fn name(self) -> List[UInt64]\n\
        \    cost time finite\n\n\
        \  law named_by_its_name(first: Self, second: Self) {\n\
        \    (first.name() == second.name()) == (first == second)\n\
        \  }\n\
         }\n\n\
         type Wrapped[Item](items: List[Item], name: List[UInt64])\n\n\
         impl Equal for Wrapped[Item: Equal] {\n\
        \  fn equal(self, other: Wrapped[Item]) -> Bool {\n\
        \    self.name == other.name\n\
        \  }\n\
         }\n\n\
         impl Named for Wrapped[Item: Equal] {\n\
        \  fn name(self) -> List[UInt64]\n\
        \    cost time finite\n\
        \  {\n\
        \    self.name.copy()\n\
        \  }\n\
         }\n")

(* Amortized moves and copies *)

let () =
  test "a deque's potential pays for moving half of one list to the other" (fun () ->
      proven
        "type Deque[Element](front: List[Element], back: List[Element])\n\
        \  invariant front.length() <= USize.maximum - back.length()\n\
        \  cost potential if front.length() > back.length() { 8 * (front.length() - back.length()) \
         } else { 8 * (back.length() - front.length()) }\n\n\
         fn Deque[Element].pop_front(mut self) -> Option[Element]\n\
        \  cost amortized time O(1)\n\
         {\n\
        \  if self.front.is_empty() && !self.back.is_empty() {\n\
        \    let half = self.back.length() - self.back.length() / 2\n\
        \    var later = mut self.back.split_off(half)\n\
        \    mut self.back.reverse()\n\
        \    let earlier = mut self.back.split_off(0)\n\
        \    mut self.front.append(own earlier)\n\
        \    mut self.back.append(own later)\n\
        \  }\n\
        \  mut self.front.pop()\n\
         }\n");
  test "a copy pays for the potential it makes" (fun () ->
      proven
        "fn push_copy[Element: Copyable](list: mut List[Element], item: Element)\n\
        \  cost amortized time O(1 + time(Element.copy))\n\
         {\n\
        \  mut list.push(item.copy())\n\
         }\n");
  test "a loop of pushed copies is amortized over the copies' time" (fun () ->
      proven
        "fn append_copies[Element: Copyable](list: mut List[Element], items: Slice[Element])\n\
        \  cost amortized time O(items.length() * (1 + time(Element.copy)))\n\
         {\n\
        \  for item in items {\n\
        \    mut list.push(item.copy())\n\
        \  }\n\
         }\n")

(* Bodies across packages *)

(* The diagnostics of [app::main], in a package that depends on [lib], whose
   one module is [lib::numbers]. *)
let across library program =
  let database = Engine.context (Engine.create ()) in
  Database.load_standard (Engine.of_context database);
  Database.load_package (Engine.of_context database) ~name:{ owner = None; name = "lib" }
    ~dependencies:[]
    [ (Support.module_of "lib::numbers", library) ];
  Database.load_package (Engine.of_context database) ~name:{ owner = None; name = "app" }
    ~dependencies:[ { package = { owner = None; name = "lib" }; capabilities = [] } ]
    [ (Support.module_of "app::main", "use lib::numbers\n\n" ^ program) ];
  check database (Support.module_of "app::main")

let doubling marker =
  "public " ^ marker
  ^ "fn double(n: Int64) -> Int64\n\
    \  requires n < 1000 && n > -1000\n\
    \  cost time O(1)\n\
     {\n\
    \  n * 2\n\
     }\n"

let () =
  test "a caller in another package reads a transparent function's body" (fun () ->
      match
        across (doubling "transparent ")
          "fn twice(n: Int64) -> Int64\n\
          \  requires n < 1000 && n > -1000\n\
          \  ensures result == n + n\n\
           {\n\
          \  numbers::double(n)\n\
           }\n"
      with
      | [] -> ()
      | found ->
          fail "%s" (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found)));
  test "a caller in another package does not read a body that is not transparent" (fun () ->
      match
        across (doubling "")
          "fn twice(n: Int64) -> Int64\n\
          \  requires n < 1000 && n > -1000\n\
          \  ensures result == n + n\n\
           {\n\
          \  numbers::double(n)\n\
           }\n"
      with
      | [ diagnostic ] ->
          if not (contains diagnostic.message "is not visible in this package") then
            fail "message %S" diagnostic.message
      | found -> fail "%d diagnostics" (List.length found));
  test "a call in another package is not run unless its function is transparent" (fun () ->
      match
        across (doubling "")
          "fn eight() -> Int64\n  ensures result == 8\n{\n  numbers::double(4)\n}\n"
      with
      | [ _ ] -> ()
      | found -> fail "%d diagnostics" (List.length found))
(* Plain and amortized bounds together *)

let () =
  test "a recursive function proves a plain and an amortized bound, each by its own counting"
    (fun () ->
      proven
        "fn shift_left_all(items: mut List[Int64], position: USize)\n\
        \  requires position <= items.length()\n\
        \  ensures items.length() == old(items.length())\n\
        \  decreases position\n\
        \  cost time O(position)\n\
        \  cost amortized time O(position)\n\
         {\n\
        \  if position >= 2 {\n\
        \    mut items.swap(position - 1, second: position - 2)\n\
        \    shift_left_all(mut items, position: position - 1)\n\
        \  }\n\
         }\n")

(* Clauses in other files *)

let () =
  test "a callee's clause in another file is named by its file and line" (fun () ->
      let found = message "fn first(items: List[Int64]) -> Int64 {\n  items[0]\n}\n" in
      if not (contains found "The clause that must hold is at `standard/list.truss:") then
        fail "message %S" found)
(* Collections from another package *)

let () =
  test "an insertion into a set of integers is amortized in its length" (fun () ->
      proven
        "fn add(names: mut Set[Int64], name: Int64)\n\
        \  cost amortized time O(1 + names.length())\n\
         {\n\
        \  mut names.insert(name)\n\
         }\n");
  test "an insertion into a set of any elements is amortized in their comparisons" (fun () ->
      proven
        "fn add[Element: Hash + Ordered](names: mut Set[Element], name: own Element)\n\
        \  cost amortized time O(1 + names.length() * (1 + time(Element.equal)))\n\
         {\n\
        \  mut names.insert(own name)\n\
         }\n");
  test "a list filled with integers is linear in its count" (fun () ->
      proven
        "fn zeros(count: USize) -> List[UInt64]\n\
        \  cost time O(count)\n\
         {\n\
        \  List.filled(value: 0, count: count)\n\
         }\n")

(* Fixes *)

let () =
  test "a callee's requires about the caller's parameters is offered as the caller's" (fun () ->
      let database =
        Support.setup
          [
            ( "app::main",
              "fn halve(count: UInt32) -> UInt32\n\
              \  requires count < 100\n\
               {\n\
              \  count / 2\n\
               }\n\n\
               fn quarter(count: UInt32) -> UInt32 {\n\
              \  halve(count) / 2\n\
               }\n" );
          ]
      in
      match check database (Support.module_of "app::main") with
      | [ { fixes = [ { title; _ } ]; _ } ] when title = "Add `requires count < 100`" -> ()
      | found ->
          fail "%s"
            (String.concat "; "
               (List.map
                  (fun (d : Diagnostic.t) ->
                    String.concat ", " (List.map (fun (f : _ Diagnostic.fix) -> f.title) d.fixes))
                  found)))

(* Facts under a quantifier *)

let () =
  test "a fact made in a quantifier's body is a hypothesis of the goal" (fun () ->
      proven
        "fn counted(items: List[UInt32]) -> Bool\n\
        \  ensures forall i in 0..items.length() => items[i].count_ones() <= 32\n\
         {\n\
        \  true\n\
         }\n");
  test "a bitwise operation under a quantifier is defined for each bound value" (fun () ->
      proven
        "theorem low_byte(items: List[UInt32])\n\
        \  ensures forall i in 0..items.length() => (items[i] & 255) <= 255\n\
         {\n\
         }\n");
  test "a fact made in a quantifier's body proves nothing false" (fun () ->
      not_proven
        "fn counted(items: List[UInt32]) -> Bool\n\
        \  ensures forall i in 0..items.length() => items[i].count_ones() <= 31\n\
         {\n\
        \  true\n\
         }\n"
        "prover.ensures")

(* Contracts under a quantifier *)

let () =
  test "a callee's ensures under its requires holds for every bound value" (fun () ->
      proven
        "fn counted_up(count: USize) -> USize\n\
        \  requires count < 1000\n\
        \  ensures result == count\n\
        \  cost time O(count)\n\
         {\n\
        \  var reached: USize = 0\n\
        \  while reached < count\n\
        \    invariant reached <= count\n\
        \    decreases count - reached\n\
        \  {\n\
        \    reached += 1\n\
        \  }\n\
        \  reached\n\
         }\n\n\
         theorem each_counted(items: List[USize])\n\
        \  requires forall i in 0..items.length() => items[i] < 1000\n\
        \  ensures forall i in 0..items.length() => counted_up(items[i]) == items[i]\n\
         {\n\
         }\n")

(* Notes about hidden bodies *)

let () =
  test "a failure that seeing hidden bodies would not fix names none of them" (fun () ->
      let found = message "fn first(items: List[Int64]) -> Int64 {\n  items[0]\n}\n" in
      if contains found "is not visible in this package" then fail "message %S" found)

(* Early exits from concurrent loops *)

let () =
  test "a concurrent for may return early, with a value known by its type" (fun () ->
      proven
        "fn any_negative(numbers: List[Int64]) -> Bool\n\
        \  uses Tasks\n\
         {\n\
        \  concurrent for number in numbers {\n\
        \    if number < 0 {\n\
        \      return true\n\
        \    }\n\
        \  }\n\
        \  false\n\
         }\n");
  test "a value returned from a concurrent for is not known to be any one iteration's" (fun () ->
      not_proven
        "fn claimed(numbers: List[Int64]) -> Bool\n\
        \  uses Tasks\n\
        \  ensures !result\n\
         {\n\
        \  concurrent for number in numbers {\n\
        \    if number < 0 {\n\
        \      return true\n\
        \    }\n\
        \  }\n\
        \  false\n\
         }\n"
        "prover.ensures")

(* Overflow fixes *)

let () =
  let fix_titles text =
    let database = Support.setup [ ("app::main", text) ] in
    List.concat_map
      (fun (d : Diagnostic.t) -> List.map (fun (f : _ Diagnostic.fix) -> f.title) d.fixes)
      (check database (Support.module_of "app::main"))
  in
  test "a divisor that may be zero offers a requires that it is not" (fun () ->
      match
        fix_titles "fn halves(total: UInt32, parts: UInt32) -> UInt32 {\n  total / parts\n}\n"
      with
      | [ "Add `requires parts != 0`" ] -> ()
      | found -> fail "%s" (String.concat "; " found));
  test "a shift amount that may be too large offers a requires below the width" (fun () ->
      match fix_titles "fn shifted(value: UInt64, by: UInt64) -> UInt64 {\n  value << by\n}\n" with
      | [ "Add `requires by < 64`" ] -> ()
      | found -> fail "%s" (String.concat "; " found));
  test "an overflow with a literal offers the bound as a requires" (fun () ->
      let database =
        Support.setup [ ("app::main", "fn next(count: UInt8) -> UInt8 {\n  count + 1\n}\n") ]
      in
      match check database (Support.module_of "app::main") with
      | [ { fixes = [ { title; _ } ]; _ } ] when title = "Add `requires count <= 254`" -> ()
      | found ->
          fail "%s"
            (String.concat "; "
               (List.map
                  (fun (d : Diagnostic.t) ->
                    String.concat ", " (List.map (fun (f : _ Diagnostic.fix) -> f.title) d.fixes))
                  found)));
  test "a failed assert about the parameters offers it as a requires" (fun () ->
      match
        fix_titles
          "fn ordered(low: Int64, high: Int64) -> Int64 {\n\
          \  proof {\n\
          \    assert low < high\n\
          \  }\n\
          \  0\n\
           }\n"
      with
      | [ "Add `requires low < high`" ] -> ()
      | found -> fail "%s" (String.concat "; " found));
  test "a failed assert under an if offers the if's condition as a premise" (fun () ->
      match
        fix_titles
          "fn guarded(flag: Bool, count: Int64) -> Int64 {\n\
          \  if flag {\n\
          \    proof {\n\
          \      assert count > 0\n\
          \    }\n\
          \  }\n\
          \  0\n\
           }\n"
      with
      | [ "Add `requires (flag) ==> (count > 0)`" ] -> ()
      | found -> fail "%s" (String.concat "; " found));
  test "a failed assert with arithmetic offers it as a requires" (fun () ->
      match
        fix_titles
          "fn spaced(low: Int64, high: Int64) -> Int64 {\n\
          \  proof {\n\
          \    assert low + 2 * high <= 100 - (high - low)\n\
          \  }\n\
          \  0\n\
           }\n"
      with
      | [ "Add `requires low + 2 * high <= 100 - (high - low)`" ] -> ()
      | found -> fail "%s" (String.concat "; " found));
  test "an unsigned sum that may overflow offers only its upper bound" (fun () ->
      match fix_titles "fn total(count: UInt8, other: UInt8) -> UInt8 {\n  count + other\n}\n" with
      | [ "Add `requires count + other <= 255`" ] -> ()
      | found -> fail "%s" (String.concat "; " found));
  test "an unsigned difference that may overflow offers only its lower bound" (fun () ->
      match fix_titles "fn gap(low: UInt8, high: UInt8) -> UInt8 {\n  high - low\n}\n" with
      | [ "Add `requires 0 <= high - low`" ] -> ()
      | found -> fail "%s" (String.concat "; " found));
  test "a failed assert about a call's result offers no requires" (fun () ->
      let database =
        Support.setup
          [
            ( "app::main",
              "fn first(items: List[Int64]) -> Int64 {\n\
              \  proof {\n\
              \    assert items.length() > 0\n\
              \  }\n\
              \  0\n\
               }\n" );
          ]
      in
      match check database (Support.module_of "app::main") with
      | [ { code; fixes = []; _ } ] when Diagnostic.Code.name code = "prover.assertion" -> ()
      | found -> fail "%d diagnostics" (List.length found));
  test "an overflow names the fixes that change what the code means" (fun () ->
      let found = message "fn next(count: UInt8) -> UInt8 {\n  count + 1\n}\n" in
      if not (contains found "checked operation") then fail "message %S" found)

(* Counterexample paths *)

let () =
  test "a counterexample says which way each if on its path goes" (fun () ->
      let found =
        message
          "fn step(count: UInt8, up: Bool) -> UInt8 {\n\
          \  if up {\n\
          \    if count > 100 {\n\
          \      count + 200\n\
          \    } else {\n\
          \      count + 1\n\
          \    }\n\
          \  } else {\n\
          \    0\n\
          \  }\n\
           }\n"
      in
      if not (contains found "On that path, `up` is true, `count > 100` is true.") then
        fail "message %S" found);
  test "a counterexample says which arm of a match its path takes" (fun () ->
      let found =
        message
          "fn bump(found: Option[UInt8]) -> UInt8 {\n\
          \  match found {\n\
          \    Some(count) => count + 1\n\
          \    None => 0\n\
          \  }\n\
           }\n"
      in
      if not (contains found "On that path, the arm `Some(count)` is taken.") then
        fail "message %S" found)

(* Ranges under a quantifier *)

let () =
  test "a pure call's result is in its type's range for every bound value" (fun () ->
      proven
        "theorem each_in_range(items: List[Int64])\n\
        \  ensures forall i in 0..items.length() => items[i] <= Int64.maximum\n\
         {\n\
         }\n")

(* Lambdas under a quantifier *)

let () =
  test "a lambda in a quantifier that captures a bound value is known for each one" (fun () ->
      proven
        "fn apply(change: (fn(Bool) -> Bool cost time finite), value: Bool) -> Bool\n\
        \  ensures result == change(value)\n\
        \  cost time finite\n\
         {\n\
        \  change(value)\n\
         }\n\n\
         theorem each_captured(items: List[Bool])\n\
        \  ensures forall i in 0..items.length() =>\n\
        \    apply(fn(_) {\n\
        \      var kept = items[i]\n\
        \      kept\n\
        \    }, value: false) == items[i]\n\
         {\n\
         }\n");
  test "a lambda in a quantifier that captures no bound value is known for every argument"
    (fun () ->
      proven
        "fn apply(change: (fn(Bool) -> Bool cost time finite), value: Bool) -> Bool\n\
        \  ensures result == change(value)\n\
        \  cost time finite\n\
         {\n\
        \  change(value)\n\
         }\n\n\
         theorem each_kept(items: List[Bool])\n\
        \  ensures forall i in 0..items.length() =>\n\
        \    apply(fn(x) {\n\
        \      var kept = x\n\
        \      kept\n\
        \    }, value: items[i]) == items[i]\n\
         {\n\
         }\n")

(* Maps from another package *)

let () =
  test "an insertion into a map, of a new key or one it has, is amortized" (fun () ->
      proven
        "fn put(values: mut Map[Int64, Int64], key: Int64, value: Int64)\n\
        \  cost amortized time O(1 + values.length())\n\
         {\n\
        \  mut values.insert(key, value: value)\n\
         }\n")

(* Lambdas inside lambdas *)

let applying =
  "fn apply(change: (fn(Bool) -> Bool cost time finite), value: Bool) -> Bool\n\
  \  ensures result == change(value)\n\
  \  cost time finite\n\
   {\n\
  \  change(value)\n\
   }\n\n"

let () =
  test "a lambda with a functional lambda inside that captures nothing it made is known" (fun () ->
      proven
        (applying
       ^ "theorem passes_through(value: Bool)\n\
         \  ensures apply(fn(x) {\n\
         \      var kept = apply(fn(y) { y }, value: x)\n\
         \      kept\n\
         \    }, value: value) == value\n\
          {\n\
          }\n"));
  test "a lambda with a functional lambda inside that captures its argument is known" (fun () ->
      proven
        (applying
       ^ "theorem returns_its_argument(value: Bool)\n\
         \  ensures apply(fn(x) {\n\
         \      var kept = apply(fn(_) { x }, value: true)\n\
         \      kept\n\
         \    }, value: value) == value\n\
          {\n\
          }\n"));
  test "a functional lambda inside that captures the argument is not one function" (fun () ->
      not_proven
        (applying
       ^ "theorem wrongly_constant()\n\
         \  ensures apply(fn(x) {\n\
         \      var kept = apply(fn(_) { x }, value: true)\n\
         \      kept\n\
         \    }, value: true) == apply(fn(x) {\n\
         \      var kept = apply(fn(_) { x }, value: true)\n\
         \      kept\n\
         \    }, value: false)\n\
          {\n\
          }\n")
        "prover.ensures")

(* Definitions under a quantifier *)

let () =
  test "a definition with branches, called under a quantifier on no bound value, is unfolded"
    (fun () ->
      proven
        "fn used_bits(length: USize) -> UInt64\n\
        \  cost time O(1)\n\
         {\n\
        \  if length % 64 == 0 { UInt64.maximum } else { 5 }\n\
         }\n\n\
         theorem the_unused_words_hold_five(words: List[UInt64], length: USize)\n\
        \  requires length % 64 == 1\n\
        \  requires forall i in 0..words.length() =>\n\
        \    words[i] == (if i < length { 1 } else { used_bits(length) })\n\
        \  ensures forall i in 0..words.length() => i >= length ==> words[i] == 5\n\
         {\n\
         }\n");
  test "a derived ordering of a one-field record is its field's, for every value" (fun () ->
      proven
        "type Day(count: Int32)\n\
        \  derives Equal, Ordered\n\n\
         theorem days_order_as_their_counts()\n\
        \  ensures forall first: Day => forall second: Day =>\n\
        \    (first < second) == (first.count < second.count)\n\
         {\n\
         }\n");
  test "a derived ordering compares fields in order, for every value" (fun () ->
      proven
        "type Pair(first: Int64, second: Int64)\n\
        \  derives Equal, Ordered\n\n\
         theorem pairs_order_by_first_then_second()\n\
        \  ensures forall a: Pair => forall b: Pair =>\n\
        \    (a < b) == (a.first < b.first || (a.first == b.first && a.second < b.second))\n\
         {\n\
         }\n")

(* Counts of bits *)

let () =
  test "zero has no ones" (fun () ->
      proven
        "theorem t(word: UInt64)\n  requires word == 0\n  ensures word.count_ones() == 0\n{\n}\n");
  test "the ones of a value fit below its bit length" (fun () ->
      proven
        "theorem t(word: UInt64, bits: USize)\n\
        \  requires bits < 64\n\
        \  requires word < power(2, bits)\n\
        \  ensures word.count_ones() <= bits\n\
         {\n\
         }\n");
  test "the lowest one is below the bit length" (fun () ->
      proven
        "theorem t(word: UInt64, bits: USize)\n\
        \  requires bits <= 64\n\
        \  requires word != 0\n\
        \  requires bits == 64 || word < power(2, bits)\n\
        \  ensures word.trailing_zeros() < bits\n\
         {\n\
         }\n");
  test "every one below a power of two is counted" (fun () ->
      proven
        "theorem t(word: UInt64, bits: USize)\n\
        \  requires bits <= 64\n\
        \  requires bits > 0\n\
        \  requires word + 1 == power(2, bits)\n\
        \  ensures word.count_ones() == bits\n\
         {\n\
         }\n");
  test "a value may have ones" (fun () ->
      not_proven "theorem t(word: UInt64)\n  ensures word.count_ones() == 0\n{\n}\n"
        "prover.ensures")

(* Proofs of laws *)

let () =
  test "a proof for a generic impl names its own generic parameters" (fun () ->
      proven
        "fn triangle(n: Int64) -> Int64\n\
        \  requires n >= 0 && n <= 1000\n\
        \  ensures result <= n * 1000\n\
        \  decreases n\n\
        \  cost time finite\n\
         {\n\
        \  if n == 0 { 0 } else { n + triangle(n - 1) }\n\
         }\n\n\
         theorem triangle_at_least(n: Int64)\n\
        \  requires n >= 0 && n <= 1000\n\
        \  ensures triangle(n) >= n\n\
        \  decreases n\n\
        \  cost time finite\n\
         {\n\
        \  if n > 0 {\n\
        \    triangle_at_least(n - 1)\n\
        \  }\n\
         }\n\n\
         trait Bounded {\n\
        \  fn amount(self) -> Int64\n\
        \    ensures result >= 0 && result <= 1000\n\
        \    cost time finite\n\n\
        \  law covered(value: Self) {\n\
        \    triangle(value.amount()) >= value.amount()\n\
        \  }\n\
         }\n\n\
         type Box[Item](item: Item, amount: Int64)\n\
        \  invariant amount >= 0 && amount <= 1000\n\n\
         impl Bounded for Box[Element] {\n\
        \  fn amount(self) -> Int64\n\
        \    ensures result >= 0 && result <= 1000\n\
        \    cost time finite\n\
        \  {\n\
        \    self.amount\n\
        \  }\n\
         }\n\n\
         proof Bounded.covered for Box[Item] {\n\
        \  triangle_at_least(value.amount())\n\
         }\n");
  test "a law's proof names the law's parameters, where its requires hold" (fun () ->
      proven
        "trait Sized {\n\
        \  fn size(self) -> Int64\n\
        \    cost time finite\n\n\
        \  law at_least_one(value: Self)\n\
        \    requires value.size() > 0\n\
        \  {\n\
        \    value.size() >= 1\n\
        \  }\n\
         }\n\n\
         type Box(n: Int64)\n\n\
         impl Sized for Box {\n\
        \  fn size(self) -> Int64\n\
        \    cost time finite\n\
        \  {\n\
        \    self.n\n\
        \  }\n\
         }\n\n\
         theorem needs(value: Box)\n\
        \  requires value.size() > 0\n\
        \  ensures value.size() >= 1\n\
         {\n\
         }\n\n\
         proof Sized.at_least_one for Box {\n\
        \  needs(value)\n\
         }\n")

(* Concurrent code *)

let early_return ensures =
  "fn f(first: mut Int64, second: mut Int64) -> Int64\n  requires second < 100\n" ^ ensures
  ^ "  uses Tasks\n{\n  concurrent {\n    return 0\n    second += 1\n  }\n}\n"

let () =
  test "an early exit from a concurrent block waits for the other branches" (fun () ->
      proven (early_return "  ensures second == old(second) + 1\n"));
  test "an early exit from a concurrent block sees the other branches' changes" (fun () ->
      not_proven (early_return "  ensures second == old(second)\n") "prover.ensures");
  test "a concurrent block with no early exit is read as its branches in order" (fun () ->
      proven
        "fn f(first: mut Int64, second: mut Int64)\n\
        \  requires first < 100 && second < 100\n\
        \  ensures first == old(first) + 1 && second == old(second) + 1\n\
        \  uses Tasks\n\
         {\n\
        \  concurrent {\n\
        \    first += 1\n\
        \    second += 1\n\
        \  }\n\
         }\n")

(* Diagnostics *)

let () =
  test "a counterexample gives the values of the locals where it fails" (fun () ->
      let text =
        message
          "fn f(items: List[Int64], value: USize) -> Int64 {\n\
          \  var at: USize = 0\n\
          \  if value > 5 {\n\
          \    at = value\n\
          \  }\n\
          \  items[at]\n\
           }\n"
      in
      if not (contains text "`at` is") then fail "%s" text);
  test "a file's proof states list what proves as well as what does not" (fun () ->
      let database =
        Support.setup
          [
            ( "app::main",
              "fn f(items: List[Int64], index: USize) -> Int64\n\
              \  requires index < items.length()\n\
               {\n\
              \  items[index] + items[0]\n\
               }\n" );
          ]
      in
      let states =
        Prover.states ~record:(Support.record database) database solver
          (Support.module_of "app::main")
      in
      let failed =
        List.filter (fun (state : Diagnostic.span Prover.state) -> state.failure <> None) states
      in
      if List.length failed <> 1 || List.length states < 2 then
        fail "%d states, %d failed" (List.length states) (List.length failed));
  test "a call's requires that may not hold has a note at the clause" (fun () ->
      let text =
        "fn halved(count: Int64) -> Int64\n\
        \  requires count > 0\n\
        \  cost time O(1)\n\
         {\n\
        \  count / 2\n\
         }\n\n\
         fn f(value: Int64) -> Int64 {\n\
        \  halved(value)\n\
         }\n"
      in
      let database = Support.setup [ ("app::main", text) ] in
      match check database (Support.module_of "app::main") with
      | [ { notes = [ (span, _) ]; _ } ] ->
          let noted = String.sub text span.start (span.stop - span.start) in
          if noted <> "count > 0" then fail "the note is at `%s`" noted
      | found -> fail "%s" (String.concat "; " (Support.codes found)));
  test "the same failure on another path is reported once" (fun () ->
      let found =
        codes
          "fn f(items: List[Int64], index: USize) -> Int64 {\n\
          \  if index > 3 {\n\
          \    items[index]\n\
          \  } else {\n\
          \    items[index]\n\
          \  }\n\
           }\n"
      in
      if found <> [ "prover.requires" ] then fail "%s" (String.concat ", " found))

(* What is not proven yet *)

let () =
  test "a construct the prover cannot read yet" (fun () ->
      not_proven
        "fn run(task: (fn() cost time finite))\n\
        \  cost time finite\n\
         {\n\
        \  task()\n\
         }\n\n\
         fn f(quick: (fn() cost time O(1)))\n\
        \  cost time finite\n\
         {\n\
        \  run(quick)\n\
         }\n"
        "prover.unsupported");
  test "a type's invariant must be well defined" (fun () ->
      not_proven "type Ratio(top: Int64, bottom: Int64)\n  invariant top / bottom > 0\n"
        "prover.division");
  test "a type's invariant is well defined given the ones before it" (fun () ->
      proven
        "type Ratio(top: Int64, bottom: Int64)\n\
        \  invariant bottom > 0\n\
        \  invariant top / bottom >= 0\n");
  test "a cost clause's bound must be well defined" (fun () ->
      let found = codes "fn f(items: List[Int64]) -> Int64\n  cost time O(items[0])\n{\n  0\n}\n" in
      if not (List.mem "prover.requires" found) then fail "found [%s]" (String.concat "; " found));
  test "a derived ordering of a record compares its fields in order" (fun () ->
      proven
        "type Version(major: Int64, minor: Int64)\n\
        \  derives Equal, Ordered\n\n\
         fn f(first: Version, second: Version) -> Bool\n\
        \  requires first.major < second.major\n\
        \  ensures result\n\
         {\n\
        \  first < second\n\
         }\n");
  test "a derived ordering compares fields in declaration order, not in the order of their names"
    (fun () ->
      proven
        "type Entry(weight: Int64, label: Int64)\n\
        \  derives Equal, Ordered\n\n\
         fn f(first: Entry, second: Entry) -> Bool\n\
        \  requires first.weight < second.weight\n\
        \  ensures result\n\
         {\n\
        \  first < second\n\
         }\n");
  test "a derived ordering of a record falls to the next field on a tie" (fun () ->
      proven
        "type Version(major: Int64, minor: Int64)\n\
        \  derives Equal, Ordered\n\n\
         fn f(first: Version, second: Version) -> Bool\n\
        \  requires first.major == second.major && first.minor > second.minor\n\
        \  ensures result\n\
         {\n\
        \  first > second\n\
         }\n");
  test "a derived ordering of a sum orders by variant first" (fun () ->
      proven
        "type Light =\n\
        \  | Off\n\
        \  | Dim(level: Int64)\n\
        \  | On\n\
        \  derives Equal, Ordered\n\n\
         fn f(level: Int64) -> Bool\n\
        \  ensures result\n\
         {\n\
        \  Light.Off < Light.Dim(level: level) && Light.Dim(level: level) < Light.On\n\
         }\n");
  test "a derived ordering is not the reverse of itself" (fun () ->
      not_proven
        "type Version(major: Int64, minor: Int64)\n\
        \  derives Equal, Ordered\n\n\
         fn f(first: Version, second: Version) -> Bool\n\
        \  requires first.major < second.major\n\
        \  ensures result\n\
         {\n\
        \  first > second\n\
         }\n"
        "prover.ensures");
  test "recursion on an element of a field's list ends" (fun () ->
      proven
        "type Tree(value: Int64, children: List[Tree])\n\n\
         fn visit(tree: Tree)\n\
        \  cost time finite\n\
         {\n\
        \  for child in tree.children {\n\
        \    visit(child)\n\
        \  }\n\
         }\n");
  test "recursion on what is not a part does not end" (fun () ->
      not_proven
        "type Tree(value: Int64, children: List[Tree])\n\n\
         fn visit(tree: Tree)\n\
        \  cost time finite\n\
         {\n\
        \  visit(Tree(value: 0, children: tree.children.copy()))\n\
         }\n"
        "prover.termination");
  test "a trait's provided body keeps the trait's clauses on its own" (fun () ->
      not_proven
        "trait Sized {\n\
        \  fn size(self) -> Int64\n\
        \    ensures result >= 0\n\n\
        \  fn last_index(self) -> Int64\n\
        \    ensures result >= 0\n\
        \  {\n\
        \    self.size() - 1\n\
        \  }\n\
         }\n"
        "prover.ensures");
  test "a trait's provided body that keeps its clauses proves" (fun () ->
      proven
        "trait Sized {\n\
        \  fn size(self) -> Int64\n\
        \    ensures result >= 0\n\n\
        \  fn halved(self) -> Int64\n\
        \    ensures result >= 0\n\
        \  {\n\
        \    self.size() / 2\n\
        \  }\n\
         }\n");
  test "a call of a bound's method spends the time of that method" (fun () ->
      proven
        "fn contains[Element: Equal](items: List[Element], item: Element) -> Bool\n\
        \  cost time O(items.length() * time(Element.equal))\n\
         {\n\
        \  var index: USize = 0\n\
        \  while index < items.length()\n\
        \    invariant index <= items.length()\n\
        \    decreases items.length() - index\n\
        \  {\n\
        \    if items[index] == item {\n\
        \      return true\n\
        \    }\n\
        \    index += 1\n\
        \  }\n\
        \  false\n\
         }\n");
  test "the time of a bound's method is not free" (fun () ->
      let found =
        codes
          "fn contains[Element: Equal](items: List[Element], item: Element) -> Bool\n\
          \  cost time O(items.length())\n\
           {\n\
          \  var index: USize = 0\n\
          \  while index < items.length()\n\
          \    invariant index <= items.length()\n\
          \    decreases items.length() - index\n\
          \  {\n\
          \    if items[index] == item {\n\
          \      return true\n\
          \    }\n\
          \    index += 1\n\
          \  }\n\
          \  false\n\
           }\n"
      in
      if not (List.mem "prover.cost" found) then fail "found [%s]" (String.concat "; " found));
  test "log of a number is its bit length" (fun () ->
      proven
        "fn integer_square_root(value: UInt64) -> UInt64\n\
        \  cost time O(64)\n\
         {\n\
        \  var result: UInt64 = 0\n\
        \  var width: UInt64 = 4294967296\n\
        \  while width > 1\n\
        \    invariant width >= 1\n\
        \    invariant result + width <= 4294967296\n\
        \    decreases width\n\
        \    cost time O(log(4294967295) - log(width - 1))\n\
        \  {\n\
        \    let half = width / 2\n\
        \    let candidate = result + half\n\
        \    if candidate <= value / candidate {\n\
        \      result = candidate\n\
        \      width = width - half\n\
        \    } else {\n\
        \      width = half\n\
        \    }\n\
        \  }\n\
        \  result\n\
         }\n");
  test "log of a bounded integer is at most its width" (fun () ->
      proven
        "fn digits(value: UInt64) -> USize\n\
        \  cost time O(log(value))\n\
         {\n\
        \  todo\n\
         }\n\n\
         fn f(value: UInt64) -> USize\n\
        \  cost time O(1)\n\
         {\n\
        \  digits(value)\n\
         }\n");
  test "power of two numbers is their power" (fun () ->
      proven
        "fn table() -> USize\n\
        \  cost time O(power(2, 10))\n\
         {\n\
        \  todo\n\
         }\n\n\
         fn f() -> USize\n\
        \  cost time O(1)\n\
         {\n\
        \  table()\n\
         }\n");
  test "a slice changed through a call changes its run of the list" (fun () ->
      proven
        (""
       ^ "fn zero(part: mut Slice[Int64])\n\
         \  ensures part.length() == old(part.length())\n\
         \  ensures forall i in 0..part.length() => part.model()[i] == 0\n\
          {\n\
         \  todo\n\
          }\n\n\
          fn f(items: mut List[Int64])\n\
         \  requires items.length() >= 4\n\
         \  ensures items[1] == 0\n\
         \  ensures items[3] == old(items[3])\n\
          {\n\
         \  zero(mut items[..2])\n\
          }\n"));
  test "a slice changed through a call changes nothing more than it says" (fun () ->
      not_proven
        (""
       ^ "fn zero(part: mut Slice[Int64])\n\
         \  ensures part.length() == old(part.length())\n\
         \  ensures forall i in 0..part.length() => part.model()[i] == 0\n\
          {\n\
         \  todo\n\
          }\n\n\
          fn f(items: mut List[Int64])\n\
         \  requires items.length() >= 4\n\
         \  ensures items[2] == 0\n\
          {\n\
         \  zero(mut items[..2])\n\
          }\n")
        "prover.ensures");
  test "an unsigned left shift that fits multiplies by a power of two" (fun () ->
      proven
        "fn f(value: UInt8) -> UInt8\n\
        \  requires value < 16\n\
        \  ensures result == value * 16\n\
         {\n\
        \  value << 4\n\
         }\n");
  test "an unsigned right shift divides by a power of two" (fun () ->
      proven "fn f(value: UInt64) -> UInt64\n  ensures result == value / 4\n{\n  value >> 2\n}\n");
  test "a left shift that may not fit is not known to multiply" (fun () ->
      not_proven "fn f(value: UInt8) -> UInt8\n  ensures result == value * 16\n{\n  value << 4\n}\n"
        "prover.ensures");
  test "a loop that changes a slice of any elements under a cost clause" (fun () ->
      proven
        "fn swap_each[Element](part: mut Slice[Element])\n\
        \  requires part.length() >= 1\n\
        \  cost time O(part.length())\n\
         {\n\
        \  var index: USize = 0\n\
        \  while index < part.length()\n\
        \    invariant index <= part.length()\n\
        \    invariant part.length() == old(part.length())\n\
        \    decreases part.length() - index\n\
        \  {\n\
        \    mut part.swap(0, second: index)\n\
        \    index += 1\n\
        \  }\n\
         }\n");
  test "a quantifier's body must be well defined" (fun () ->
      not_proven
        "fn f(items: List[Int64]) -> Int64\n\
        \  requires forall i in 0..items.length() + 1 => items[i] > 0\n\
         {\n\
        \  0\n\
         }\n"
        "prover.requires");
  test "a quantifier's body within its range is well defined" (fun () ->
      proven
        "fn f(items: List[Int64]) -> Int64\n\
        \  requires forall i in 0..items.length() => items[i] > 0\n\
         {\n\
        \  0\n\
         }\n");
  test "a call under a quantifier gives a value for each value, not one for all" (fun () ->
      not_proven
        "fn same(item: Int64) -> Int64\n\
        \  ensures result == item\n\
         {\n\
        \  item\n\
         }\n\n\
         fn f(items: List[Int64]) -> Bool\n\
        \  requires items.length() == 2 && items[0] == 1 && items[1] == 2\n\
        \  ensures !result\n\
         {\n\
        \  forall i in 0..items.length() => same(items[i]) == items[i]\n\
         }\n"
        "prover.ensures");
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
  test "an answer read from the cache is marked as asked now" (fun () ->
      let directory = Filename.temp_dir "truss-answers" "" in
      let now = Logic.Symbol.Variable { label = "asked.now"; numbers = [] } in
      let query =
        {
          Logic.declarations = [ Logic.Constant (now, Logic.Int) ];
          facts = [];
          goal = Logic.Operation (">=", [ Logic.Symbol now; Logic.Symbol now ]);
        }
      in
      let file = Filename.concat directory (Solver.key query) in
      Out_channel.with_open_bin file (fun channel -> output_string channel "proven\n");
      Unix.utimes file 1. 1.;
      match Solver.find ~cache:directory () with
      | Error message -> fail "%s" message
      | Ok cached ->
          if Solver.solve cached query <> Solver.Proven then fail "expected the stored answer";
          if (Unix.stat file).st_mtime < 2. then fail "the answer's file was not marked as asked");
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

(* Arrays *)

let () =
  test "a slice of a whole array is within it" (fun () ->
      proven
        "fn f[Element, count: USize](items: mut Array[Element, count])\n\
        \  ensures items.length() == old(items.length())\n\
         {\n\
        \  mut items[..].reverse()\n\
         }\n");
  test "a loop that changes an array's elements keeps their potentials" (fun () ->
      proven
        "fn reversed[Element, count: USize](items: mut Array[Element, count]) yields mut Element\n\
        \  cost time O(items.length())\n\
         {\n\
        \  var index = items.length()\n\
        \  while index > 0\n\
        \    invariant items.length() == old(items.length())\n\
        \    invariant index <= items.length()\n\
        \    decreases index\n\
        \  {\n\
        \    index -= 1\n\
        \    yield mut items[index]\n\
        \  }\n\
         }\n");
  test "a slice of an array is within it only as far as its count" (fun () ->
      not_proven
        "fn f[Element, count: USize](items: mut Array[Element, count]) {\n\
        \  mut items[1..].reverse()\n\
         }\n"
        "prover.requires")

(* Deep definitions *)

let () =
  test "a nested call's arguments are written once, however deep it nests" (fun () ->
      let most depth =
        let nested =
          List.fold_left
            (fun inner _ -> "spread(" ^ inner ^ ")")
            "value + 12345 - 12345" (List.init depth Fun.id)
        in
        let database =
          Support.setup
            [
              ( "app::main",
                "fn spread(value: Int64) -> Int64\n\
                \  requires 0 <= value && value < 1000\n\
                \  ensures result == value\n\
                \  cost time O(1)\n\
                 {\n\
                \  (value + value + value + value) / 4\n\
                 }\n\n\
                 fn f(value: Int64) -> Int64\n\
                \  requires 0 <= value && value < 100\n\
                \  ensures result == value\n\
                \  cost time O(1)\n\
                 {\n\
                \  " ^ nested ^ "\n}\n" );
            ]
        in
        let key =
          List.find
            (fun (declaration : Resolve.Names.declaration) ->
              Path.show declaration.path = "app::main::f")
            (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))
        in
        match Query.demand database Prover.proof (Resolve.Names.key_of key) with
        | Obligations { obligations; _ } ->
            List.fold_left
              (fun most (obligation : Prover.Translate.obligation) ->
                let text = Logic.text obligation.query in
                let rec count from found =
                  match String.index_from_opt text from '1' with
                  | Some at when at + 5 <= String.length text && String.sub text at 5 = "12345" ->
                      count (at + 5) (found + 1)
                  | Some at -> count (at + 1) found
                  | None -> found
                in
                max most (count 0 0))
              0 obligations
        | _ ->
            fail "expected obligations";
            0
      in
      let shallow = most 3 and deep = most 6 in
      if deep > shallow then fail "written %d times nested 3 deep, %d times 6 deep" shallow deep);
  test "a query over an unfolded definition can be asked with the contract alone" (fun () ->
      let database =
        Support.setup
          [
            ( "app::main",
              "fn halved(value: Int64) -> Int64\n\
              \  requires value >= 0\n\
              \  ensures result <= value\n\
              \  cost time O(1)\n\
               {\n\
              \  value / 2\n\
               }\n\n\
               fn f(value: Int64) -> Int64\n\
              \  requires value >= 0\n\
              \  ensures result <= value\n\
              \  cost time O(1)\n\
               {\n\
              \  halved(value)\n\
               }\n" );
          ]
      in
      let key =
        List.find
          (fun (declaration : Resolve.Names.declaration) ->
            Path.show declaration.path = "app::main::f")
          (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))
      in
      match Query.demand database Prover.proof (Resolve.Names.key_of key) with
      | Obligations { obligations; _ } -> (
          match
            List.find_opt
              (fun (obligation : Prover.Translate.obligation) -> obligation.code = Ensures)
              obligations
          with
          | Some { query; contracts_alone = Some alone; _ } ->
              if List.length alone.facts >= List.length query.facts then
                fail "the contract alone keeps every fact"
          | Some _ -> fail "no query with the contract alone"
          | None -> fail "no ensures obligation")
      | _ -> fail "expected obligations")

(* Triggers *)

let v label = Logic.Symbol.Variable { label; numbers = [] }

let triggered fact =
  let open Logic in
  Logic.text
    {
      declarations =
        [ Function (v "f", [ Int ], Int); Function (v "g", [ Int ], Int); Constant (v "n", Int) ];
      facts = [ fact ];
      goal = Operation (">", [ Apply (v "f", [ Symbol (v "n") ]); int 0 ]);
    }

let () =
  let open Logic in
  let i = Symbol (v "i") and j = Symbol (v "j") in
  let f term = Apply (v "f", [ term ]) and g term = Apply (v "g", [ term ]) in
  let positive term = Operation (">", [ term; int 0 ]) in
  let expect fact fragment =
    let text = triggered fact in
    if not (contains text fragment) then fail "expected %s in %s" fragment text
  in
  test "a quantified fact triggers on an application of its variable" (fun () ->
      expect
        (Forall ([ (v "i", Int) ], Operation (">=", [ i; int 0 ]) ==> positive (f i)))
        ":pattern ((x0 b0))");
  test "a trigger has no arithmetic on a bound variable" (fun () ->
      let text =
        triggered (Forall ([ (v "i", Int) ], positive (f (Operation ("+", [ i; int 1 ])))))
      in
      if contains text ":pattern" then fail "%s" text);
  test "a trigger that would match its own body's larger term is passed over" (fun () ->
      expect
        (Forall
           ( [ (v "i", Int) ],
             Operation ("<", [ f i; f (Operation ("+", [ i; int 1 ])) ]) &&& positive (g i) ))
        ":pattern ((x2 b0)))");
  test "a definition triggers on what it defines" (fun () ->
      let text =
        triggered (Forall ([ (v "i", Int) ], equal (f i) (Operation ("+", [ g i; int 1 ]))))
      in
      if (not (contains text ":pattern ((x0 b0)))")) || contains text ":pattern ((x1" then
        fail "%s" text);
  let query fact =
    {
      declarations =
        [ Function (v "f", [ Int ], Int); Function (v "g", [ Int ], Int); Constant (v "n", Int) ];
      facts = [ fact ];
      goal = Operation (">", [ Apply (v "f", [ Symbol (v "n") ]); int 0 ]);
    }
  in
  test "a quantified fact with no trigger is told apart" (fun () ->
      if
        not
          (untriggered
             (query (Forall ([ (v "i", Int) ], positive (f (Operation ("+", [ i; int 1 ])))))))
      then fail "a fact on f(i + 1) alone has no trigger";
      if untriggered (query (Forall ([ (v "i", Int) ], positive (f i)))) then
        fail "a fact on f(i) has one");
  test "variables named by no one application share a trigger" (fun () ->
      expect
        (Forall ([ (v "i", Int); (v "j", Int) ], Operation ("<", [ f i; g j ])))
        ":pattern ((x0 b0) (x2 b1))")

(* Short-circuit operators *)

let bump =
  "fn bump(count: mut UInt8) -> Bool\n\
  \  requires count < 200\n\
  \  ensures count == old(count) + 1\n\
  \  ensures result\n\
   {\n\
  \  count += 1\n\
  \  true\n\
   }\n\n"

let () =
  test "a change on the right of && happens only where the left holds" (fun () ->
      proven
        (bump
       ^ "fn f(go: Bool) -> UInt8\n\
         \  ensures go ==> result == 1\n\
         \  ensures !go ==> result == 0\n\
          {\n\
         \  var count: UInt8 = 0\n\
         \  let _ = go && bump(mut count)\n\
         \  count\n\
          }\n"));
  test "a change on the right of || is not known to have happened" (fun () ->
      not_proven
        (bump
       ^ "fn f(done: Bool) -> UInt8\n\
         \  ensures result == 1\n\
          {\n\
         \  var count: UInt8 = 0\n\
         \  let _ = done || bump(mut count)\n\
         \  count\n\
          }\n")
        "prover.ensures")

(* Function values in the logic *)

let apply_function =
  "fn apply(measure: (fn(Int64) -> Int64 cost time finite), value: Int64) -> Int64\n\
  \  ensures result == measure(value)\n\
  \  cost time finite\n\
   {\n\
  \  measure(value)\n\
   }\n\n"

let () =
  test "a pure function value gives the same result for the same argument" (fun () ->
      proven
        "fn f(measure: (fn(Int64) -> Int64 cost time finite), value: Int64) -> Bool\n\
        \  ensures result\n\
         {\n\
        \  measure(value) == measure(value)\n\
         }\n");
  test "a function value that uses a capability may give different results" (fun () ->
      not_proven
        "fn f(read: (fn(Int64) -> Int64 uses Clock cost time finite), value: Int64) -> Bool\n\
        \  uses Clock\n\
        \  ensures result\n\
         {\n\
        \  read(value) == read(value)\n\
         }\n"
        "prover.ensures");
  test "a function value without a time clause is a fresh result" (fun () ->
      not_proven
        "fn f(measure: fn(Int64) -> Int64, value: Int64) -> Bool\n\
        \  ensures result\n\
         {\n\
        \  measure(value) == measure(value)\n\
         }\n"
        "prover.ensures");
  test "a lambda applied is its body" (fun () ->
      proven
        (apply_function
       ^ "fn f(value: Int64) -> Int64\n\
         \  ensures result == value / 2\n\
          {\n\
         \  apply(fn(each) { each / 2 }, value: value)\n\
          }\n"));
  test "a lambda whose body is not its definition gives what its body shows" (fun () ->
      proven
        (apply_function
       ^ "fn f() -> Int64\n\
         \  ensures result == 4\n\
          {\n\
         \  apply(fn(each) { var next = each\n\
         \    if next < 100 { next += 1 }\n\
         \    next }, value: 3)\n\
          }\n"));
  test "what a lambda's body shows is about its own argument" (fun () ->
      not_proven
        (apply_function
       ^ "fn f() -> Int64\n\
         \  ensures result == 3\n\
          {\n\
         \  apply(fn(each) { var next = each\n\
         \    if next < 100 { next += 1 }\n\
         \    next }, value: 3)\n\
          }\n")
        "prover.ensures");
  let halved =
    "fn apply(measure: (fn(UInt64) -> UInt64 cost time finite), value: UInt64) -> UInt64\n\
    \  ensures result == measure(value)\n\
    \  cost time finite\n\
     {\n\
    \  measure(value)\n\
     }\n\n\
     fn halved(value: UInt64) -> UInt64\n\
    \  requires value >= 0\n\
    \  ensures result <= value\n\
    \  cost time finite\n\
     {\n\
    \  value / 2\n\
     }\n\n"
  in
  test "a named function with a requires, as a value, keeps its ensures" (fun () ->
      proven
        (halved
       ^ "fn f(value: UInt64) -> Bool\n\
         \  ensures result\n\
          {\n\
         \  apply(halved, value: value) <= value\n\
          }\n"));
  test "a named function, as a value, gives no more than its ensures" (fun () ->
      not_proven
        (halved
       ^ "fn f(value: UInt64) -> Bool\n\
         \  ensures result\n\
          {\n\
         \  apply(halved, value: value) < value\n\
          }\n")
        "prover.ensures");
  test "a lambda applied knows what it captures" (fun () ->
      proven
        (apply_function
       ^ "fn f(value: Int64, floor: Int64) -> Int64\n\
         \  ensures result == (if value > floor { value } else { floor })\n\
          {\n\
         \  apply(fn(each) { if each > floor { each } else { floor } }, value: value)\n\
          }\n"));
  test "two lambdas with the same body are the same function" (fun () ->
      proven
        "fn tally(measure: (fn(Int64) -> Int64 cost time finite)) -> Int64\n\
        \  cost time finite\n\
         {\n\
        \  var total = 0\n\
        \  total = measure(1)\n\
        \  total\n\
         }\n\n\
         fn f() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  tally(fn(each) { each / 2 }) == tally(fn(other) { other / 2 })\n\
         }\n");
  test "lambdas with different bodies are not known to be the same function" (fun () ->
      not_proven
        "fn tally(measure: (fn(Int64) -> Int64 cost time finite)) -> Int64\n\
        \  cost time finite\n\
         {\n\
        \  var total = 0\n\
        \  total = measure(1)\n\
        \  total\n\
         }\n\n\
         fn f() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  tally(fn(each) { each / 2 }) == tally(fn(other) { other / 3 })\n\
         }\n"
        "prover.ensures");
  test "a named pure function applied is the function" (fun () ->
      proven
        ("fn half(value: Int64) -> Int64\n  cost time O(1)\n{\n  value / 2\n}\n\n" ^ apply_function
       ^ "fn f() -> Int64\n  ensures result == 3\n{\n  apply(half, value: 7)\n}\n"))

let () =
  test "a specification spends nothing, whatever it calls" (fun () ->
      proven
        "fn f(items: List[Int64], keep: (fn(Int64) -> Bool cost time finite)) -> USize\n\
        \  requires forall i in 0..items.length() => keep(items.model()[i])\n\
        \  cost time O(1)\n\
         {\n\
        \  items.length()\n\
         }\n")

(* Sums over sequences *)

let () =
  test "appending adds the new element's measure to a sum" (fun () ->
      proven
        "theorem appending(items: Sequence[List[Int64]], row: List[Int64])\n\
        \  ensures items.append(row).sum(fn(each) { each.length() })\n\
        \    == items.sum(fn(other) { other.length() }) + row.length()\n\
         {\n\
         }\n");
  test "a sum is not known to be anything else" (fun () ->
      not_proven
        "theorem appending(items: Sequence[List[Int64]], row: List[Int64])\n\
        \  ensures items.append(row).sum(fn(each) { each.length() })\n\
        \    == items.sum(fn(other) { other.length() })\n\
         {\n\
         }\n"
        "prover.ensures");
  test "a loop whose iterations cost different amounts is bounded by a sum" (fun () ->
      proven
        "fn count_cells(rows: List[List[Int64]]) -> USize\n\
        \  cost time O(rows.length() + rows.model().sum(fn(cells) { cells.length() }))\n\
         {\n\
        \  var count: USize = 0\n\
        \  for row in rows\n\
        \    cost time O(yielded.length() + yielded.sum(fn(cells) { cells.length() }))\n\
        \  {\n\
        \    for _ in row {\n\
        \      count = count.saturating_add(1)\n\
        \    }\n\
        \  }\n\
        \  count\n\
         }\n");
  test "a loop's bound that leaves out its iterations' sum does not hold" (fun () ->
      not_proven
        "fn count_cells(rows: List[List[Int64]]) -> USize\n\
        \  cost time O(rows.length())\n\
         {\n\
        \  var count: USize = 0\n\
        \  for row in rows {\n\
        \    for _ in row {\n\
        \      count = count.saturating_add(1)\n\
        \    }\n\
        \  }\n\
        \  count\n\
         }\n"
        "prover.cost")

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
    | [] -> Prover.diagnostics ~record:(Support.record database) database solver module_
    | errors -> errors
  in
  (match prove () with
  | [] -> ()
  | found -> fail "before the edit: %s" (String.concat "; " (Support.codes found)));
  Database.Testing.set_text engine module_ after;
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

(* Addresses of views *)

let () =
  let proven_in_standard text =
    let database = Engine.context (Engine.create ~log:true ()) in
    Database.load_package (Engine.of_context database)
      ~name:{ owner = None; name = "standard" }
      ~dependencies:[]
      [ (Support.module_of "standard::probe", text) ];
    match check database (Support.module_of "standard::probe") with
    | [] -> ()
    | found -> fail "%s" (String.concat "; " (List.map (fun (d : Diagnostic.t) -> d.message) found))
  in
  test "a view of a scalar ends within the address space and is not at zero" (fun () ->
      proven_in_standard
        "use standard::intrinsic\n\n\
         fn placed(starts: intrinsic::View[USize]) -> USize {\n\
        \  let first = intrinsic::view_address(starts)\n\
        \  proof {\n\
        \    assert intrinsic::view_length(starts) == 0 || first >= 1\n\
        \    assert first + 8 * intrinsic::view_length(starts) <= 18446744073709551616\n\
        \  }\n\
        \  first\n\
         }\n")

let () = finish ()
