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

(* What is not proven yet *)

let () =
  test "a construct the prover cannot read yet" (fun () ->
      not_proven
        "fn f(items: List[Int64]) -> Int64 {\n  match items.length() {\n    _ => 0\n  }\n}\n"
        "prover.unsupported");
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
