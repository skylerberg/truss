module Patterns = Type_checker.For_testing.Patterns
module Usage = Type_checker.For_testing.Usage

(* The tests of the rules on use: unused variables and unreachable code. *)

open Harness
open Support

let check database module_ =
  Resolve.diagnostics database module_
  @ Interface.diagnostics database module_
  @ Infer.diagnostics database module_
  @ Patterns.diagnostics database module_
  @ Usage.diagnostics database module_

let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]

let () =
  test "a variable nothing reads is an error with a fix that renames it _" (fun () ->
      one_diagnostic "fn f() {\n  let count = 1\n}\n" "usage.unused_variable"
        ~fixed:"fn f() {\n  let _ = 1\n}\n");
  test "a parameter nothing reads is not an error" (fun () -> fine "fn f(count: Int64) {}\n");
  test "an unused field of a record pattern is fixed by name" (fun () ->
      one_diagnostic
        "type Pair2(first: Int64, second: Int64)\n\n\
         fn f(pair: Pair2) -> Int64 {\n\
        \  let (first, second) = pair\n\
        \  first\n\
         }\n"
        "usage.unused_variable"
        ~fixed:
          "type Pair2(first: Int64, second: Int64)\n\n\
           fn f(pair: Pair2) -> Int64 {\n\
          \  let (first, second: _) = pair\n\
          \  first\n\
           }\n");
  test "a binding in a match arm must be used" (fun () ->
      one_diagnostic
        "fn f(found: Option[Int64]) -> Int64 {\n\
        \  match found {\n\
        \    Some(value) => 1\n\
        \    None => 0\n\
        \  }\n\
         }\n"
        "usage.unused_variable");
  test "code after a return is unreachable, with a fix that deletes it" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  return 1\n  2\n}\n" "usage.unreachable_code"
        ~fixed:"fn f() -> Int64 {\n  return 1\n}\n");
  test "code after a loop that is never left is unreachable" (fun () ->
      one_diagnostic "fn f() -> Int64 {\n  while true {\n  }\n  1\n}\n" "usage.unreachable_code");
  test "code after a loop that breaks is reachable" (fun () ->
      fine "fn f() -> Int64 {\n  while true {\n    break\n  }\n  1\n}\n");
  test "code after todo is not unreachable" (fun () -> fine "fn f() -> Int64 {\n  todo\n  1\n}\n");
  test "if false is not reported" (fun () ->
      fine "fn f() -> Int64 {\n  if false {\n    return 0\n  }\n  1\n}\n");
  test "a branch after one that returns still runs" (fun () ->
      fine "fn f() -> Int64\n  uses Tasks\n{\n  concurrent {\n    return 1\n    return 2\n  }\n}\n");
  test "code after a block whose branch never finishes is unreachable" (fun () ->
      one_diagnostic
        "fn f() -> Int64\n\
        \  uses Tasks\n\
         {\n\
        \  concurrent {\n\
        \    return 1\n\
        \    return 2\n\
        \  }\n\
        \  3\n\
         }\n"
        "usage.unreachable_code")
