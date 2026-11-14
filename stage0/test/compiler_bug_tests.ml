(* The tests of how the compiler reports its own failures. *)

open Harness

let expect_bug work check =
  match work () with
  | () -> fail "expected a compiler bug"
  | exception Compiler_bug.Bug bug -> check bug

let () =
  test "a bug carries its stage and its message" (fun () ->
      expect_bug
        (fun () -> Compiler_bug.bug ~stage:"Lower" "no type for expression %d" 7)
        (fun bug ->
          if bug.stage <> "Lower" || bug.message <> "no type for expression 7" || bug.doing <> []
          then fail "got %s" (Compiler_bug.to_string bug)));
  test "a bug gathers the compiler's context, innermost first" (fun () ->
      expect_bug
        (fun () ->
          Compiler_bug.while_doing ~stage:"Compile" "lowering a caller" (fun () ->
              Compiler_bug.while_doing ~stage:"Compile" "lowering a callee" (fun () ->
                  Compiler_bug.bug ~stage:"Lower" "a local with no place")))
        (fun bug ->
          if bug.stage <> "Lower" || bug.doing <> [ "lowering a callee"; "lowering a caller" ] then
            fail "got %s" (Compiler_bug.to_string bug)));
  test "a broken invariant the standard library finds is a bug of the stage that ran" (fun () ->
      expect_bug
        (fun () -> Compiler_bug.while_doing ~stage:"Compile" "lowering f" (fun () -> List.hd []))
        (fun bug ->
          if bug.stage <> "Compile" || bug.doing <> [ "lowering f" ] then
            fail "got %s" (Compiler_bug.to_string bug)));
  test "a failed assert is a bug of the stage that ran" (fun () ->
      expect_bug
        (fun () ->
          Compiler_bug.while_doing ~stage:"Prover" "translating f" (fun () -> assert false))
        (fun bug ->
          if
            bug.stage <> "Prover" || bug.doing <> [ "translating f" ]
            || not (String.starts_with ~prefix:"Assert_failure at " bug.message)
          then fail "got %s" (Compiler_bug.to_string bug)));
  test "a bug reads as its stage, its message, and each step of its context" (fun () ->
      let text =
        Compiler_bug.to_string
          { stage = "Lower"; message = "no impl"; doing = [ "lowering f"; "lowering g" ] }
      in
      if text <> "Lower: no impl\n  while lowering f\n  while lowering g" then fail "got %S" text)
