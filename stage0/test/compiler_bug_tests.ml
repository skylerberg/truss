(* The tests of how the compiler reports its own failures. *)

open Harness

let expect_bug f check =
  match f () with
  | () -> fail "expected a compiler bug"
  | exception Compiler_bug.Bug bug -> check bug

let () =
  test "a bug carries its stage and what it found" (fun () ->
      expect_bug
        (fun () -> Compiler_bug.bug ~stage:"Lower" "no type for expression %d" 7)
        (fun bug ->
          if bug.stage <> "Lower" || bug.message <> "no type for expression 7" || bug.doing <> []
          then fail "got %s" (Compiler_bug.to_string bug)));
  test "a bug gathers what the compiler was doing, innermost first" (fun () ->
      expect_bug
        (fun () ->
          Compiler_bug.within ~stage:"Compile" "lowering a caller" (fun () ->
              Compiler_bug.within ~stage:"Compile" "lowering a cursor" (fun () ->
                  Compiler_bug.bug ~stage:"Yields" "a local a cursor cannot keep")))
        (fun bug ->
          if bug.stage <> "Yields" || bug.doing <> [ "lowering a cursor"; "lowering a caller" ] then
            fail "got %s" (Compiler_bug.to_string bug)));
  test "a broken invariant the standard library finds is a bug of the stage that ran" (fun () ->
      expect_bug
        (fun () -> Compiler_bug.within ~stage:"Compile" "lowering f" (fun () -> List.hd []))
        (fun bug ->
          if bug.stage <> "Compile" || bug.doing <> [ "lowering f" ] then
            fail "got %s" (Compiler_bug.to_string bug)));
  test "a program the compiler cannot build yet is not a bug" (fun () ->
      match
        Compiler_bug.within ~stage:"Compile" "lowering f" (fun () ->
            Compiler_bug.unsupported "a quantifier in code that runs")
      with
      | () -> fail "expected it to be raised"
      | exception Compiler_bug.Unsupported { what; at = None } ->
          if what <> "a quantifier in code that runs" then fail "got %s" what
      | exception Compiler_bug.Unsupported _ -> fail "expected no position");
  test "a bug reads as its stage, what it found, and each thing being done" (fun () ->
      let text =
        Compiler_bug.to_string
          { stage = "Lower"; message = "no impl"; doing = [ "lowering f"; "lowering g" ] }
      in
      if text <> "Lower: no impl\n  while lowering f\n  while lowering g" then fail "got %S" text)

let () = finish ()
