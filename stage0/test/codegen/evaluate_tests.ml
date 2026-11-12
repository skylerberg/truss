(* The prover deciding a tagged template's check by running it, through
   code generation. *)

open Codegen_support

(* The oracles' responses, recorded in the engine, as the database does for
   a session. *)
let record database responses =
  let engine = Engine.of_context database in
  List.iter (fun (key, response) -> Engine.set engine Prover.oracle_response key response) responses

let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

(* The prover's diagnostics of a module, deciding template checks by
   running them. *)
let proven_with_running text =
  let database, compile = load text in
  Prover.diagnostics
    ~evaluator:(Evaluator.of_compiler (lazy compile))
    ~record:(record database) database (Lazy.force solver) example

let shout = Fixtures.Evaluate.shout

let () =
  test "a template check that holds is proven by running it" (fun () ->
      match
        proven_with_running
          (shout ^ Fixtures.Evaluate.template_check_that_holds_is_proven_by_running_it)
      with
      | [] -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)));
  test "a template check that does not hold fails, saying it ran" (fun () ->
      match
        proven_with_running
          (shout ^ Fixtures.Evaluate.template_check_that_does_not_hold_fails_saying_it)
      with
      | [ diagnostic ] ->
          if Diagnostic.Code.name diagnostic.code <> "prover.requires" then
            fail "%s" (Diagnostic.Code.name diagnostic.code);
          let ran = "Running it on this template's text gives `false`." in
          let length = String.length ran and message = diagnostic.message in
          let rec contains position =
            position + length <= String.length message
            && (String.sub message position length = ran || contains (position + 1))
          in
          if not (contains 0) then fail "%s" message
      | actual -> fail "%d diagnostics" (List.length actual));
  test "a check that reads a template's parts is not run" (fun () ->
      let text = Fixtures.Evaluate.check_that_reads_a_templates_parts_is_not_run in
      match proven_with_running text with
      | [] -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)))

let counting = Fixtures.Evaluate.counting

let () =
  test "a call whose arguments are known is evaluated by running it" (fun () ->
      match
        proven_with_running
          (counting ^ Fixtures.Evaluate.call_whose_arguments_are_known_is_evaluated_by)
      with
      | [] -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)));
  test "without running it, such a call is known only by its contract" (fun () ->
      let database, _ =
        load (counting ^ Fixtures.Evaluate.without_running_it_such_a_call_is_known_only_by)
      in
      match Prover.diagnostics ~record:(record database) database (Lazy.force solver) example with
      | [ _ ] -> ()
      | actual -> fail "%d diagnostics" (List.length actual));
  test "running a call gives its real result, not the hoped one" (fun () ->
      match
        proven_with_running
          (counting ^ Fixtures.Evaluate.running_a_call_gives_its_real_result_not_the)
      with
      | [ _ ] -> ()
      | actual -> fail "%d diagnostics" (List.length actual))

let () =
  test "a call that is run uses the argument it gives a parameter that has a default" (fun () ->
      let source promised =
        Fixtures.Evaluate.promised ^ promised ^ "\n{\n  count_to(limit: 4)\n}\n"
      in
      (match proven_with_running (source "4") with
      | [] -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)));
      match proven_with_running (source "3") with
      | [ _ ] -> ()
      | actual -> fail "%d diagnostics for the default's value" (List.length actual))

(* The same tag at the same path with the same text, checked by code that
   differs: a check is kept under the code that ran, not under its name. *)
let () =
  test "a template's check is done again when the code it runs has changed" (fun () ->
      let use = Fixtures.Evaluate.use in
      let accepts_all =
        let refuses = "        quiet = false" in
        let at = ref 0 in
        while String.sub shout !at (String.length refuses) <> refuses do
          incr at
        done;
        String.sub shout 0 !at ^ "        quiet = true"
        ^ String.sub shout
            (!at + String.length refuses)
            (String.length shout - !at - String.length refuses)
      in
      (match proven_with_running (shout ^ use) with
      | [ _ ] -> ()
      | actual -> fail "expected the first check to fail, got %d diagnostics" (List.length actual));
      match proven_with_running (accepts_all ^ use) with
      | [] -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)))

(* The same call with the same arguments, in one database, before and
   after the callee's body changes: a stale value would prove a false
   [ensures]. *)
let () =
  test "a call is run again when the callee's body has changed" (fun () ->
      let source body =
        "fn same(value: UInt8) -> UInt8\n  cost time finite\n{\n  " ^ body
        ^ "\n}\n\nfn run_example() -> UInt8\n  ensures result == 7\n{\n  same(7)\n}\n"
      in
      let database, compile = load (source "value") in
      let proven () =
        Prover.diagnostics
          ~evaluator:(Evaluator.of_compiler (lazy compile))
          ~record:(record database) database (Lazy.force solver) example
      in
      (match proven () with
      | [] -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)));
      Database.For_testing.set_text (Engine.of_context database) example (source "0");
      match proven () with
      | [ _ ] -> ()
      | actual ->
          fail "expected the changed callee to fail, got %d diagnostics" (List.length actual))

(* A timeout is not kept: the next check runs the template's check again,
   with the code unchanged. The evaluator here times out on its first run
   only, as a run on a loaded machine may. *)
let () =
  test "a template check that timed out is run again on the next check" (fun () ->
      let database, _ =
        load (shout ^ Fixtures.Evaluate.template_check_that_timed_out_is_run_again_on_the)
      in
      let runs = ref 0 in
      let evaluator : Prover.evaluator =
        {
          code_key = (fun _ -> Some "unchanged");
          run =
            (fun _ ->
              incr runs;
              if !runs = 1 then Timed_out else Returned Z.one);
        }
      in
      let proven () =
        Prover.diagnostics ~evaluator ~record:(record database) database (Lazy.force solver) example
      in
      (match proven () with
      | [ _ ] -> ()
      | actual ->
          fail "expected the timed-out check to fail, got %d diagnostics" (List.length actual));
      (match proven () with
      | [] -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)));
      if !runs <> 2 then fail "expected 2 runs, got %d" !runs)

(* Only a proof that used a value from running code trusts compiled code. *)
let () =
  test "a state says whether its proof trusts compiled code" (fun () ->
      let database, compile =
        load (counting ^ Fixtures.Evaluate.state_says_whether_its_proof_trusts_compiled_code)
      in
      let states =
        Prover.states
          ~evaluator:(Evaluator.of_compiler (lazy compile))
          ~record:(record database) database (Lazy.force solver) example
      in
      let ensures =
        List.filter
          (fun (state : Diagnostic.span Prover.state) ->
            Diagnostic.Code.name (Prover state.code) = "prover.ensures")
          states
      in
      match ensures with
      | [ first; second ] ->
          if not (first.trusts_compiled_code && first.failure = None) then
            fail "the proof of f's ensures should trust compiled code";
          if second.trusts_compiled_code || second.failure <> None then
            fail "the proof of g's ensures should be proven without trusting compiled code"
      | actual -> fail "expected 2 ensures states, got %d" (List.length actual))
