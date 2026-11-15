open Codegen_support

let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

let verdicts ~evaluator database =
  Pipeline.decide ~evaluator (Lazy.force solver)
    (Pipeline.prove (pipeline database) [ example_file ])

let proven_with_running text =
  let database, compile = load text in
  Pipeline.diagnostics
    (verdicts ~evaluator:(Evaluator.of_compiler (lazy compile)) database)
    example_file

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

let () =
  test "a template check that timed out is run again on the next check" (fun () ->
      let database, _ =
        load (shout ^ Fixtures.Evaluate.template_check_that_timed_out_is_run_again_on_the)
      in
      let runs = ref 0 in
      let evaluator : Prover.evaluator =
       fun _ ->
        incr runs;
        if !runs = 1 then Timed_out else Ran true
      in
      let proven () = Pipeline.diagnostics (verdicts ~evaluator database) example_file in
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

let () =
  test "a state says whether its proof trusts compiled code" (fun () ->
      let database, compile =
        load (shout ^ Fixtures.Evaluate.state_says_whether_its_proof_trusts_compiled_code)
      in
      let states =
        Pipeline.states
          (verdicts ~evaluator:(Evaluator.of_compiler (lazy compile)) database)
          example_file
      in
      let with_code code =
        List.filter
          (fun (state : Diagnostic.span Prover.state) ->
            Diagnostic.Code.name (Prover state.code) = code)
          states
      in
      let trusting =
        List.filter
          (fun (state : Diagnostic.span Prover.state) -> state.trusts_compiled_code)
          states
      in
      match (trusting, with_code "prover.ensures") with
      | [ template ], [ ensured ] ->
          if
            Diagnostic.Code.name (Prover template.code) <> "prover.requires"
            || template.failure <> None
          then fail "only the proof of the template's requires should trust compiled code";
          if ensured.failure <> None then fail "the proof of g's ensures should hold"
      | trusting, ensured ->
          fail "expected 1 state that trusts compiled code and 1 ensures state, got %d and %d"
            (List.length trusting) (List.length ensured))
