open Codegen_support

let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

let run_template_checks compile checks =
  List.map
    (fun ({ from_template; literals; clauses } as check : Prover.State.template_check) ->
      (check, Compile.run_template_check compile ~from_template ~literals ~clauses))
    checks

let verdicts compile database =
  let proofs = Database.prove database [ example_file ] in
  Prover.decide
    ~runs:(run_template_checks compile (Database.list_template_checks proofs))
    (Database.make_proof_lookups database)
    (Lazy.force solver) (Database.list_proofs proofs)

let diagnostics compile database = Prover.list_diagnostics (verdicts compile database) example_file

let proven_with_running ?results text =
  let database, compile = load ?results text in
  diagnostics compile database

let messages diagnostics =
  String.concat "; " (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) diagnostics)

let fails_saying expected = function
  | [ (diagnostic : Diagnostic.t) ] ->
      if Diagnostic.Code.name diagnostic.code <> "prover.requires" then
        fail "%s" (Diagnostic.Code.name diagnostic.code);
      if not (Substring.contains diagnostic.message expected) then fail "%s" diagnostic.message
  | actual -> fail "%d diagnostics: %s" (List.length actual) (messages actual)

let proven = function [] -> () | actual -> fail "%s" (messages actual)

let results () : Compile.results =
  let stored = Hashtbl.create 4 in
  { find = Hashtbl.find_opt stored; add = Hashtbl.replace stored }

let shout = Fixtures.Evaluate.shout

let () =
  test "a template check that holds is proven by running it" (fun () ->
      proven
        (proven_with_running
           (shout ^ Fixtures.Evaluate.template_check_that_holds_is_proven_by_running_it)));
  test "a template check that does not hold fails, saying it ran" (fun () ->
      fails_saying "Running it on this template's text gives `false`."
        (proven_with_running
           (shout ^ Fixtures.Evaluate.template_check_that_does_not_hold_fails_saying_it)));
  test "a template check that reaches a todo fails, saying where" (fun () ->
      fails_saying "Running it on this template's text failed, so it is not known: todo reached"
        (proven_with_running Fixtures.Evaluate.template_check_that_reaches_a_todo_fails_saying));
  test "a check that reads a template's parts is not run" (fun () ->
      let database, compile =
        load Fixtures.Evaluate.check_that_reads_a_templates_parts_is_not_run
      in
      (match Database.list_template_checks (Database.prove database [ example_file ]) with
      | [] -> ()
      | checks -> fail "%d template checks" (List.length checks));
      proven (diagnostics compile database));
  test "a template check whose code has errors is not run" (fun () ->
      let database =
        database
          (example_package
             [ (example_file, Fixtures.Evaluate.template_check_whose_code_has_errors_is_not_run) ])
      in
      let proofs = Database.prove database [ example_file ] in
      match Database.list_template_checks proofs with
      | [] -> fails_saying "which its tag requires." (diagnostics (compile database) database)
      | checks -> fail "%d template checks" (List.length checks))

let () =
  test "a template's check is done again when the code it runs has changed" (fun () ->
      let results = results () in
      let use = Fixtures.Evaluate.use in
      let refuses = "        quiet = false" in
      let accepts_all =
        match Substring.find shout refuses with
        | Some at ->
            String.sub shout 0 at ^ "        quiet = true"
            ^ String.sub shout
                (at + String.length refuses)
                (String.length shout - at - String.length refuses)
        | None -> failwith ("shout has no " ^ refuses)
      in
      fails_saying "gives `false`" (proven_with_running ~results (shout ^ use));
      proven (proven_with_running ~results (accepts_all ^ use)))

let () =
  test "a template check that timed out is run again on the next check" (fun () ->
      let results = results () in
      let database, _ =
        load (shout ^ Fixtures.Evaluate.template_check_that_timed_out_is_run_again_on_the)
      in
      fails_saying "failed, so it is not known: it ran past the time limit of 0 ms"
        (diagnostics (compile ~results ~evaluation_time_limit_ms:0 database) database);
      proven (diagnostics (compile ~results database) database))

let () =
  test "a state says whether its proof trusts compiled code" (fun () ->
      let database, compile =
        load (shout ^ Fixtures.Evaluate.state_says_whether_its_proof_trusts_compiled_code)
      in
      let states = Prover.list_states (verdicts compile database) example_file in
      let with_code code =
        List.filter
          (fun (state : Source.span Prover.state) ->
            Diagnostic.Code.name (Prover state.code) = code)
          states
      in
      let trusting =
        List.filter (fun (state : Source.span Prover.state) -> state.trusts_compiled_code) states
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
