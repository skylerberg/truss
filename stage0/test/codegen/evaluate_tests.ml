let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

let run_literal_checks compile checks =
  List.map
    (fun check -> (check, Compile.run_literal_check compile (Database.convert_literal_check check)))
    checks

let compute_verdicts compile database =
  let proofs = Database.prove database [ Codegen_support.example_file ] in
  Prover.decide
    ~runs:(run_literal_checks compile (Database.list_literal_checks proofs))
    (Database.make_proof_lookups database)
    (Lazy.force solver) (Database.list_proofs proofs)

let list_diagnostics compile database =
  Prover.list_diagnostics (compute_verdicts compile database) Codegen_support.example_file

let prove_with_running ?results text =
  let database, compile = Codegen_support.load ?results text in
  list_diagnostics compile database

let show_messages diagnostics =
  String.concat "; " (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) diagnostics)

let expect_failure_saying expected = function
  | [ (diagnostic : Diagnostic.t) ] ->
      if Diagnostic.Code.name diagnostic.code <> "prover.requires" then
        Codegen_support.fail "%s" (Diagnostic.Code.name diagnostic.code);
      if not (String.includes ~affix:expected diagnostic.message) then
        Codegen_support.fail "%s" diagnostic.message
  | actual -> Codegen_support.fail "%d diagnostics: %s" (List.length actual) (show_messages actual)

let expect_proven = function [] -> () | actual -> Codegen_support.fail "%s" (show_messages actual)

let make_results () : Compile.results =
  let stored = Hashtbl.create 4 in
  { find = Hashtbl.find_opt stored; add = Hashtbl.replace stored }

let shout = Fixtures.Evaluate.shout

let () =
  Codegen_support.test "a template check that holds is proven by running it" (fun () ->
      expect_proven (prove_with_running (shout ^ Fixtures.Evaluate.shout_of_a_name)));
  Codegen_support.test "a template check that does not hold fails, saying it ran" (fun () ->
      expect_failure_saying "Running it on this template's text gives `false`."
        (prove_with_running (shout ^ Fixtures.Evaluate.shout_of_capitals)));
  Codegen_support.test "a template check that reaches a todo fails, saying where" (fun () ->
      expect_failure_saying
        "Running it on this template's text failed, so it is not known: todo reached"
        (prove_with_running Fixtures.Evaluate.shout_with_a_todo_check));
  Codegen_support.test "a check that reads a template's parts is not run" (fun () ->
      let database, compile =
        Codegen_support.load Fixtures.Evaluate.count_template_reading_its_parts
      in
      (match
         Database.list_literal_checks (Database.prove database [ Codegen_support.example_file ])
       with
      | [] -> ()
      | checks -> Codegen_support.fail "%d template checks" (List.length checks));
      expect_proven (list_diagnostics compile database));
  Codegen_support.test "a template check whose code has errors is not run" (fun () ->
      let database =
        Codegen_support.make_database
          (Codegen_support.make_example_package
             [ (Codegen_support.example_file, Fixtures.Evaluate.shout_with_an_ill_typed_check) ])
      in
      let proofs = Database.prove database [ Codegen_support.example_file ] in
      match Database.list_literal_checks proofs with
      | [] ->
          expect_failure_saying "which its tag requires."
            (list_diagnostics (Codegen_support.compile database) database)
      | checks -> Codegen_support.fail "%d template checks" (List.length checks))

let () =
  Codegen_support.test "a constant map literal's distinct keys are proven by running the check"
    (fun () -> expect_proven (prove_with_running Fixtures.Evaluate.map_literal_of_forty_eight_keys));
  Codegen_support.test "a constant map literal with a repeated key fails, saying it ran" (fun () ->
      expect_failure_saying "Running it on this literal gives `false`."
        (prove_with_running Fixtures.Evaluate.map_literal_with_a_repeated_constant_key);
      expect_failure_saying "Running it on this literal gives `false`."
        (prove_with_running Fixtures.Evaluate.sorted_map_literal_with_a_repeated_constant_key));
  Codegen_support.test
    "a constant literal in a field's default, a constant, and a lambda is proven by running"
    (fun () ->
      expect_proven
        (prove_with_running Fixtures.Evaluate.map_literals_in_a_default_a_constant_and_a_lambda));
  Codegen_support.test "a literal's check is done again when its keys have changed" (fun () ->
      let results = make_results () in
      expect_failure_saying "gives `false`"
        (prove_with_running ~results Fixtures.Evaluate.map_literal_with_a_repeated_constant_key);
      expect_proven
        (prove_with_running ~results Fixtures.Evaluate.map_literal_with_distinct_constant_keys));
  Codegen_support.test "a map literal with a value that is not constant is not run" (fun () ->
      let database, compile =
        Codegen_support.load Fixtures.Evaluate.map_literal_with_a_value_that_is_not_constant
      in
      (match
         Database.list_literal_checks (Database.prove database [ Codegen_support.example_file ])
       with
      | [] -> ()
      | checks -> Codegen_support.fail "%d literal checks" (List.length checks));
      expect_proven (list_diagnostics compile database))

let () =
  Codegen_support.test "a template's check is done again when the code it runs has changed"
    (fun () ->
      let results = make_results () in
      let use = Fixtures.Evaluate.shout_of_capitals in
      let accepts_all =
        String.replace_first ~sub:"        quiet = false" ~by:"        quiet = true" shout
      in
      expect_failure_saying "gives `false`" (prove_with_running ~results (shout ^ use));
      expect_proven (prove_with_running ~results (accepts_all ^ use)))

let () =
  Codegen_support.test "a template check that timed out is run again on the next check" (fun () ->
      let results = make_results () in
      let database, _ = Codegen_support.load (shout ^ Fixtures.Evaluate.shout_of_a_greeting) in
      expect_failure_saying "failed, so it is not known: it ran past the time limit of 0 ms"
        (list_diagnostics
           (Codegen_support.compile ~results ~evaluation_time_limit_ms:0 database)
           database);
      expect_proven (list_diagnostics (Codegen_support.compile ~results database) database))

let () =
  Codegen_support.test "a state says whether its proof trusts compiled code" (fun () ->
      let database, compile =
        Codegen_support.load (shout ^ Fixtures.Evaluate.shout_of_a_name_and_an_identity)
      in
      let states =
        Prover.list_states (compute_verdicts compile database) Codegen_support.example_file
      in
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
          then
            Codegen_support.fail
              "only the proof of the template's requires should trust compiled code";
          if ensured.failure <> None then
            Codegen_support.fail "the proof of g's ensures should hold"
      | trusting, ensured ->
          Codegen_support.fail
            "expected 1 state that trusts compiled code and 1 ensures state, got %d and %d"
            (List.length trusting) (List.length ensured))
