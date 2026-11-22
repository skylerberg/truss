let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

let run_template_checks backend checks =
  List.map
    (fun ({ function_; literals } as check : Prover.Obligation.template_check) ->
      match Backend.evaluate_predicate backend ~function_ ~arguments:[ Literals literals ] with
      | Ok run -> (check, run)
      | Error message -> failwith message)
    checks

let compute_verdicts backend database =
  let proofs = Database.prove database [ Codegen_support.example_file ] in
  Prover.decide
    ~runs:(run_template_checks backend (Database.list_template_checks proofs))
    (Database.make_proof_lookups database)
    (Lazy.force solver) (Database.list_proofs proofs)

let list_diagnostics backend database =
  Prover.list_diagnostics (compute_verdicts backend database) Codegen_support.example_file

let prove_with_running ?results text =
  let database, backend = Codegen_support.load ?results text in
  list_diagnostics backend database

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

let make_results () : Backend.results =
  let stored = Hashtbl.create 4 in
  { find = Hashtbl.find_opt stored; add = Hashtbl.replace stored }

let shout = Fixtures.Evaluate.shout

let () =
  Codegen_support.test "a template check that holds is proven by running it" (fun () ->
      expect_proven (prove_with_running (shout ^ Fixtures.Evaluate.shout_of_a_name)));
  Codegen_support.test "a template whose check gives false fails every time it is reached"
    (fun () ->
      expect_failure_saying "This fails every time the code reaches it."
        (prove_with_running (shout ^ Fixtures.Evaluate.shout_of_capitals)));
  Codegen_support.test "a template check that reaches a todo fails, saying where" (fun () ->
      expect_failure_saying
        "Running `Shout.is_valid_template` on the template text `hey` failed, so its result is not \
         known: todo reached"
        (prove_with_running Fixtures.Evaluate.shout_with_a_todo_check));
  Codegen_support.test "a template check whose code has errors is not run" (fun () ->
      let database =
        Codegen_support.make_database
          (Codegen_support.make_example_package
             [ (Codegen_support.example_file, Fixtures.Evaluate.shout_with_an_ill_typed_check) ])
      in
      let proofs = Database.prove database [ Codegen_support.example_file ] in
      match Database.list_template_checks proofs with
      | [] ->
          expect_failure_saying "may not hold for this call to `Shout.from_template`"
            (list_diagnostics (Codegen_support.make_backend database) database)
      | checks -> Codegen_support.fail "%d template checks" (List.length checks))

let () =
  Codegen_support.test "a template's check is done again when the code it runs has changed"
    (fun () ->
      let results = make_results () in
      let use = Fixtures.Evaluate.shout_of_capitals in
      let accepts_all =
        String.replace_first ~sub:"          quiet = false" ~by:"          quiet = true" shout
      in
      expect_failure_saying "fails every time the code reaches it"
        (prove_with_running ~results (shout ^ use));
      expect_proven (prove_with_running ~results (accepts_all ^ use)))

let () =
  Codegen_support.test "a template check that used too much CPU time is run again on the next check"
    (fun () ->
      let results = make_results () in
      let database, _ = Codegen_support.load Fixtures.Evaluate.slow_check in
      expect_failure_saying "failed, so its result is not known: it used more than 5 ms of CPU time"
        (list_diagnostics
           (Codegen_support.make_backend ~results ~evaluation_cpu_time_limit_ms:5 database)
           database);
      expect_proven (list_diagnostics (Codegen_support.make_backend ~results database) database))

let () =
  Codegen_support.test "a release build reads the value that a development build evaluated"
    (fun () ->
      let results = make_results () in
      let database, _ = Codegen_support.load Fixtures.Lowering.constant_computed_by_a_long_loop in
      let spun = Lowered.Item.Constant (Top { module_ = Codegen_support.example; name = "spun" }) in
      let compile ?evaluation_cpu_time_limit_ms profile =
        ignore
          (Backend.For_testing.compile_fragment
             (Codegen_support.make_backend ~results ?evaluation_cpu_time_limit_ms ~profile database)
             spun)
      in
      compile Development;
      compile ~evaluation_cpu_time_limit_ms:5 Release)

let loaded_shout_of_a_name_and_an_identity =
  lazy (Codegen_support.load (shout ^ Fixtures.Evaluate.shout_of_a_name_and_an_identity))

let () =
  Codegen_support.test "a state says whether its proof trusts compiled code" (fun () ->
      let database, backend = Lazy.force loaded_shout_of_a_name_and_an_identity in
      let states =
        Prover.list_states (compute_verdicts backend database) Codegen_support.example_file
      in
      let with_code code =
        List.filter
          (fun (state : Source.span Prover.state) ->
            Diagnostic.Code.name (Prover state.site.code) = code)
          states
      in
      let trusting =
        List.filter (fun (state : Source.span Prover.state) -> state.trusts_compiled_code) states
      in
      match (trusting, with_code "prover.ensures") with
      | [ template ], [ ensured ] ->
          if
            Diagnostic.Code.name (Prover template.site.code) <> "prover.requires"
            || template.failure <> None
          then
            Codegen_support.fail
              "only the proof of the template's requires should trust compiled code";
          if ensured.failure <> None then
            Codegen_support.fail "the proof of g's ensures should hold"
      | trusting, ensured ->
          Codegen_support.fail
            "expected 1 state that trusts compiled code and 1 ensures state, got %d and %d"
            (List.length trusting) (List.length ensured));
  Codegen_support.test "the query of a template states the result of running its check" (fun () ->
      let database, backend = Lazy.force loaded_shout_of_a_name_and_an_identity in
      let proofs = Database.prove database [ Codegen_support.example_file ] in
      let runs = run_template_checks backend (Database.list_template_checks proofs) in
      let lookups = Database.make_proof_lookups database in
      let list_queries runs =
        Prover.For_testing.list_queries ~runs lookups (Database.list_proofs proofs)
          Codegen_support.example_file
      in
      let with_runs = list_queries runs and without_runs = list_queries [] in
      let states =
        Prover.list_states
          (Prover.decide ~runs lookups (Lazy.force solver) (Database.list_proofs proofs))
          Codegen_support.example_file
      in
      if List.length with_runs <> List.length states then
        Codegen_support.fail "listed %d queries for %d obligations" (List.length with_runs)
          (List.length states);
      match
        List.filter (fun (state : Source.span Prover.state) -> state.trusts_compiled_code) states
      with
      | [ template ] ->
          if List.assoc template.site with_runs = List.assoc template.site without_runs then
            Codegen_support.fail "the template's query is the same without the run of its check"
      | trusting ->
          Codegen_support.fail "expected 1 state that trusts compiled code, got %d"
            (List.length trusting))
