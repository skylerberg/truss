let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

let decide backend database =
  let proofs = Database.prove database (In_files [ Codegen_support.example_file ]) in
  ignore (Backend.evaluate backend (Database.list_evaluations proofs));
  Database.decide proofs solver

let list_diagnostics backend database =
  decide backend database;
  Database.list_proof_diagnostics database Codegen_support.example_file

let list_states backend database =
  decide backend database;
  Database.list_proof_states database Codegen_support.example_file

let prove_with_running text =
  let database, backend = Codegen_support.load text in
  list_diagnostics backend database

let show_messages diagnostics =
  String.concat "; " (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) diagnostics)

let expect_failure_saying expected = function
  | [ (diagnostic : Diagnostic.t) ] ->
      if Diagnostic.Code.name diagnostic.code <> "prover.assertion" then
        Codegen_support.fail "%s" (Diagnostic.Code.name diagnostic.code);
      if not (String.includes ~affix:expected diagnostic.message) then
        Codegen_support.fail "%s" diagnostic.message
  | actual -> Codegen_support.fail "%d diagnostics: %s" (List.length actual) (show_messages actual)

let expect_proven = function [] -> () | actual -> Codegen_support.fail "%s" (show_messages actual)
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
        "The call to `Shout.is_valid_template` that `Shout\"hey\"` makes may not give `true`. Its \
         evaluation stopped, so its result is not known: todo reached"
        (prove_with_running Fixtures.Evaluate.shout_with_a_todo_check));
  Codegen_support.test "a template check whose code has errors is not run" (fun () ->
      let database =
        Codegen_support.make_database
          (Codegen_support.make_example_package
             [ (Codegen_support.example_file, Fixtures.Evaluate.shout_with_an_ill_typed_check) ])
      in
      let proofs = Database.prove database (In_files [ Codegen_support.example_file ]) in
      match Database.list_evaluations proofs with
      | [] ->
          expect_failure_saying
            "The call to `Shout.is_valid_template` that `Shout\"hey\"` makes may not give `true`."
            (list_diagnostics (Codegen_support.make_backend database) database)
      | checks -> Codegen_support.fail "%d template checks" (List.length checks))

let () =
  Codegen_support.test "a template's check is done again when the code it runs has changed"
    (fun () ->
      let use = Fixtures.Evaluate.shout_of_capitals in
      let accepts_all =
        String.replace_first ~sub:"          quiet = false" ~by:"          quiet = true" shout
      in
      let database, backend = Codegen_support.load (shout ^ use) in
      expect_failure_saying "fails every time the code reaches it"
        (list_diagnostics backend database);
      Database.update database [ (Codegen_support.example_file, Some (accepts_all ^ use)) ];
      expect_proven (list_diagnostics (Codegen_support.make_backend database) database))

let () =
  Codegen_support.test "a release build reads the value that a development build evaluated"
    (fun () ->
      let database, _ = Codegen_support.load Fixtures.Lowering.constant_computed_by_a_long_loop in
      let spun = Lowered.Item.Constant (Top { module_ = Codegen_support.example; name = "spun" }) in
      let compile ?evaluation_cpu_time_limit_ms profile =
        ignore
          (Backend.For_testing.compile_fragment
             (Codegen_support.make_backend ?evaluation_cpu_time_limit_ms ~profile database)
             spun)
      in
      compile Development;
      compile ~evaluation_cpu_time_limit_ms:5 Release)

let () =
  Codegen_support.test
    "a command reads the result that an earlier command recorded, and builds no program" (fun () ->
      let database, _ = Codegen_support.load Fixtures.Lowering.constant_computed_by_a_long_loop in
      let spun = Lowered.Item.Constant (Top { module_ = Codegen_support.example; name = "spun" }) in
      let compile () =
        ignore (Backend.For_testing.compile_fragment (Codegen_support.make_backend database) spun)
      in
      compile ();
      let built = Backend.For_testing.count_built_programs () in
      compile ();
      Codegen_support.expect_int ~expected:built (Backend.For_testing.count_built_programs ()))

let () =
  Codegen_support.test
    "a constant whose evaluation uses too much CPU time is an error of its own check, and is \
     evaluated again on the next check" (fun () ->
      let database, _ = Codegen_support.load Fixtures.Lowering.constant_computed_by_a_long_loop in
      (match
         list_diagnostics
           (Codegen_support.make_backend ~evaluation_cpu_time_limit_ms:5 database)
           database
       with
      | [ diagnostic ] ->
          Codegen_support.expect_string ~expected:"prover.evaluation"
            (Diagnostic.Code.name diagnostic.code);
          Codegen_support.expect_string
            ~expected:
              "The value of `example.spun` cannot be computed: it used more than 5 ms of CPU time"
            diagnostic.message
      | actual ->
          Codegen_support.fail "%d diagnostics: %s" (List.length actual) (show_messages actual));
      expect_proven (list_diagnostics (Codegen_support.make_backend database) database))

let () =
  Codegen_support.test
    "the evaluations of a check share one program for each layer of constants that read each other"
    (fun () ->
      let database, _ = Codegen_support.load Fixtures.Evaluate.constants_in_two_layers in
      let built_before = Backend.For_testing.count_built_programs () in
      expect_proven (list_diagnostics (Codegen_support.make_backend database) database);
      match Backend.For_testing.count_built_programs () - built_before with
      | 2 -> ()
      | built -> Codegen_support.fail "%d programs for three evaluations in two layers" built)

let load_shout_of_a_name_and_an_identity () =
  Codegen_support.load (shout ^ Fixtures.Evaluate.shout_of_a_name_and_an_identity)

let () =
  Codegen_support.test "a state says whether its proof trusts compiled code" (fun () ->
      let database, backend = load_shout_of_a_name_and_an_identity () in
      let states = list_states backend database in
      let with_code code =
        List.filter (fun (state : Database.proof_state) -> state.site.code = code) states
      in
      let trusting =
        List.filter (fun (state : Database.proof_state) -> state.trusts_compiled_code) states
      in
      match (trusting, with_code "prover.ensures") with
      | [ first; second ], [ ensured ] ->
          if
            List.sort compare
              (List.map (fun (state : Database.proof_state) -> state.site.code) [ first; second ])
            <> [ "prover.assertion"; "prover.requires" ]
            || (not first.is_proven) || not second.is_proven
          then
            Codegen_support.fail
              "only the template's check and the requires that it proves should trust compiled code";
          if not ensured.is_proven then Codegen_support.fail "the proof of g's ensures should hold"
      | trusting, ensured ->
          Codegen_support.fail
            "expected 2 states that trust compiled code and 1 ensures state, got %d and %d"
            (List.length trusting) (List.length ensured));
  Codegen_support.test "the query of a template states the result of running its check" (fun () ->
      let database, backend = load_shout_of_a_name_and_an_identity () in
      let proofs = Database.prove database (In_files [ Codegen_support.example_file ]) in
      let without_runs = Database.For_testing.list_queries proofs in
      ignore (Backend.evaluate backend (Database.list_evaluations proofs));
      let with_runs = Database.For_testing.list_queries proofs in
      Database.decide proofs solver;
      let states = Database.list_proof_states database Codegen_support.example_file in
      if List.length with_runs <> List.length states then
        Codegen_support.fail "listed %d queries for %d obligations" (List.length with_runs)
          (List.length states);
      match
        List.filter (fun (state : Database.proof_state) -> state.trusts_compiled_code) states
      with
      | [ _; _ ] as trusting ->
          List.iter
            (fun (state : Database.proof_state) ->
              if List.assoc state.site with_runs = List.assoc state.site without_runs then
                Codegen_support.fail "a query is the same without the run of the template's check")
            trusting
      | trusting ->
          Codegen_support.fail "expected 2 states that trust compiled code, got %d"
            (List.length trusting))
