let solver =
  lazy (match Solver.find () with Ok solver -> solver | Error message -> failwith message)

let run_template_checks compile checks =
  List.map
    (fun ({ from_template; literals; clauses } as check : Prover.State.template_check) ->
      (check, Compile.run_template_check compile ~from_template ~literals ~clauses))
    checks

let verdicts compile database =
  let proofs = Database.prove database [ Codegen_support.example_file ] in
  Prover.decide
    ~runs:(run_template_checks compile (Database.list_template_checks proofs))
    (Database.make_proof_lookups database)
    (Lazy.force solver) (Database.list_proofs proofs)

let diagnostics compile database =
  Prover.list_diagnostics (verdicts compile database) Codegen_support.example_file

let proven_with_running ?results text =
  let database, compile = Codegen_support.load ?results text in
  diagnostics compile database

let messages diagnostics =
  String.concat "; " (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) diagnostics)

let fails_saying expected = function
  | [ (diagnostic : Diagnostic.t) ] ->
      if Diagnostic.Code.name diagnostic.code <> "prover.requires" then
        Codegen_support.fail "%s" (Diagnostic.Code.name diagnostic.code);
      if not (Substring.contains diagnostic.message expected) then
        Codegen_support.fail "%s" diagnostic.message
  | actual -> Codegen_support.fail "%d diagnostics: %s" (List.length actual) (messages actual)

let proven = function [] -> () | actual -> Codegen_support.fail "%s" (messages actual)

let results () : Compile.results =
  let stored = Hashtbl.create 4 in
  { find = Hashtbl.find_opt stored; add = Hashtbl.replace stored }

let shout = Fixtures.Evaluate.shout

let () =
  Codegen_support.test "a template check that holds is proven by running it" (fun () ->
      proven (proven_with_running (shout ^ Fixtures.Evaluate.shout_of_a_name)));
  Codegen_support.test "a template check that does not hold fails, saying it ran" (fun () ->
      fails_saying "Running it on this template's text gives `false`."
        (proven_with_running (shout ^ Fixtures.Evaluate.shout_of_capitals)));
  Codegen_support.test "a template check that reaches a todo fails, saying where" (fun () ->
      fails_saying "Running it on this template's text failed, so it is not known: todo reached"
        (proven_with_running Fixtures.Evaluate.shout_with_a_todo_check));
  Codegen_support.test "a check that reads a template's parts is not run" (fun () ->
      let database, compile =
        Codegen_support.load Fixtures.Evaluate.count_template_reading_its_parts
      in
      (match
         Database.list_template_checks (Database.prove database [ Codegen_support.example_file ])
       with
      | [] -> ()
      | checks -> Codegen_support.fail "%d template checks" (List.length checks));
      proven (diagnostics compile database));
  Codegen_support.test "a template check whose code has errors is not run" (fun () ->
      let database =
        Codegen_support.database
          (Codegen_support.example_package
             [ (Codegen_support.example_file, Fixtures.Evaluate.shout_with_an_ill_typed_check) ])
      in
      let proofs = Database.prove database [ Codegen_support.example_file ] in
      match Database.list_template_checks proofs with
      | [] ->
          fails_saying "which its tag requires."
            (diagnostics (Codegen_support.compile database) database)
      | checks -> Codegen_support.fail "%d template checks" (List.length checks))

let () =
  Codegen_support.test "a template's check is done again when the code it runs has changed"
    (fun () ->
      let results = results () in
      let use = Fixtures.Evaluate.shout_of_capitals in
      let refuses = "        quiet = false" in
      let accepts_all =
        match Substring.For_testing.find shout refuses with
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
  Codegen_support.test "a template check that timed out is run again on the next check" (fun () ->
      let results = results () in
      let database, _ = Codegen_support.load (shout ^ Fixtures.Evaluate.shout_of_a_greeting) in
      fails_saying "failed, so it is not known: it ran past the time limit of 0 ms"
        (diagnostics
           (Codegen_support.compile ~results ~evaluation_time_limit_ms:0 database)
           database);
      proven (diagnostics (Codegen_support.compile ~results database) database))

let () =
  Codegen_support.test "a state says whether its proof trusts compiled code" (fun () ->
      let database, compile =
        Codegen_support.load (shout ^ Fixtures.Evaluate.shout_of_a_name_and_an_identity)
      in
      let states = Prover.list_states (verdicts compile database) Codegen_support.example_file in
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
