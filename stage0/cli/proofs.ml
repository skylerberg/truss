(* The prover, as commands run it: each definition's obligations are sent
   to the pinned solver, and each tagged template's check is decided by
   running it. *)

(* The solver, found once. Proving requires it, as building requires a C
   compiler. Its answers are cached in the store. *)
let solver =
  lazy
    (match Solver.find ~cache:(Filename.concat (Database.store_directory ()) "proofs") () with
    | Ok solver -> solver
    | Error message -> Project.cannot_run "%s" message)

(* The evaluator runs code through the compiler that builds programs. The
   compiler is created only when a proof needs a run, and run results are
   cached as test results are. *)
let evaluator (project : Project.t) =
  Evaluator.of_compiler ~results:(Compiler.test_results ())
    (lazy (Compiler.create project Development))

(* The prover's diagnostics of each of the modules, and the state of each
   of its obligations, which a language server shows. A module is proven
   only once no other stage reports a diagnostic in it, since the prover
   reads the type checker's output; any other module has neither. The
   queries of every proven module are sent to the solver together, before
   the first module's results are read. *)
let checked (project : Project.t) modules =
  match List.filter (fun module_ -> Database.diagnostics project.session module_ = []) modules with
  | [] -> fun _ -> ([], [])
  | provable ->
      let solver = Lazy.force solver and evaluator = evaluator project in
      let record responses =
        List.iter
          (fun (key, response) -> Database.set project.session Prover.oracle_response key response)
          responses
      in
      Prover.solve_ahead ~evaluator ~record project.context solver provable;
      fun module_ ->
        if List.mem module_ provable then
          ( Prover.diagnostics ~evaluator ~record project.context solver module_,
            Prover.states ~evaluator ~record project.context solver module_ )
        else ([], [])

let diagnostics (project : Project.t) modules =
  let checked = checked project modules in
  fun module_ -> fst (checked module_)

(* Each definition that [main] reaches and whose proofs have a hole. A
   program with such a definition cannot be built. *)
let holes_reached (project : Project.t) main =
  let reached = List.hd (Database.reachable project.session [ main ]) in
  List.concat_map
    (fun module_ ->
      List.filter_map
        (fun (declaration : Resolve.Names.declaration) ->
          match Query.demand project.context Prover.proof (Resolve.Names.key_of declaration) with
          | Obligations { holes = _ :: _; _ } when Path.Set.mem declaration.path reached ->
              Some declaration.path
          | _ -> None)
        (Query.demand project.context Resolve.Names.declarations module_))
    (Project.program_modules project)
