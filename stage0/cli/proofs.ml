(* The prover's part of a command: each definition's obligations, solved by
   the pinned solver, with a tagged template's check decided by running it. *)

(* The solver, found once. A check cannot be done without it, as a build
   cannot without a C compiler. Its answers are kept in the store. *)
let solver =
  lazy
    (match Solver.find ~cache:(Filename.concat (Database.store_directory ()) "proofs") () with
    | Ok solver -> solver
    | Error message -> Project.cannot_run "%s" message)

(* The evaluator, through the compiler that builds programs, made only if
   a proof asks for a run, with results kept as test results are. *)
let evaluator (project : Project.t) =
  Evaluator.of_compiler ~results:(Compiler.test_results ())
    (lazy (Compiler.create project Development))

(* The proofs of each of the modules, by module, with every module's
   queries solved first, together: its diagnostics, and the state of each
   of its obligations, which a language server shows. *)
let checked (project : Project.t) modules =
  let solver = Lazy.force solver and evaluator = evaluator project in
  let record responses =
    List.iter
      (fun (key, response) -> Database.set project.session Prover.oracle_response key response)
      responses
  in
  Prover.solve_ahead ~evaluator ~record project.context solver modules;
  fun module_ ->
    ( Prover.diagnostics ~evaluator ~record project.context solver module_,
      Prover.states ~evaluator ~record project.context solver module_ )

let diagnostics (project : Project.t) modules =
  let checked = checked project modules in
  fun module_ -> fst (checked module_)

(* Each definition [main] can reach whose proofs have a hole, which a
   program cannot be built with. *)
let holes_reached (project : Project.t) main =
  let seen = Project.reachable (Database.dependencies project.session) main in
  List.concat_map
    (fun module_ ->
      List.filter_map
        (fun (declaration : Resolve.Names.declaration) ->
          match Query.demand project.context Prover.proof (Resolve.Names.key_of declaration) with
          | Obligations { holes = _ :: _; _ } when Hashtbl.mem seen declaration.path ->
              Some declaration.path
          | _ -> None)
        (Query.demand project.context Resolve.Names.declarations module_))
    (Project.program_modules project)
