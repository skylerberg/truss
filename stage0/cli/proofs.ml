(* The prover's part of a command: each definition's obligations, solved by
   the pinned solver, with a tagged template's check decided by running it.
   See PROVER.md and CLI.md, "Checking". *)

(* The solver, found once. A check cannot be done without it, as a build
   cannot without a C compiler. Its answers are kept in the store. *)
let solver =
  lazy
    (match Solver.find ~cache:(Filename.concat (Database.store_directory ()) "proofs") () with
    | Ok solver -> solver
    | Error message -> Project.cannot_run "%s" message)

(* Running a template's check, through the compiler that builds programs,
   made only if a template asks for it, with results kept as test results
   are. A check that cannot be built is left to the solver. *)
let evaluate (project : Project.t) =
  let compile = lazy (Compiler.create project Development) in
  fun (evaluation : Prover.Translate.evaluation) : Prover.evaluated option ->
    match
      Compile.check_template ~results:(Database.test_results ()) (Lazy.force compile)
        ~time_limit:10_000 ~from_template:evaluation.from_template ~texts:evaluation.texts
    with
    | Ok (Ran found) ->
        Option.map
          (fun holds -> if holds then Prover.Holds else Prover.Fails)
          (List.assoc_opt evaluation.clause found)
    | Ok Ran_too_long -> Some Too_long
    | Error _ -> None

(* The proofs' diagnostics of each file, by module. *)
let diagnostics (project : Project.t) =
  let solver = Lazy.force solver and evaluate = evaluate project in
  fun module_ -> Prover.diagnostics ~evaluate project.context solver module_

(* Each definition [main] can reach whose proofs have a hole, which a
   program cannot be built with, as PROVER.md's "Holes" says. *)
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
    (Project.modules project)
