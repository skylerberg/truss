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

(* Running compiled code, through the compiler that builds programs, made
   only if a proof asks for it, with results kept as test results are. *)
let running (project : Project.t) =
  Running.through ~results:(Database.test_results ()) (lazy (Compiler.create project Development))

(* The proofs' diagnostics of each file, by module. *)
let diagnostics (project : Project.t) =
  let solver = Lazy.force solver and running = running project in
  fun module_ -> Prover.diagnostics ~running project.context solver module_

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
