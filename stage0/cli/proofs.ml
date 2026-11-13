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

(* The prover's diagnostics of each of the files, and the state of each
   of its obligations, which a language server shows. A file is proven
   only once no other stage reports a diagnostic in it, since the prover
   reads the type checker's output; any other file has neither. The
   queries of every proven file are sent to the solver together, before
   the first file's results are read. *)
let checked (project : Project.t) files =
  match List.filter (fun file -> Database.diagnostics project.session file = []) files with
  | [] -> fun _ -> ([], [])
  | provable ->
      let solver = Lazy.force solver and evaluator = evaluator project in
      let record responses =
        List.iter
          (fun (key, response) -> Database.set project.session Prover.oracle_response key response)
          responses
      in
      Prover.solve_ahead ~evaluator ~record project.context solver provable;
      fun file ->
        if List.mem file provable then
          ( Prover.diagnostics ~evaluator ~record project.context solver file,
            Prover.states ~evaluator ~record project.context solver file )
        else ([], [])

let diagnostics (project : Project.t) files =
  let checked = checked project files in
  fun file -> fst (checked file)

(* Each hole in the proofs of the definitions that [main] reaches, a [todo]
   or a law that an impl leaves unshown: the definition, and the hole's
   file, as the current directory shows it, line, and column. A program
   with one cannot be built. *)
let holes_reached (project : Project.t) main =
  let reached = List.hd (Database.reachable project.session [ main ]) in
  List.concat_map
    (fun file ->
      List.concat_map
        (fun (declaration : Resolve.Names.declaration) ->
          match Query.demand project.context Prover.proof (Resolve.Names.key_of declaration) with
          | Obligations { holes; _ } when Path.Set.mem declaration.path reached ->
              List.filter_map
                (fun (home, (span : Syntax.span)) ->
                  Option.map
                    (fun (file, base) ->
                      let source = Project.source project file in
                      let line, column = Source.position source (base + span.start) in
                      (declaration.path, Project.shown (Source.path source), line, column))
                    (Query.demand project.context Resolve.Names.base home))
                holes
          | _ -> [])
        (Query.demand project.context Resolve.Names.declarations_in file))
    (Project.program_files project)
