(* The prover, as commands run it: each definition's obligations are sent
   to the pinned solver, and each tagged template's check is decided by
   running it. *)

(* The solver that [TRUSS_Z3] names, or else [z3]. Proving requires it, as
   building requires a C compiler. Its answers are cached in the store. *)
let solver () =
  match Solver.find ~cache:(Filename.concat (Database.store_directory ()) "proofs") () with
  | Ok solver -> solver
  | Error message -> Outcome.cannot_run "%s" message

(* The evaluator runs code through the compiler that builds programs. The
   compiler is created only when a proof needs a run. *)
let evaluator session packages =
  Evaluator.of_compiler (lazy (Compiler.create session packages Development))

(* The prover's diagnostics of each of the files, and the state of each
   of its obligations, which a language server shows. A file is proven
   only once no other stage reports a diagnostic in it, since the prover
   reads the type checker's output; any other file has neither. The
   queries of every proven file are sent to the solver together, before
   the first file's results are read. *)
let checked session packages files =
  match List.filter (fun file -> Database.diagnostics session file = []) files with
  | [] -> fun _ -> ([], [])
  | provable ->
      let solver = solver () and evaluator = evaluator session packages in
      let record responses =
        List.iter
          (fun (key, response) -> Database.set session Prover.oracle_response key response)
          responses
      in
      Prover.solve_ahead ~evaluator ~record (Database.context session) solver provable;
      fun file ->
        if List.mem file provable then
          ( Prover.diagnostics ~evaluator ~record (Database.context session) solver file,
            Prover.states ~evaluator ~record (Database.context session) solver file )
        else ([], [])

let diagnostics session packages files =
  let checked = checked session packages files in
  fun file -> fst (checked file)

let holes_reached session packages main =
  let reached = List.hd (Database.reachable session [ main ]) in
  List.concat_map
    (fun file ->
      List.concat_map
        (fun (declaration : Resolve.Names.declaration) ->
          match
            Query.demand (Database.context session) Prover.proof (Resolve.Names.key_of declaration)
          with
          | Obligations { holes; _ } when Path.Set.mem declaration.path reached ->
              List.filter_map
                (fun (home, (span : Syntax.span)) ->
                  Option.map
                    (fun (file, base) ->
                      let source = Command_packages.source session packages file in
                      let line, column = Source.position source (base + span.start) in
                      (declaration.path, Shown_path.shown (Source.path source), line, column))
                    (Query.demand (Database.context session) Resolve.Names.base home))
                holes
          | _ -> [])
        (Query.demand (Database.context session) Resolve.Names.declarations_in file))
    (Command_packages.program_files session packages)
