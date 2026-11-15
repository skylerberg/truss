let solver () =
  let find, add = Database.results ~kind:Store.Solver_answer in
  match Solver.find ~cache:{ find; add } () with
  | Ok solver -> solver
  | Error message -> Outcome.cannot_run "%s" message

let evaluator session packages =
  Evaluator.of_compiler (lazy (Compiler.create session packages Development))

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
