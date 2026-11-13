(* Measuring how long the standard library's proofs take to solve. This is a
   tool, not a test.

     dune exec stage0/tools/proof_benchmark/proof_benchmark.exe

   It checks every module, then proves each module that checks, one after
   another, with no answers kept from before, so every query is solved. For
   each module it prints how many queries the solver ran and how long
   proving took, slowest first, and then the totals. Proving a module
   solves its queries together, one for each core, as the command line
   does. *)

(* The oracles' responses, recorded in the engine, as the database does for
   a session. *)
let record database responses =
  let engine = Engine.of_context database in
  List.iter (fun (key, response) -> Engine.set engine Prover.oracle_response key response) responses

let () =
  let solver =
    match Solver.find () with
    | Ok solver -> solver
    | Error message ->
        prerr_endline message;
        exit 1
  in
  let engine = Engine.create () in
  Engine.skip_audit engine;
  let database = Engine.context engine in
  Database.load_standard engine;
  let timed =
    List.filter_map
      (fun ((file : Path.file), _) ->
        match Checks.diagnostics database file with
        | _ :: _ -> None
        | [] ->
            let solved = Solver.solved solver in
            let start = Unix.gettimeofday () in
            let failed =
              List.length (Prover.diagnostics ~record:(record database) database solver file)
            in
            Some
              ( Path.show_file file,
                Solver.solved solver - solved,
                Unix.gettimeofday () -. start,
                failed ))
      Standard_library.files
  in
  List.iter
    (fun (name, queries, seconds, failed) ->
      Printf.printf "%8.2f s %6d queries  %s%s\n" seconds queries name
        (if failed = 0 then "" else Printf.sprintf " (%d not proven)" failed))
    (List.sort (fun (_, _, first, _) (_, _, second, _) -> compare second first) timed);
  let queries = List.fold_left (fun total (_, queries, _, _) -> total + queries) 0 timed in
  let seconds = List.fold_left (fun total (_, _, seconds, _) -> total +. seconds) 0. timed in
  Printf.printf "%8.2f s %6d queries  in %d files\n" seconds queries (List.length timed)
