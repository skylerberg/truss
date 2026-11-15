let () =
  let solver =
    match Solver.find () with
    | Ok solver -> solver
    | Error message ->
        prerr_endline message;
        exit 1
  in
  let standard : Project.package =
    { name = Path.standard_package; dependencies = []; files = Standard_library.files }
  in
  let timed =
    List.filter_map
      (fun ((file : Path.file), _) ->
        let pipeline = Pipeline.create [ standard ] in
        Pipeline.check pipeline [ file.module_.package ];
        match Pipeline.file_diagnostics pipeline file with
        | _ :: _ -> None
        | [] ->
            let runs_before = Solver.queries_run solver in
            let start = Unix.gettimeofday () in
            let failed =
              List.length
                (Pipeline.diagnostics
                   (Pipeline.decide ~runs:[] solver (Pipeline.prove pipeline [ file ]))
                   file)
            in
            Some
              ( Path.show_file file,
                Solver.queries_run solver - runs_before,
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
