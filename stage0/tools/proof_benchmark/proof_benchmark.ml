let () =
  let solver =
    match Solver.find () with
    | Ok solver -> solver
    | Error message ->
        prerr_endline message;
        exit 1
  in
  let modules =
    List.sort_uniq compare
      (List.map
         (fun ((file : Path.file), _) -> Path.show_module file.module_)
         Standard_library.files)
  in
  let wanted = List.tl (Array.to_list Sys.argv) in
  (match List.filter (fun name -> not (List.mem name modules)) wanted with
  | [] -> ()
  | unknown ->
      prerr_endline ("Not modules of the standard library: " ^ String.concat ", " unknown);
      exit 2);
  let is_wanted ((file : Path.file), _) =
    wanted = [] || List.mem (Path.show_module file.module_) wanted
  in
  let database =
    Database.create
      [ { name = Path.standard_package; dependencies = []; files = Standard_library.files } ]
  in
  let show channel (name, queries, seconds, failed) =
    Printf.fprintf channel "%8.2f s %6d queries  %s%s\n%!" seconds queries name
      (if failed = 0 then "" else Printf.sprintf " (%d not proven)" failed)
  in
  let timed =
    List.filter_map
      (fun ((file : Path.file), _) ->
        match Database.list_file_diagnostics database file with
        | _ :: _ -> None
        | [] ->
            let runs_before = Solver.For_testing.count_queries_run solver in
            let start = Unix.gettimeofday () in
            let failed =
              List.length
                (Prover.list_diagnostics
                   (Prover.decide ~runs:[]
                      (Database.make_proof_lookups database)
                      solver
                      (Database.list_proofs (Database.prove database [ file ])))
                   file)
            in
            let row =
              ( Path.show_file file,
                Solver.For_testing.count_queries_run solver - runs_before,
                Unix.gettimeofday () -. start,
                failed )
            in
            show stderr row;
            Some row)
      (List.filter is_wanted Standard_library.files)
  in
  List.iter (show stdout)
    (List.sort (fun (_, _, first, _) (_, _, second, _) -> compare second first) timed);
  let queries = List.fold_left (fun total (_, queries, _, _) -> total + queries) 0 timed in
  let seconds = List.fold_left (fun total (_, _, seconds, _) -> total +. seconds) 0. timed in
  Printf.printf "%8.2f s %6d queries  in %d files\n" seconds queries (List.length timed)
