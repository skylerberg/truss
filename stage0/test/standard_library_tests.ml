let library =
  List.map
    (fun module_ ->
      ( module_,
        List.filter (fun ((file : Path.file), _) -> file.module_ = module_) Standard_library.files
      ))
    (List.sort_uniq compare
       (List.map (fun ((file : Path.file), _) -> file.module_) Standard_library.files))

let solver =
  match Solver.find () with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

let run_timed label work =
  let start = Unix.gettimeofday () in
  let runs_before = Solver.For_testing.count_queries_run solver in
  let result = work () in
  Printf.printf "%6.1f s, %d queries solved: %s\n%!"
    (Unix.gettimeofday () -. start)
    (Solver.For_testing.count_queries_run solver - runs_before)
    label;
  result

let () =
  let database =
    run_timed "type checking" (fun () ->
        Database.create
          [ { name = Path.standard_package; dependencies = []; files = Standard_library.files } ])
  in
  Harness.test "every fact whose kind is always read has a reader" (fun () ->
      match Database.For_testing.list_unread database with
      | [] -> ()
      | unread -> Harness.fail "no unit reads %s" (String.concat ", " unread));
  let list_clean files =
    List.filter_map
      (fun (file, _) ->
        if Database.list_file_diagnostics database file = [] then Some file else None)
      files
  in
  List.iter
    (fun ((module_ : Path.module_), files) ->
      let name = Path.show_module module_ in
      Harness.test (name ^ " checks cleanly and proves") (fun () ->
          run_timed name (fun () ->
              Database.decide
                (Database.prove database (In_files (list_clean files)))
                (Lazy.from_val solver);
              List.iter
                (fun (file, text) ->
                  let source = Source.create ~path:(Path.show_file file) text in
                  List.iter
                    (fun diagnostic ->
                      Harness.fail "%s" (Diagnostic.render ~is_colored:false source diagnostic))
                    (match Database.list_file_diagnostics database file with
                    | [] -> Database.list_proof_diagnostics database file
                    | errors -> errors))
                files));
      Harness.test (name ^ "'s core forms and MIR keep their invariants") (fun () ->
          List.iter
            (fun file ->
              ignore (Core_lint.check_file database file);
              Mir_lint.check_file database file)
            (list_clean files)))
    library
