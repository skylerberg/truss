let share =
  match Sys.getenv_opt "TRUSS_PROOF_SHARE" with
  | None | Some "" -> None
  | Some text -> (
      match List.map int_of_string_opt (String.split_on_char '/' text) with
      | [ Some index; Some count ] when 0 <= index && index < count -> Some (index, count)
      | _ ->
          prerr_endline ("TRUSS_PROOF_SHARE is `index/count`, such as `0/2`, not `" ^ text ^ "`.");
          exit 2)

let count_letters source =
  String.fold_left
    (fun letters character ->
      match character with 'a' .. 'z' | 'A' .. 'Z' -> letters + 1 | _ -> letters)
    0 source

let library =
  List.map
    (fun module_ ->
      ( module_,
        List.filter (fun ((file : Path.file), _) -> file.module_ = module_) Standard_library.files
      ))
    (List.sort_uniq compare
       (List.map (fun ((file : Path.file), _) -> file.module_) Standard_library.files))

let count_module_letters files =
  List.fold_left (fun total (_, text) -> total + count_letters text) 0 files

let weigh ((module_ : Path.module_), files) =
  match List.assoc_opt (Path.show_module module_) Proof_weights.weights with
  | Some measured -> measured
  | None -> max 1 (count_module_letters files / Proof_weights.letters_for_one)

let test_name (module_ : Path.module_) =
  Printf.sprintf "%s checks cleanly and proves" (Path.show_module module_)

let modules =
  match share with
  | None -> List.filter (fun (module_, _) -> Harness.is_wanted (test_name module_)) library
  | Some (index, count) ->
      let totals = Array.make count 0 in
      let weighed = List.map (fun entry -> (weigh entry, entry)) library in
      let mine =
        List.fold_left
          (fun mine (weight, entry) ->
            let least = ref 0 in
            Array.iteri (fun other total -> if total < totals.(!least) then least := other) totals;
            totals.(!least) <- totals.(!least) + weight;
            if !least = index then entry :: mine else mine)
          []
          (List.stable_sort (fun (first, _) (second, _) -> compare second first) weighed)
      in
      List.filter (fun entry -> List.memq entry mine) library

let solver =
  let cache = Workspace.open_cache () in
  match
    Solver.find
      ~cache:
        {
          find = (fun key -> Cache.find_result cache ~kind:Solver_answer ~key);
          add = (fun key value -> Cache.add_result cache ~kind:Solver_answer ~key value);
        }
      ()
  with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

let measured_modules =
  match Sys.getenv_opt "TRUSS_PROOF_WEIGHTS" with
  | None | Some "" -> None
  | Some "all" -> Some (fun _ -> true)
  | Some names ->
      let names = String.split_on_char ',' names in
      let known = List.map (fun (module_, _) -> Path.show_module module_) library in
      List.iter
        (fun name ->
          if not (List.mem name known) then begin
            prerr_endline
              ("TRUSS_PROOF_WEIGHTS names `" ^ name ^ "`, which is not a module of the library.");
            exit 2
          end)
        names;
      Some (fun name -> List.mem name names)

let read_processor_time () =
  let times = Unix.times () in
  times.tms_utime +. times.tms_stime +. times.tms_cutime +. times.tms_cstime

let prove_files database files =
  Prover.decide ~runs:[]
    (Database.make_proof_lookups database)
    solver
    (Database.list_proofs (Database.prove database files))

let is_always_read_kind : type a. a Database.Part.stored -> bool = function
  | Parsed _ | Resolved _ | Trait_header _ | Interface _ | Signature_check _ | Contract _
  | Checked_body _ | Body_mir _ | Contract_mir _ | Mir_call_edges _ ->
      true
  | Namespace _ | Folded_integer _ | Header _ | Derived_interface _ | Type_facts _ | Grant _
  | Generated_mir _ | Usage _ | Ownership _ | Import_check _ | Package_check _ | Call_edges _
  | Recursion_group _ | Proof _ | Lowered _ | Test_key _ ->
      false

let is_always_read (Database.Part.Any part) = is_always_read_kind part

let measure database ~is_measured =
  let measured =
    List.map
      (fun (((module_ : Path.module_), files) as entry) ->
        let name = Path.show_module module_ in
        if is_measured name then begin
          let start = read_processor_time () in
          ignore
            (prove_files database
               (List.filter_map
                  (fun (file, _) ->
                    if Database.list_file_diagnostics database file = [] then Some file else None)
                  files));
          let spent = int_of_float (Float.round ((read_processor_time () -. start) *. 100.)) in
          (name, max 1 spent, count_module_letters files)
        end
        else (name, weigh entry, count_module_letters files))
      library
  in
  let total_weight = List.fold_left (fun total (_, weight, _) -> total + weight) 0 measured in
  let total_letters = List.fold_left (fun total (_, _, letters) -> total + letters) 0 measured in
  print_endline "let weights =\n  [";
  List.iter (fun (name, weight, _) -> Printf.printf "    (%S, %d);\n" name weight) measured;
  Printf.printf "  ]\n\nlet letters_for_one = %d\n" (max 1 (total_letters / max 1 total_weight))

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
  let make_database () =
    Database.create
      [ { name = Path.standard_package; dependencies = []; files = Standard_library.files } ]
  in
  Option.iter
    (fun is_measured ->
      measure (make_database ()) ~is_measured;
      exit 0)
    measured_modules;
  let database = run_timed "type checking" make_database in
  Harness.test "every part whose kind is always read has a reader" (fun () ->
      List.iter
        (fun part ->
          if is_always_read part then
            Harness.fail "no part reads %s" (Database.Part.show (Stored part)))
        (Database.For_testing.list_unread_parts database [ Path.standard_package ]));
  let checked =
    List.map
      (fun (module_, files) ->
        ( module_,
          List.map (fun (file, _) -> (file, Database.list_file_diagnostics database file)) files ))
      modules
  in
  let verdicts =
    run_timed "proving" (fun () ->
        prove_files database
          (List.concat_map
             (fun (_, files) ->
               List.filter_map (fun (file, errors) -> if errors = [] then Some file else None) files)
             checked))
  in
  List.iter
    (fun ((module_ : Path.module_), files) ->
      Harness.test (test_name module_) (fun () ->
          run_timed (Path.show_module module_) (fun () ->
              List.iter
                (fun (file, errors) ->
                  let source =
                    Source.create ~path:(Path.show_file file)
                      (List.assoc file Standard_library.files)
                  in
                  List.iter
                    (fun diagnostic -> Harness.fail "%s" (Diagnostic.render source diagnostic))
                    (match errors with
                    | [] -> Prover.list_diagnostics verdicts file
                    | errors -> errors))
                files)))
    checked;
  run_timed "collecting the cache" Workspace.For_testing.collect_cache
