(* The tests of the standard library's source: each module checks through
   every stage with no diagnostic, and proves. *)

open Harness

(* CI proves the library in several processes at once, one for each core
   of several runners. [TRUSS_PROOF_SHARE] names this process's share as
   [index/count], and the process checks and proves only its own modules,
   and computes the parts of other modules they use on demand. The modules
   are dealt out by weight, heaviest first, each to the share with the
   least so far, so that the shares take about as long as each other. A
   module's weight is its measured proof cost, which [Proof_weights]
   lists. The letters of a module's source do not tell: a module of loops
   with invariants costs several times as much as straight-line code of
   the same length. A module that was not measured weighs by its letters,
   which leaves out tables of numbers: they are large and have nothing to
   prove. *)
let share =
  match Sys.getenv_opt "TRUSS_PROOF_SHARE" with
  | None | Some "" -> None
  | Some text -> (
      match List.map int_of_string_opt (String.split_on_char '/' text) with
      | [ Some index; Some count ] when 0 <= index && index < count -> Some (index, count)
      | _ ->
          prerr_endline ("TRUSS_PROOF_SHARE is `index/count`, such as `0/2`, not `" ^ text ^ "`.");
          exit 2)

let letters source =
  String.fold_left
    (fun letters character ->
      match character with 'a' .. 'z' | 'A' .. 'Z' -> letters + 1 | _ -> letters)
    0 source

(* Each module of the library, with its files' texts. A module is the unit
   that a test checks and proves. *)
let library =
  List.map
    (fun module_ ->
      ( module_,
        List.filter (fun ((file : Path.file), _) -> file.module_ = module_) Standard_library.files
      ))
    (List.sort_uniq compare
       (List.map (fun ((file : Path.file), _) -> file.module_) Standard_library.files))

let module_letters files = List.fold_left (fun total (_, text) -> total + letters text) 0 files

let weight ((module_ : Path.module_), files) =
  match List.assoc_opt (Path.show_module module_) Proof_weights.weights with
  | Some measured -> measured
  | None -> max 1 (module_letters files / Proof_weights.letters_for_one)

let test_name (module_ : Path.module_) =
  Printf.sprintf "%s checks cleanly and proves" (Path.show_module module_)

(* With [TRUSS_TEST] set, only the modules whose tests it names are checked
   and proven. *)
let modules =
  match share with
  | None -> List.filter (fun (module_, _) -> wanted (test_name module_)) library
  | Some (index, count) ->
      let totals = Array.make count 0 in
      let weighed = List.map (fun entry -> (weight entry, entry)) library in
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

(* Solver answers are kept in the store by the text of the query, the
   solver's version and its limit, so a run solves only the queries that no
   earlier run solved, whatever compiler that run was. *)
let solver =
  let find, add = Database.results ~kind:"solver" in
  match Solver.find ~cache:{ find; add } () with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

(* [TRUSS_PROOF_WEIGHTS] measures weights. Its value is [all], or the names
   of modules with commas between them, such as
   [standard::regex,standard::math]. Each module it names is checked and
   proven by itself, and the run prints [Proof_weights] again, with the
   processor time of each measured module, the solver's included, in
   hundredths of a second, and the recorded weight of every other module.
   Measure with a store that holds every query's answer, as CI's runs
   start with: there a module's cost is translating it, which the solver's
   cost from nothing would hide. *)
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

let processor_time () =
  let times = Unix.times () in
  times.tms_utime +. times.tms_stime +. times.tms_cutime +. times.tms_cstime

let measure database ~record ~is_measured =
  let measured =
    List.map
      (fun (((module_ : Path.module_), files) as entry) ->
        let name = Path.show_module module_ in
        if is_measured name then begin
          let start = processor_time () in
          List.iter
            (fun (file, _) ->
              if Checks.diagnostics database file = [] then
                ignore (Prover.diagnostics ~record database solver file))
            files;
          let spent = int_of_float (Float.round ((processor_time () -. start) *. 100.)) in
          (name, max 1 spent, module_letters files)
        end
        else (name, weight entry, module_letters files))
      library
  in
  let total_weight = List.fold_left (fun total (_, weight, _) -> total + weight) 0 measured in
  let total_letters = List.fold_left (fun total (_, _, letters) -> total + letters) 0 measured in
  print_endline "let weights =\n  [";
  List.iter (fun (name, weight, _) -> Printf.printf "    (%S, %d);\n" name weight) measured;
  Printf.printf "  ]\n\nlet letters_for_one = %d\n" (max 1 (total_letters / max 1 total_weight))

(* A run prints how long each stage and each module took, and how many
   queries the solver ran and did not read from its kept answers, so the
   log of a slow job names the slow modules. *)
let timed label work =
  let start = Unix.gettimeofday () in
  let runs_before = Solver.queries_run solver in
  let result = work () in
  Printf.printf "%6.1f s, %d queries solved: %s\n%!"
    (Unix.gettimeofday () -. start)
    (Solver.queries_run solver - runs_before)
    label;
  result

(* [TRUSS_PROOF_STATE] names a state of the library in the code database's
   store. A run that names one starts from the state the last such run
   saved, recomputes only the dependents of an edit to the library, and
   saves the result. A run that names none starts from the sources. *)
let session =
  match Sys.getenv_opt "TRUSS_PROOF_STATE" with
  | None | Some "" -> None
  | Some name -> (
      match Database.For_testing.open_library name with
      | Ok session -> Some session
      | Error message ->
          prerr_endline message;
          exit 1)

let () =
  let engine =
    match session with
    | Some session -> Database.For_testing.engine session
    | None ->
        let engine = Engine.create () in
        Database.load_standard engine;
        engine
  in
  (* One engine holds every module's results, so an audit after each
     module's test would compute the whole library again for each of them.
     It is audited once, when every module is checked and before any is
     proven: the prover's own tests audit its queries, and auditing them
     here would translate every proof of the library a second time. An
     engine opened from a kept state holds the last run's proofs already,
     so its audit stops before the proofs. *)
  Engine.skip_audit engine;
  let database =
    match session with Some session -> Database.context session | None -> Engine.context engine
  in
  let record responses =
    match session with
    | Some session ->
        List.iter
          (fun (key, response) -> Database.set session Prover.oracle_response key response)
          responses
    | None -> Support.record database responses
  in
  Option.iter
    (fun is_measured ->
      measure database ~record ~is_measured;
      exit 0)
    measured_modules;
  let checked =
    timed "type checking" (fun () ->
        List.map
          (fun (module_, files) ->
            (module_, List.map (fun (file, _) -> (file, Checks.diagnostics database file)) files))
          modules)
  in
  test "the code database kept every result of checking the standard library current" (fun () ->
      timed "auditing the code database" (fun () ->
          let before = Option.map (fun _ -> Phases.proofs) session in
          List.iter (fun problem -> fail "%s" problem) (Engine.audit ?before engine)));
  timed "solving ahead" (fun () ->
      Prover.solve_ahead ~record database solver
        (List.concat_map
           (fun (_, files) ->
             List.filter_map (fun (file, errors) -> if errors = [] then Some file else None) files)
           checked));
  List.iter
    (fun ((module_ : Path.module_), files) ->
      test (test_name module_) (fun () ->
          timed (Path.show_module module_) (fun () ->
              List.iter
                (fun (file, errors) ->
                  let source = Query.demand database Packages.source file in
                  List.iter
                    (fun diagnostic -> fail "%s" (Diagnostic.render source diagnostic))
                    (match errors with
                    | [] -> Prover.diagnostics ~record database solver file
                    | errors -> errors))
                files)))
    checked;
  timed "saving the state" (fun () -> Option.iter Database.save_session session);
  (* A run that saves a state starts no background process, and the
     background process is what keeps the store within its budget. Without
     this, CI's store would keep the state of every compiler it ran. *)
  Option.iter (fun _ -> timed "collecting the store" Database.For_testing.collect_store) session
