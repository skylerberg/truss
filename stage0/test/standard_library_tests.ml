(* The tests of the standard library's source: each module checks through
   every stage with no diagnostic, and proves. *)

open Harness

(* CI proves the library on runners of its own, beside the other tests. *)
let () =
  if Sys.getenv_opt "TRUSS_SKIP_LIBRARY_PROOFS" = Some "1" then begin
    print_endline "skipped: the library's proofs run in jobs of their own";
    exit 0
  end

(* CI proves the library on several runners at once. [TRUSS_PROOF_SHARE]
   names this run's share as [index/count], and the run checks and proves
   only its own modules: what they use of the others is worked out as it is
   needed. The modules are dealt out by weight, heaviest first, each to the
   share with the least so far, so that the shares take about as long as
   each other. A module's weight is what proving it was measured to cost,
   which [Proof_weights] lists. The letters of a module's source do not
   tell: a module of loops with invariants costs several times what
   straight-line code of the same length does. A module that was not
   measured weighs by its letters, which leaves out tables of numbers:
   they are large and have nothing to prove. *)
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

let weight ((module_ : Path.module_), source) =
  match List.assoc_opt (Path.show_module module_) Proof_weights.weights with
  | Some measured -> measured
  | None -> max 1 (letters source / Proof_weights.letters_for_one)

let modules =
  match share with
  | None -> Standard_library.modules
  | Some (index, count) ->
      let totals = Array.make count 0 in
      let weighed = List.map (fun entry -> (weight entry, entry)) Standard_library.modules in
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
      List.filter (fun entry -> List.memq entry mine) Standard_library.modules

(* Solver answers are kept by the text of the query, the solver's version
   and its limit, so with a directory to keep them in, a run solves only
   the queries that the last run did not. *)
let solver =
  match Solver.find ?cache:(Sys.getenv_opt "TRUSS_SOLVER_CACHE") () with
  | Ok solver -> solver
  | Error message ->
      prerr_endline message;
      exit 1

(* [TRUSS_PROOF_WEIGHTS=1] measures the weights: each module is checked and
   proven by itself, and the run prints [Proof_weights] again, with each
   module's processor time, the solver's included, in hundredths of a
   second. With no directory of solver answers, that is what a module
   costs a run that starts from nothing. *)
let measuring = Sys.getenv_opt "TRUSS_PROOF_WEIGHTS" = Some "1"

let processor_time () =
  let times = Unix.times () in
  times.tms_utime +. times.tms_stime +. times.tms_cutime +. times.tms_cstime

let measure database ~tell =
  let measured =
    List.map
      (fun ((module_ : Path.module_), source) ->
        let start = processor_time () in
        if Type_checker.diagnostics database module_ = [] then
          ignore (Prover.diagnostics ~tell database solver module_);
        let spent = int_of_float (Float.round ((processor_time () -. start) *. 100.)) in
        (Path.show_module module_, max 1 spent, letters source))
      Standard_library.modules
  in
  let total_weight = List.fold_left (fun total (_, weight, _) -> total + weight) 0 measured in
  let total_letters = List.fold_left (fun total (_, _, letters) -> total + letters) 0 measured in
  print_endline "let weights =\n  [";
  List.iter (fun (name, weight, _) -> Printf.printf "    (%S, %d);\n" name weight) measured;
  Printf.printf "  ]\n\nlet letters_for_one = %d\n" (max 1 (total_letters / max 1 total_weight))

(* [TRUSS_PROOF_STATE] names a state of the library in the code database's
   store. A run that names one starts from what the last such run saved,
   works out only what an edit to the library changed, and saves the
   result. A run that names none starts from the sources. *)
let session =
  match Sys.getenv_opt "TRUSS_PROOF_STATE" with
  | None | Some "" -> None
  | Some name -> (
      match Database.open_library name with
      | Ok session -> Some session
      | Error message ->
          prerr_endline message;
          exit 1)

let () =
  let engine =
    match session with
    | Some session -> Database.Testing.engine session
    | None ->
        let engine = Engine.create () in
        Database.load_standard engine;
        engine
  in
  (* One engine holds every module's results, so an audit after each
     module's test would compute the whole library again for each of them.
     It is audited once, when every module is checked and before any is
     proven: the prover's own tests audit its queries, and auditing them
     here would translate every proof of the library a second time. *)
  Engine.skip_audit engine;
  let database =
    match session with Some session -> Database.context session | None -> Engine.context engine
  in
  let tell said =
    match session with
    | Some session -> List.iter (fun (key, told) -> Database.set session Prover.told key told) said
    | None -> Support.tell database said
  in
  if measuring then begin
    measure database ~tell;
    exit 0
  end;
  let checked =
    List.map
      (fun ((module_ : Path.module_), _) -> (module_, Type_checker.diagnostics database module_))
      modules
  in
  test "the code database kept every result of checking the standard library current" (fun () ->
      List.iter (fun problem -> fail "%s" problem) (Engine.audit engine));
  Prover.solve_ahead ~tell database solver
    (List.filter_map (fun (module_, errors) -> if errors = [] then Some module_ else None) checked);
  List.iter
    (fun ((module_ : Path.module_), errors) ->
      test
        (Printf.sprintf "%s checks cleanly and proves" (Path.show_module module_))
        (fun () ->
          let source = (Query.demand database Workspace.file module_).source in
          let report =
            List.iter (fun diagnostic -> fail "%s" (Diagnostic.render source diagnostic))
          in
          match errors with
          | [] -> report (Prover.diagnostics ~tell database solver module_)
          | errors -> report errors))
    checked;
  Option.iter Database.save_session session

let () = finish ()
