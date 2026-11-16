let version = "5.3.3"
let steps = 1_000_000
let cardinality_bounds = [ 2; 3; 4 ]
let raise_bug format = Compiler_bug.raise_bug ~stage:"Solver" format

type cache = { find : string -> string option; add : string -> string -> unit }

type t = {
  program : string;
  cache : cache option;
  entries : (string, string) Hashtbl.t;
  lock : Mutex.t;
  mutable queries_run : int;
}

let find ?cache () =
  let program =
    match Sys.getenv_opt "TRUSS_Z3" with Some program when program <> "" -> program | _ -> "z3"
  in
  match Process.run program [ "--version" ] with
  | exception Unix.Unix_error _ ->
      Error
        (Printf.sprintf
           "The prover needs Z3 %s, and `%s` could not be run. Install it, or set TRUSS_Z3 to its \
            path."
           version program)
  | 0, output, _ ->
      let expected = "Z3 version " ^ version in
      if String.starts_with ~prefix:expected output then
        Ok { program; cache; entries = Hashtbl.create 256; lock = Mutex.create (); queries_run = 0 }
      else
        Error
          (Printf.sprintf
             "The prover is pinned to Z3 %s, since another version can answer differently, but \
              `%s` is %s."
             version program (String.trim output))
  | _, _, errors -> Error (Printf.sprintf "`%s --version` failed: %s" program (String.trim errors))

let header =
  Printf.sprintf
    "(set-option :produce-models true)\n\
     (set-option :smt.random_seed 0)\n\
     (set-option :sat.random_seed 0)\n\
     (set-option :rlimit %d)\n"
    steps

let key_of_text text =
  Logic.hash
    (Printf.sprintf
       "z3 %s\nstatus of the query, with unknown retried at cardinality bounds %s\n%s%s" version
       (String.concat ", " (List.map string_of_int cardinality_bounds))
       header text)

let hash_query query = key_of_text (Logic.show_query query)

type sexp = Atom of string | List of sexp list
type answer = Proven | Counterexample of (Logic.symbol * sexp) list | Unknown

let parse_sexps text =
  let length = String.length text in
  let rec skip position =
    if
      position < length
      && (text.[position] = ' '
         || text.[position] = '\n'
         || text.[position] = '\t'
         || text.[position] = '\r')
    then skip (position + 1)
    else position
  in
  let rec parse_one position =
    let position = skip position in
    if position >= length then None
    else if text.[position] = '(' then
      let rec parse_items position acc =
        let position = skip position in
        if position >= length then (List (List.rev acc), position)
        else if text.[position] = ')' then (List (List.rev acc), position + 1)
        else
          match parse_one position with
          | Some (item, position) -> parse_items position (item :: acc)
          | None -> (List (List.rev acc), position)
      in
      Some (parse_items (position + 1) [])
    else
      let stop = ref position in
      while !stop < length && not (List.mem text.[!stop] [ ' '; '\n'; '\t'; '\r'; '('; ')' ]) do
        incr stop
      done;
      Some (Atom (String.sub text position (!stop - position)), !stop)
  in
  let rec parse_all position acc =
    match parse_one position with
    | Some (item, position) -> parse_all position (item :: acc)
    | None -> List.rev acc
  in
  parse_all 0 []

let rec show_sexp = function
  | Atom atom -> atom
  | List items -> "(" ^ String.concat " " (List.map show_sexp items) ^ ")"

type request = {
  text_key : string;
  values_key : string;
  requested : (Logic.symbol * string) list;
  value_arguments : string list;
}

type status = Unsatisfiable | Satisfiable of { cardinality_bound : int option } | Undecided

let run_locked solver work = Mutex.protect solver.lock work

let request ?(symbols = []) ?(terms = []) query =
  let rendering = Logic.render query in
  let named = Logic.list_symbols rendering in
  let requested_symbols =
    List.filter_map
      (fun symbol ->
        List.assoc_opt symbol named
        |> Option.map (fun canonical -> ((symbol, canonical), canonical)))
      symbols
  in
  let requested_terms =
    List.filter_map
      (fun (name, term) ->
        Logic.render_term rendering term |> Option.map (fun text -> (name, text)))
      terms
    |> List.mapi (fun index (name, text) -> ((name, Printf.sprintf "#%d" index), text))
  in
  let requested = List.map fst (requested_symbols @ requested_terms)
  and value_arguments = List.map snd (requested_symbols @ requested_terms) in
  let text_key = key_of_text (Logic.rendered_text rendering) in
  {
    text_key;
    values_key = text_key ^ "/" ^ String.concat "," value_arguments;
    requested;
    value_arguments;
  }

let print_status = function
  | Unsatisfiable -> "proven\n"
  | Undecided -> "unknown\n"
  | Satisfiable { cardinality_bound = None } -> "model\n"
  | Satisfiable { cardinality_bound = Some bound } -> Printf.sprintf "model %d\n" bound

let parse_status text =
  match String.split_on_char ' ' (String.trim text) with
  | [ "proven" ] -> Some Unsatisfiable
  | [ "unknown" ] -> Some Undecided
  | [ "model" ] -> Some (Satisfiable { cardinality_bound = None })
  | [ "model"; bound ] ->
      Option.map
        (fun bound -> Satisfiable { cardinality_bound = Some bound })
        (int_of_string_opt bound)
  | _ -> None

let print_values values =
  String.concat ""
    (List.map
       (fun (canonical, value) -> Printf.sprintf "%s %s\n" canonical (show_sexp value))
       values)

let parse_values text =
  List.filter_map
    (fun line ->
      match String.split_first ~sep:" " line with
      | Some (canonical, value) -> (
          match parse_sexps value with [ value ] -> Some (canonical, value) | _ -> None)
      | None -> None)
    (String.split_on_char '\n' text)

let find_entry solver key =
  run_locked solver (fun () ->
      match Hashtbl.find_opt solver.entries key with
      | Some entry -> Some entry
      | None -> (
          match Option.bind solver.cache (fun cache -> cache.find key) with
          | Some entry ->
              Hashtbl.replace solver.entries key entry;
              Some entry
          | None -> None))

let add_entry solver key entry =
  run_locked solver (fun () ->
      Hashtbl.replace solver.entries key entry;
      Option.iter (fun cache -> cache.add key entry) solver.cache)

let run_check solver request ?cardinality_bound text =
  let input =
    header ^ text
    ^
    if request.requested = [] then ""
    else Printf.sprintf "(get-value (%s))\n" (String.concat " " request.value_arguments)
  in
  run_locked solver (fun () -> solver.queries_run <- solver.queries_run + 1);
  let status, output, errors = Process.run ~input solver.program [ "-in"; "-smt2" ] in
  match parse_sexps output with
  | Atom "unsat" :: _ -> (Unsatisfiable, [])
  | Atom "sat" :: rest ->
      ( Satisfiable { cardinality_bound },
        match rest with
        | List pairs :: _ ->
            List.take (List.length request.requested)
              (List.mapi
                 (fun index pair ->
                   match (pair, List.nth_opt request.requested index) with
                   | List [ _; value ], Some (_, canonical) -> Some (canonical, value)
                   | _ -> None)
                 pairs)
            |> List.filter_map Fun.id
        | _ -> [] )
  | Atom "unknown" :: _ -> (Undecided, [])
  | _ ->
      raise_bug
        "Z3 exited with status %d without answering a query, writing `%s` to stdout and `%s` to \
         stderr"
        status (String.trim output) (String.trim errors)

let run_bounded_check solver request query cardinality_bound =
  run_check solver request ~cardinality_bound (Logic.show_query ~cardinality_bound query)

let search_model solver request query text =
  let rec search_from = function
    | [] -> (Undecided, [])
    | cardinality_bound :: larger_bounds -> (
        match run_bounded_check solver request query cardinality_bound with
        | Unsatisfiable, _ -> search_from larger_bounds
        | ((Satisfiable _ | Undecided), _) as outcome -> outcome)
  in
  match run_check solver request text with
  | Undecided, _ when Logic.has_uninterpreted_sort query -> search_from cardinality_bounds
  | outcome -> outcome

let solve solver (request, query) =
  let render_checked () =
    let text = Logic.show_query query in
    if key_of_text text <> request.text_key then
      raise_bug "the query is not the one its request was made from";
    text
  in
  let status, values =
    match Option.bind (find_entry solver request.text_key) parse_status with
    | Some (Satisfiable { cardinality_bound } as status) when request.requested <> [] -> (
        match find_entry solver request.values_key with
        | Some entry -> (status, parse_values entry)
        | None -> (
            let text = render_checked () in
            match
              match cardinality_bound with
              | Some cardinality_bound -> run_bounded_check solver request query cardinality_bound
              | None -> run_check solver request text
            with
            | Satisfiable _, values ->
                add_entry solver request.values_key (print_values values);
                (status, values)
            | (Unsatisfiable | Undecided), _ ->
                raise_bug "a query that had a model has none when it is solved again"))
    | Some status -> (status, [])
    | None ->
        let ((status, values) as outcome) = search_model solver request query (render_checked ()) in
        add_entry solver request.text_key (print_status status);
        (match status with
        | Satisfiable _ when request.requested <> [] ->
            add_entry solver request.values_key (print_values values)
        | Satisfiable _ | Unsatisfiable | Undecided -> ());
        outcome
  in
  match status with
  | Unsatisfiable -> Proven
  | Undecided -> Unknown
  | Satisfiable _ ->
      Counterexample
        (List.filter_map
           (fun (symbol, canonical) ->
             Option.map (fun value -> (symbol, value)) (List.assoc_opt canonical values))
           request.requested)

let run_workers count work =
  let next = Atomic.make 0 in
  let rec run_worker () =
    let index = Atomic.fetch_and_add next 1 in
    if index < count then begin
      work index;
      run_worker ()
    end
  in
  let helper_domains = min count (Domain.recommended_domain_count ()) - 1 in
  let domains = List.init (max 0 helper_domains) (fun _ -> Domain.spawn run_worker) in
  run_worker ();
  List.iter Domain.join domains

let solve_all solver requests =
  let solve_distinct key_of =
    let distinct = Hashtbl.create 64 in
    List.iter
      (fun ((request, _) as asked) ->
        if not (Hashtbl.mem distinct (key_of request)) then
          Hashtbl.replace distinct (key_of request) asked)
      requests;
    let distinct = Array.of_seq (Hashtbl.to_seq_values distinct) in
    run_workers (Array.length distinct) (fun index -> ignore (solve solver distinct.(index)))
  in
  solve_distinct (fun request -> request.text_key);
  solve_distinct (fun request -> request.values_key);
  List.map (solve solver) requests

let count_queries_run solver = run_locked solver (fun () -> solver.queries_run)

module For_testing = struct
  let hash_query = hash_query
end
