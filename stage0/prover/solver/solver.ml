let version = "5.3.3"
let steps = 1_000_000
let cardinality_bounds = [ 2; 3; 4 ]
let raise_bug format = Compiler_bug.raise_bug ~stage:"Solver" format

type cache = { find : string -> string option; add : string -> string -> unit }
type t = { program : string; cache : cache option; mutable queries_run : int }

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
      if String.starts_with ~prefix:expected output then Ok { program; cache; queries_run = 0 }
      else
        Error
          (Printf.sprintf
             "The prover is pinned to Z3 %s, since another version can answer differently, but \
              `%s` is %s."
             version program (String.trim output))
  | _, _, errors -> Error (Printf.sprintf "`%s --version` failed: %s" program (String.trim errors))

type answer = Proven | Counterexample of (Logic.symbol * string) list | Unknown

let header =
  Printf.sprintf
    "(set-option :produce-models true)\n\
     (set-option :smt.random_seed 0)\n\
     (set-option :sat.random_seed 0)\n\
     (set-option :rlimit %d)\n"
    steps

let key_of_text text =
  Logic.hash
    (Printf.sprintf "z3 %s\nunknown retried with cardinality bounds %s\n%s%s" version
       (String.concat ", " (List.map string_of_int cardinality_bounds))
       header text)

let hash_query query = key_of_text (Logic.show_query query)

type sexp = Atom of string | List of sexp list

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
  key : string;
  requested : (Logic.symbol * string) list;
  value_arguments : string list;
}

type canonical = Proven_canonical | Values of (string * string) list | Unknown_canonical

let answers : (string, canonical) Hashtbl.t = Hashtbl.create 256
let small_model_bounds : (string, int) Hashtbl.t = Hashtbl.create 16
let lock = Mutex.create ()
let run_locked work = Mutex.protect lock work
let request_key_of_text text value_arguments = key_of_text text ^ String.concat "," value_arguments

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
  {
    key = request_key_of_text (Logic.rendered_text rendering) value_arguments;
    requested;
    value_arguments;
  }

let request_key request = request.key

let read request = function
  | Proven_canonical -> Proven
  | Unknown_canonical -> Unknown
  | Values pairs ->
      Counterexample
        (List.filter_map
           (fun (symbol, canonical) ->
             Option.map (fun value -> (symbol, value)) (List.assoc_opt canonical pairs))
           request.requested)

let print_canonical = function
  | Proven_canonical -> "proven\n"
  | Unknown_canonical -> "unknown\n"
  | Values pairs ->
      "counterexample\n"
      ^ String.concat ""
          (List.map (fun (canonical, value) -> Printf.sprintf "%s %s\n" canonical value) pairs)

let parse_canonical text =
  match String.split_on_char '\n' text with
  | "proven" :: _ -> Some Proven_canonical
  | "unknown" :: _ -> Some Unknown_canonical
  | "counterexample" :: lines -> Some (Values (List.filter_map (String.split_first ~sep:" ") lines))
  | _ -> None

let find_known_answer solver key =
  run_locked (fun () ->
      match Hashtbl.find_opt answers key with
      | Some answer -> Some answer
      | None -> (
          match
            Option.bind solver.cache (fun cache -> Option.bind (cache.find key) parse_canonical)
          with
          | Some answer ->
              Hashtbl.replace answers key answer;
              Some answer
          | None -> None))

let run_check solver request text =
  let input =
    header ^ text
    ^
    if request.requested = [] then ""
    else Printf.sprintf "(get-value (%s))\n" (String.concat " " request.value_arguments)
  in
  run_locked (fun () -> solver.queries_run <- solver.queries_run + 1);
  let status, output, errors = Process.run ~input solver.program [ "-in"; "-smt2" ] in
  match parse_sexps output with
  | Atom "unsat" :: _ -> Proven_canonical
  | Atom "sat" :: rest ->
      Values
        (match rest with
        | List pairs :: _ ->
            List.take (List.length request.requested)
              (List.mapi
                 (fun index pair ->
                   match (pair, List.nth_opt request.requested index) with
                   | List [ _; value ], Some (_, canonical) -> Some (canonical, show_sexp value)
                   | _ -> None)
                 pairs)
            |> List.filter_map Fun.id
        | _ -> [])
  | Atom "unknown" :: _ -> Unknown_canonical
  | _ ->
      raise_bug
        "Z3 exited with status %d without answering a query, writing `%s` to stdout and `%s` to \
         stderr"
        status (String.trim output) (String.trim errors)

let search_small_models solver request query ~text_key =
  let rec search_from = function
    | [] -> Unknown_canonical
    | cardinality_bound :: larger_bounds -> (
        match run_check solver request (Logic.show_query ~cardinality_bound query) with
        | Values _ as counterexample ->
            run_locked (fun () -> Hashtbl.replace small_model_bounds text_key cardinality_bound);
            counterexample
        | Proven_canonical -> search_from larger_bounds
        | Unknown_canonical -> Unknown_canonical)
  in
  search_from cardinality_bounds

let solve solver (request, query) =
  match find_known_answer solver request.key with
  | Some answer -> answer
  | None ->
      let text = Logic.show_query query in
      if request_key_of_text text request.value_arguments <> request.key then
        raise_bug "the query is not the one its request was made from";
      let text_key = key_of_text text in
      let answer =
        match run_locked (fun () -> Hashtbl.find_opt small_model_bounds text_key) with
        | Some cardinality_bound ->
            run_check solver request (Logic.show_query ~cardinality_bound query)
        | None -> (
            match run_check solver request text with
            | Unknown_canonical when Logic.has_uninterpreted_sort query ->
                search_small_models solver request query ~text_key
            | (Proven_canonical | Values _ | Unknown_canonical) as answer -> answer)
      in
      run_locked (fun () ->
          Hashtbl.replace answers request.key answer;
          Option.iter (fun cache -> cache.add request.key (print_canonical answer)) solver.cache);
      answer

let solve_all solver requests =
  let requests = Array.of_list requests in
  let answers = Array.make (Array.length requests) Unknown_canonical in
  let next = Atomic.make 0 in
  let rec run_worker () =
    let index = Atomic.fetch_and_add next 1 in
    if index < Array.length requests then begin
      answers.(index) <- solve solver requests.(index);
      run_worker ()
    end
  in
  let helper_domains = min (Array.length requests) (Domain.recommended_domain_count ()) - 1 in
  let domains = List.init (max 0 helper_domains) (fun _ -> Domain.spawn run_worker) in
  run_worker ();
  List.iter Domain.join domains;
  Array.to_list answers

let count_queries_run solver = run_locked (fun () -> solver.queries_run)

module For_testing = struct
  let hash_query = hash_query
end
