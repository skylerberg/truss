let version = "5.3.3"
let steps = 1_000_000
let cardinality_bounds = [ 2; 3; 4 ]
let raise_bug format = Compiler_bug.raise_bug ~stage:"Solver" format

type t = { run_z3 : string -> string; queries_run : int Atomic.t }
type sexp = Atom of string | List of sexp list
type unknown = Out_of_steps | Incomplete of string
type answer = Proven | Counterexample of (Logic.symbol * sexp) list | Unknown of unknown

let find_string_literal_end text position =
  let length = String.length text in
  let rec scan index =
    if index >= length then length
    else if text.[index] <> '"' then scan (index + 1)
    else if index + 1 < length && text.[index + 1] = '"' then scan (index + 2)
    else index + 1
  in
  scan (position + 1)

let read_string_literal literal =
  let length = String.length literal in
  if length < 2 || literal.[0] <> '"' || literal.[length - 1] <> '"' then
    raise_bug "Z3 wrote `%s` where a string literal belongs" literal
  else
    let buffer = Buffer.create length in
    let rec copy index =
      if index < length - 1 then begin
        Buffer.add_char buffer literal.[index];
        copy (if literal.[index] = '"' then index + 2 else index + 1)
      end
    in
    copy 1;
    Buffer.contents buffer

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
    else if text.[position] = '"' then
      let stop = find_string_literal_end text position in
      Some (Atom (String.sub text position (stop - position)), stop)
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

let is_answer output =
  match parse_sexps output with Atom ("sat" | "unsat" | "unknown") :: _ -> true | _ -> false

let run_program program input =
  let status, output, errors = Process.run ~input program [ "-in"; "-smt2" ] in
  if is_answer output then output
  else
    raise_bug
      "Z3 exited with status %d without answering a query, writing `%s` to stdout and `%s` to \
       stderr"
      status (String.trim output) (String.trim errors)

let find () =
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
        Ok { run_z3 = run_program program; queries_run = Atomic.make 0 }
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

type request = {
  query : Logic.query;
  text : string;
  requested : Logic.symbol list;
  value_arguments : string list;
}

let make_request ?(symbols = []) ?(terms = []) query =
  let rendering = Logic.render query in
  let named = Logic.list_symbols rendering in
  let requested =
    List.filter_map
      (fun symbol ->
        Option.map (fun canonical -> (symbol, canonical)) (List.assoc_opt symbol named))
      symbols
    @ List.filter_map
        (fun (symbol, term) ->
          Option.map (fun text -> (symbol, text)) (Logic.render_term rendering term))
        terms
  in
  {
    query;
    text = Logic.rendered_text rendering;
    requested = List.map fst requested;
    value_arguments = List.map snd requested;
  }

let make_input ~value_arguments text =
  header ^ text
  ^ (if value_arguments = [] then ""
     else Printf.sprintf "(get-value (%s))\n" (String.concat " " value_arguments))
  ^ "(get-info :reason-unknown)\n(get-info :rlimit)\n"

let show_input request = make_input ~value_arguments:request.value_arguments request.text

type status = Unsatisfiable | Satisfiable of sexp option list | Undecided of unknown

let read_unknown answers =
  let find_info keyword =
    List.find_map
      (function List [ Atom name; Atom value ] when name = keyword -> Some value | _ -> None)
      answers
  in
  match (find_info ":rlimit", find_info ":reason-unknown") with
  | Some steps_used, Some reason -> (
      match int_of_string_opt steps_used with
      | Some steps_used when steps_used >= steps -> Out_of_steps
      | Some _ -> Incomplete (read_string_literal reason)
      | None -> raise_bug "Z3 counted `%s` steps" steps_used)
  | _ -> raise_bug "Z3 answered unknown without its reason and its count of steps"

let read_status output =
  match parse_sexps output with
  | Atom "unsat" :: _ -> Unsatisfiable
  | Atom "sat" :: List pairs :: _ ->
      Satisfiable (List.map (function List [ _; value ] -> Some value | _ -> None) pairs)
  | Atom "sat" :: _ -> Satisfiable []
  | Atom "unknown" :: answers -> Undecided (read_unknown answers)
  | _ -> raise_bug "Z3's output `%s` is no answer" (String.trim output)

type run = { input : string; output : string }
type solved = { answer : answer; runs : run list }

let solve solver ~find_output request =
  let runs = ref [] in
  let check ~is_asking_values text =
    let input =
      make_input ~value_arguments:(if is_asking_values then request.value_arguments else []) text
    in
    let output =
      match find_output input with
      | Some output -> output
      | None ->
          Atomic.incr solver.queries_run;
          solver.run_z3 input
    in
    runs := { input; output } :: !runs;
    read_status output
  in
  let is_proven_from_ground_facts () =
    List.exists Logic.has_quantifier request.query.facts
    &&
    match
      check ~is_asking_values:false (Logic.show_query (Logic.remove_quantified_facts request.query))
    with
    | Unsatisfiable -> true
    | Satisfiable _ | Undecided _ -> false
  in
  let status =
    match check ~is_asking_values:true request.text with
    | Undecided _ when is_proven_from_ground_facts () -> Unsatisfiable
    | Undecided _ as undecided when Logic.has_uninterpreted_sort request.query ->
        let rec search_from = function
          | [] -> undecided
          | cardinality_bound :: larger_bounds -> (
              match
                check ~is_asking_values:true (Logic.show_query ~cardinality_bound request.query)
              with
              | Unsatisfiable -> search_from larger_bounds
              | Satisfiable _ as model -> model
              | Undecided _ -> undecided)
        in
        search_from cardinality_bounds
    | status -> status
  in
  (status, List.rev !runs)

let name_values request values =
  List.filter_map Fun.id
    (List.mapi
       (fun index symbol ->
         Option.map (fun value -> (symbol, value)) (Option.join (List.nth_opt values index)))
       request.requested)

let make_answer request = function
  | Unsatisfiable -> Proven
  | Satisfiable values -> Counterexample (name_values request values)
  | Undecided unknown -> Unknown unknown

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

let solve_all ?(find_output = fun _ -> None) solver requests =
  let asked = List.map (fun request -> (show_input request, request)) requests in
  let distinct = Hashtbl.create 64 in
  List.iter
    (fun (input, request) ->
      if not (Hashtbl.mem distinct input) then Hashtbl.replace distinct input request)
    asked;
  let distinct = Array.of_seq (Hashtbl.to_seq distinct) in
  let outcomes = Array.make (Array.length distinct) None in
  run_workers (Array.length distinct) (fun index ->
      outcomes.(index) <- Some (solve solver ~find_output (snd distinct.(index))));
  let by_input = Hashtbl.create (Array.length distinct) in
  Array.iteri
    (fun index (input, _) ->
      match outcomes.(index) with
      | Some outcome -> Hashtbl.replace by_input input outcome
      | None -> raise_bug "a distinct request was not solved")
    distinct;
  List.map
    (fun (input, request) ->
      let status, runs = Hashtbl.find by_input input in
      { answer = make_answer request status; runs })
    asked

module For_testing = struct
  let count_queries_run solver = Atomic.get solver.queries_run
  let make ~run_z3 = { run_z3; queries_run = Atomic.make 0 }
end
