let version = "5.3.3"
let steps = 1_000_000
let refutation_steps = steps / 10
let cardinality_bounds = [ 2; 3; 4 ]
let raise_bug format = Compiler_bug.raise_bug ~stage:"Solver" format

type t = { answer_query : string -> string; stop : unit -> unit; queries_run : int Atomic.t }
type sexp = Atom of string | List of sexp list
type unknown = Out_of_steps | Incomplete of string
type answer = Proven | Falsifiable | Unknown of unknown

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

let make_header ~steps =
  Printf.sprintf
    "(set-option :smt.random_seed 0)\n(set-option :sat.random_seed 0)\n(set-option :rlimit %d)\n"
    steps

let info_request = "(get-info :reason-unknown)\n(get-info :rlimit)\n"
let end_of_answer = "truss.end-of-answer"
let echo_end_of_answer = Printf.sprintf "(echo \"%s\")\n" end_of_answer

type pool = { program : string; lock : Mutex.t; mutable idle : Process.coprocess list }

let start_z3 program = Process.start program [ "-in"; "-smt2" ]

let take_idle pool =
  Mutex.protect pool.lock (fun () ->
      match pool.idle with
      | [] -> None
      | z3 :: idle ->
          pool.idle <- idle;
          Some z3)

let answer_from pool input =
  let z3 = match take_idle pool with Some z3 -> z3 | None -> start_z3 pool.program in
  match Process.converse z3 (input ^ echo_end_of_answer ^ "(reset)\n") ~until:end_of_answer with
  | Ok output ->
      Mutex.protect pool.lock (fun () -> pool.idle <- z3 :: pool.idle);
      output
  | Error output ->
      Process.stop z3;
      raise_bug "Z3 stopped without answering a query, after writing `%s`" (String.trim output)
  | exception error ->
      Process.stop z3;
      raise error

let stop_idle pool =
  let idle =
    Mutex.protect pool.lock (fun () ->
        let idle = pool.idle in
        pool.idle <- [];
        idle)
  in
  List.iter Process.stop idle

let read_version output =
  match parse_sexps output with
  | [ List [ Atom ":version"; Atom literal ] ] when String.starts_with ~prefix:"\"" literal -> (
      match String.split_on_char ' ' (read_string_literal literal) with
      | number :: _ -> Some number
      | [] -> None)
  | _ -> None

let find () =
  let program =
    match Sys.getenv_opt "TRUSS_Z3" with Some program when program <> "" -> program | _ -> "z3"
  in
  let report_not_run () =
    Error
      (Printf.sprintf
         "The prover needs Z3 %s, and `%s` could not be run. Install it, or set TRUSS_Z3 to its \
          path."
         version program)
  in
  match start_z3 program with
  | exception Unix.Unix_error _ -> report_not_run ()
  | z3 -> (
      match
        Process.converse z3 ("(get-info :version)\n" ^ echo_end_of_answer) ~until:end_of_answer
      with
      | Ok output when read_version output = Some version ->
          let pool = { program; lock = Mutex.create (); idle = [ z3 ] } in
          Ok
            {
              answer_query = answer_from pool;
              stop = (fun () -> stop_idle pool);
              queries_run = Atomic.make 0;
            }
      | Ok output ->
          Process.stop z3;
          Error
            (Printf.sprintf
               "The prover is pinned to Z3 %s, since another version can answer differently, but \
                `%s` answers `(get-info :version)` with `%s`."
               version program (String.trim output))
      | Error _ ->
          Process.stop z3;
          report_not_run ())

let stop solver = solver.stop ()

type request = { query : Logic.query; text : string; is_refutation : bool }

let make_request query = { query; text = Logic.show_query query; is_refutation = false }
let make_refutation_request query = { query; text = Logic.show_query query; is_refutation = true }
let count_steps request = if request.is_refutation then refutation_steps else steps
let make_input ~steps text = make_header ~steps ^ text ^ info_request
let show_input request = make_input ~steps:(count_steps request) request.text

let read_unknown ~steps answers =
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

let read_answer ~steps output =
  let answers = parse_sexps output in
  if List.exists (function List (Atom "error" :: _) -> true | _ -> false) answers then
    raise_bug "Z3 answered a query with `%s`" (String.trim output);
  match answers with
  | Atom "unsat" :: _ -> Proven
  | Atom "sat" :: _ -> Falsifiable
  | Atom "unknown" :: answers -> Unknown (read_unknown ~steps answers)
  | _ -> raise_bug "Z3's output `%s` is no answer" (String.trim output)

type run = { input : string; output : string }
type solved = { answer : answer; runs : run list }

let solve solver ~find_output request =
  let runs = ref [] and steps = count_steps request in
  let check text =
    let input = make_input ~steps text in
    let output =
      match find_output input with
      | Some output -> output
      | None ->
          Atomic.incr solver.queries_run;
          solver.answer_query input
    in
    runs := { input; output } :: !runs;
    read_answer ~steps output
  in
  let is_proven_from_ground_facts () =
    List.exists Logic.has_quantifier request.query.facts
    && check (Logic.show_query (Logic.remove_quantified_facts request.query)) = Proven
  in
  let is_proven_one_conjunct_at_a_time () =
    match Logic.list_conjunct_queries request.query with
    | [] -> false
    | conjuncts ->
        List.for_all (fun conjunct -> check (Logic.show_query conjunct) = Proven) conjuncts
  in
  let answer =
    match check request.text with
    | Unknown _ as undecided when request.is_refutation -> undecided
    | Unknown _ when is_proven_from_ground_facts () -> Proven
    | Unknown Out_of_steps when is_proven_one_conjunct_at_a_time () -> Proven
    | Unknown _ as undecided when Logic.has_uninterpreted_sort request.query ->
        let rec search_from = function
          | [] -> undecided
          | cardinality_bound :: larger_bounds -> (
              match check (Logic.show_query ~cardinality_bound request.query) with
              | Proven -> search_from larger_bounds
              | Falsifiable -> Falsifiable
              | Unknown _ -> undecided)
        in
        search_from cardinality_bounds
    | answer -> answer
  in
  { answer; runs = List.rev !runs }

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
  List.map (fun (input, _) -> Hashtbl.find by_input input) asked

module For_testing = struct
  let count_queries_run solver = Atomic.get solver.queries_run
  let make ~run_z3 = { answer_query = run_z3; stop = ignore; queries_run = Atomic.make 0 }
end
