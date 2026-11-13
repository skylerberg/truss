(* The Z3 version the prover is pinned to. A different one is refused, since
   its answers could differ. *)
let version = "5.3.3"

(* The limit in steps every query runs with. *)
let steps = 1_000_000

type t = { program : string; cache : string option; mutable solved : int }

let find ?cache () =
  let program = Option.value (Sys.getenv_opt "TRUSS_Z3") ~default:"z3" in
  match Process.run program [ "--version" ] with
  | exception Unix.Unix_error _ ->
      Error
        (Printf.sprintf
           "The prover needs Z3 %s, and `%s` could not be run. Install it, or set TRUSS_Z3 to its \
            path."
           version program)
  | 0, output, _ ->
      let expected = "Z3 version " ^ version in
      if String.starts_with ~prefix:expected output then Ok { program; cache; solved = 0 }
      else
        Error
          (Printf.sprintf
             "The prover is pinned to Z3 %s, since another version can answer differently, but \
              `%s` is %s."
             version program (String.trim output))
  | _, _, errors -> Error (Printf.sprintf "`%s --version` failed: %s" program (String.trim errors))

type answer = Proven | Counterexample of (Logic.symbol * string) list | Out_of_steps

(* The options every query runs with, which are part of its key. *)
let header =
  Printf.sprintf
    "(set-option :produce-models true)\n\
     (set-option :smt.random_seed 0)\n\
     (set-option :sat.random_seed 0)\n\
     (set-option :rlimit %d)\n"
    steps

let key_of_text text = Logic.hash (Printf.sprintf "z3 %s\n%s%s" version header text)
let key query = key_of_text (Logic.text query)

(* A small reader of the s-expressions [get-value] prints. *)
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
  let rec one position =
    let position = skip position in
    if position >= length then None
    else if text.[position] = '(' then
      let rec items position acc =
        let position = skip position in
        if position >= length then (List (List.rev acc), position)
        else if text.[position] = ')' then (List (List.rev acc), position + 1)
        else
          match one position with
          | Some (item, position) -> items position (item :: acc)
          | None -> (List (List.rev acc), position)
      in
      Some (items (position + 1) [])
    else
      let stop = ref position in
      while !stop < length && not (List.mem text.[!stop] [ ' '; '\n'; '\t'; '\r'; '('; ')' ]) do
        incr stop
      done;
      Some (Atom (String.sub text position (!stop - position)), !stop)
  in
  let rec all position acc =
    match one position with
    | Some (item, position) -> all position (item :: acc)
    | None -> List.rev acc
  in
  all 0 []

let rec show_sexp = function
  | Atom atom -> atom
  | List items -> "(" ^ String.concat " " (List.map show_sexp items) ^ ")"

(* A query as the solver is asked it: its key, and for each symbol whose
   value a counterexample should give, the canonical name the text calls it
   by. It holds no text: a query's text is about 100 KB, and a run keeps
   every request it makes, so the text is rendered again from the query
   when the solver must be run. *)
type request = {
  key : string;
  requested : (Logic.symbol * string) list;
  asked : string list;  (** The [get-value] argument for each of [requested], in order. *)
}

(* An answer in the canonical names, the same for every query with the
   same text, so it can be kept by key alone. *)
type canonical = Proven_canonical | Values of (string * string) list | Out_of_steps_canonical

let cache : (string, canonical) Hashtbl.t = Hashtbl.create 256

(* Queries are solved on several domains at once, which share the cache
   and the count of solved queries. *)
let lock = Mutex.create ()
let locked work = Mutex.protect lock work
let key_of_asked text asked = key_of_text text ^ String.concat "," asked

let request ?(values = []) ?(terms = []) query =
  let rendering = Logic.render query in
  let named = Logic.symbols rendering in
  let symbols =
    List.filter_map
      (fun symbol ->
        List.assoc_opt symbol named
        |> Option.map (fun canonical -> ((symbol, canonical), canonical)))
      values
  in
  (* A term is asked by its text and kept by its place, since its text has
     spaces and the solver may print it back otherwise. *)
  let terms =
    List.filter_map
      (fun (name, term) -> Logic.term_text rendering term |> Option.map (fun text -> (name, text)))
      terms
    |> List.mapi (fun index (name, text) -> ((name, Printf.sprintf "#%d" index), text))
  in
  let requested = List.map fst (symbols @ terms) and asked = List.map snd (symbols @ terms) in
  { key = key_of_asked (Logic.rendered_text rendering) asked; requested; asked }

let request_key request = request.key

let read request = function
  | Proven_canonical -> Proven
  | Out_of_steps_canonical -> Out_of_steps
  | Values pairs ->
      Counterexample
        (List.filter_map
           (fun (symbol, canonical) ->
             Option.map (fun value -> (symbol, value)) (List.assoc_opt canonical pairs))
           request.requested)

(* Runs one request, or reads its answer from a cache. The query is the
   one the request was made from, and is rendered only to be run. *)
let ask solver (request, query) =
  let file = Option.map (fun directory -> Filename.concat directory request.key) solver.cache in
  let stored =
    match file with
    | Some file when Sys.file_exists file -> (
        (* An answer read is one still asked, so its file's age is how long
           ago a run last asked it, which pruning old answers reads. *)
        (try Unix.utimes file 0. 0. with Unix.Unix_error _ -> ());
        match String.split_on_char '\n' (File_system.read file) with
        | "proven" :: _ -> Some Proven_canonical
        | "out_of_steps" :: _ -> Some Out_of_steps_canonical
        | "counterexample" :: lines ->
            Some
              (Values
                 (List.filter_map
                    (fun line ->
                      match String.index_opt line ' ' with
                      | Some space ->
                          Some
                            ( String.sub line 0 space,
                              String.sub line (space + 1) (String.length line - space - 1) )
                      | None -> None)
                    lines))
        | _ -> None)
    | _ -> None
  in
  match (locked (fun () -> Hashtbl.find_opt cache request.key), stored) with
  | Some answer, _ | None, Some answer -> answer
  | None, None ->
      let text = Logic.text query in
      if key_of_asked text request.asked <> request.key then
        invalid_arg "Solver.ask_all: the query is not the one its request was made from";
      let input =
        header ^ text
        ^
        if request.requested = [] then ""
        else Printf.sprintf "(get-value (%s))\n" (String.concat " " request.asked)
      in
      locked (fun () -> solver.solved <- solver.solved + 1);
      let _, output, _ = Process.run ~input solver.program [ "-in"; "-smt2" ] in
      let answer =
        match parse_sexps output with
        | Atom "unsat" :: _ -> Proven_canonical
        | Atom "sat" :: rest ->
            Values
              (match rest with
              | List pairs :: _ ->
                  (* In the order asked. *)
                  List.filteri
                    (fun index _ -> index < List.length request.requested)
                    (List.mapi
                       (fun index pair ->
                         match (pair, List.nth_opt request.requested index) with
                         | List [ _; value ], Some (_, canonical) ->
                             Some (canonical, show_sexp value)
                         | _ -> None)
                       pairs)
                  |> List.filter_map Fun.id
              | _ -> [])
        | Atom "unknown" :: _ -> Out_of_steps_canonical
        | _ ->
            (* An error is a query the prover built wrong, not one the
               solver could not answer, and is never kept as an answer. *)
            failwith ("Solver.ask: the solver rejected a query: " ^ String.trim output)
      in
      locked (fun () -> Hashtbl.replace cache request.key answer);
      (match file with
      | Some file -> (
          let text =
            match answer with
            | Proven_canonical -> "proven\n"
            | Out_of_steps_canonical -> "out_of_steps\n"
            | Values pairs ->
                "counterexample\n"
                ^ String.concat ""
                    (List.map
                       (fun (canonical, value) -> Printf.sprintf "%s %s\n" canonical value)
                       pairs)
          in
          try
            File_system.make_directory (Filename.dirname file);
            File_system.write_atomically file text
          with Sys_error _ -> ())
      | None -> ());
      answer

let ask_all solver requests =
  let requests = Array.of_list requests in
  let answers = Array.make (Array.length requests) Out_of_steps_canonical in
  let next = Atomic.make 0 in
  let rec work () =
    let index = Atomic.fetch_and_add next 1 in
    if index < Array.length requests then begin
      answers.(index) <- ask solver requests.(index);
      work ()
    end
  in
  let others = min (Array.length requests) (Domain.recommended_domain_count ()) - 1 in
  let domains = List.init (max 0 others) (fun _ -> Domain.spawn work) in
  work ();
  List.iter Domain.join domains;
  Array.to_list answers

let solved solver = locked (fun () -> solver.solved)

module For_testing = struct
  let key = key
end
