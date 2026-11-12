(* The Z3 version the prover is pinned to. A different one is refused, since
   its answers could differ. *)
let version = "5.3.3"

(* The limit in steps every query runs with. *)
let steps = 2_000_000

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

type answer = Proven | Counterexample of (Logic.Symbol.t * string) list | Out_of_steps

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

(* A query's text, its symbols' canonical names, and its key, made once for
   each query asked, which a run asks again: once ahead with the others,
   and again for its answer. *)
module Asked = Hashtbl.Make (struct
  type t = Logic.query

  let equal = ( == )
  let hash = Hashtbl.hash
end)

type rendered = { text : string; named : (Logic.Symbol.t * string) list; text_key : string }

let rendered_queries : rendered Asked.t = Asked.create 1024

(* A small reader of the s-expressions [get-value] prints. *)
type sexp = Atom of string | List of sexp list

let parse_sexps text =
  let length = String.length text in
  let rec skip i =
    if i < length && (text.[i] = ' ' || text.[i] = '\n' || text.[i] = '\t' || text.[i] = '\r') then
      skip (i + 1)
    else i
  in
  let rec one i =
    let i = skip i in
    if i >= length then None
    else if text.[i] = '(' then
      let rec items i acc =
        let i = skip i in
        if i >= length then (List (List.rev acc), i)
        else if text.[i] = ')' then (List (List.rev acc), i + 1)
        else
          match one i with
          | Some (item, i) -> items i (item :: acc)
          | None -> (List (List.rev acc), i)
      in
      Some (items (i + 1) [])
    else
      let stop = ref i in
      while !stop < length && not (List.mem text.[!stop] [ ' '; '\n'; '\t'; '\r'; '('; ')' ]) do
        incr stop
      done;
      Some (Atom (String.sub text i (!stop - i)), !stop)
  in
  let rec all i acc =
    match one i with Some (item, i) -> all i (item :: acc) | None -> List.rev acc
  in
  all 0 []

let rec show_sexp = function
  | Atom atom -> atom
  | List items -> "(" ^ String.concat " " (List.map show_sexp items) ^ ")"

(* A query as the solver is asked it: its canonical text, its key, and for
   each symbol whose value a counterexample should give, the canonical
   name the text calls it by. *)
type request = {
  text : string;
  key : string;
  requested : (Logic.Symbol.t * string) list;
  asked : string list;  (** What [get-value] is given for each of [requested], in order. *)
}

(* An answer in the canonical names, the same for every query with the
   same text, so it can be kept by key alone. *)
type canonical = Proven_canonical | Values of (string * string) list | Out_of_steps_canonical

let cache : (string, canonical) Hashtbl.t = Hashtbl.create 256

(* Queries are solved on several domains at once, which share the cache
   and the count of what was solved. *)
let lock = Mutex.create ()
let locked f = Mutex.protect lock f

let render query =
  match locked (fun () -> Asked.find_opt rendered_queries query) with
  | Some rendered -> rendered
  | None ->
      let text = Logic.text query in
      let rendered = { text; named = Logic.symbols query; text_key = key_of_text text } in
      locked (fun () -> Asked.replace rendered_queries query rendered);
      rendered

let request ?(values = []) ?(terms = []) query =
  let { text; named; text_key } = render query in
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
      (fun (name, term) -> Logic.term_text query term |> Option.map (fun text -> (name, text)))
      terms
    |> List.mapi (fun index (name, text) -> ((name, Printf.sprintf "#%d" index), text))
  in
  let requested = List.map fst (symbols @ terms) and asked = List.map snd (symbols @ terms) in
  { text; key = text_key ^ String.concat "," asked; requested; asked }

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

(* Runs one request, or reads its answer from a cache. *)
let ask solver request =
  let file = Option.map (fun directory -> Filename.concat directory request.key) solver.cache in
  let stored =
    match file with
    | Some file when Sys.file_exists file -> (
        (* An answer read is one still asked, so its file's age is how long
           ago a run last asked it, which is what pruning old answers reads. *)
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
      let input =
        header ^ request.text
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
        | _ -> Out_of_steps_canonical
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

let solve solver ?(values = []) query =
  let request = request ~values query in
  read request (ask solver request)

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
