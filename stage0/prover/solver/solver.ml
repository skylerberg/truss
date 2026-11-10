(* The pinned solver. *)

let version = "5.3.3"
let steps = 2_000_000

type t = { program : string; cache : string option; mutable solved : int }

let find ?cache () =
  let program = Option.value (Sys.getenv_opt "TRUSS_Z3") ~default:"z3" in
  match Toolchain.run program [ "--version" ] with
  | exception Unix.Unix_error _ ->
      Error
        (Printf.sprintf
           "The prover needs Z3 %s, and `%s` could not be run. Install it, or set TRUSS_Z3 to its \
            path."
           version program)
  | 0, output, _ ->
      let expected = "Z3 version " ^ version in
      if
        String.length output >= String.length expected
        && String.sub output 0 (String.length expected) = expected
      then Ok { program; cache; solved = 0 }
      else
        Error
          (Printf.sprintf
             "The prover is pinned to Z3 %s, since another version can answer differently, but \
              `%s` is %s."
             version program (String.trim output))
  | _, _, errors -> Error (Printf.sprintf "`%s --version` failed: %s" program (String.trim errors))

type answer = Proven | Counterexample of (string * string) list | Out_of_steps

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

type rendered = { text : string; named : (string * string) list; text_key : string }

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

let cache : (string, answer) Hashtbl.t = Hashtbl.create 256

(* Queries are solved on several domains at once, which share the cache
   and the count of what was solved. *)
let lock = Mutex.create ()
let locked f = Mutex.protect lock f

let rec make_directories directory =
  if not (Sys.file_exists directory) then begin
    make_directories (Filename.dirname directory);
    try Sys.mkdir directory 0o755 with Sys_error _ when Sys.file_exists directory -> ()
  end

let render query =
  match locked (fun () -> Asked.find_opt rendered_queries query) with
  | Some rendered -> rendered
  | None ->
      let text = Logic.text query in
      let rendered = { text; named = Logic.symbols query; text_key = key_of_text text } in
      locked (fun () -> Asked.replace rendered_queries query rendered);
      rendered

let solve solver ?(values = []) query =
  let { text; named; text_key } = render query in
  let requested =
    List.filter_map
      (fun symbol ->
        List.assoc_opt symbol named |> Option.map (fun canonical -> (symbol, canonical)))
      values
  in
  let key = text_key ^ String.concat "," (List.map snd requested) in
  let file = Option.map (fun directory -> Filename.concat directory key) solver.cache in
  let stored =
    match file with
    | Some file when Sys.file_exists file -> (
        match String.split_on_char '\n' (In_channel.with_open_bin file In_channel.input_all) with
        | "proven" :: _ -> Some Proven
        | "out_of_steps" :: _ -> Some Out_of_steps
        | "counterexample" :: lines ->
            Some
              (Counterexample
                 (List.filter_map
                    (fun line ->
                      match String.index_opt line ' ' with
                      | Some space -> (
                          let canonical = String.sub line 0 space in
                          let value =
                            String.sub line (space + 1) (String.length line - space - 1)
                          in
                          match List.find_opt (fun (_, c) -> c = canonical) requested with
                          | Some (symbol, _) -> Some (symbol, value)
                          | None -> None)
                      | None -> None)
                    lines))
        | _ -> None)
    | _ -> None
  in
  match (locked (fun () -> Hashtbl.find_opt cache key), stored) with
  | Some answer, _ | None, Some answer -> answer
  | None, None ->
      let input =
        header ^ text
        ^
        if requested = [] then ""
        else Printf.sprintf "(get-value (%s))\n" (String.concat " " (List.map snd requested))
      in
      locked (fun () -> solver.solved <- solver.solved + 1);
      let _, output, _ = Toolchain.run ~input solver.program [ "-in"; "-smt2" ] in
      let answer =
        match parse_sexps output with
        | Atom "unsat" :: _ -> Proven
        | Atom "sat" :: rest ->
            let pairs =
              match rest with
              | List pairs :: _ ->
                  List.filter_map
                    (function
                      | List [ Atom canonical; value ] -> Some (canonical, show_sexp value)
                      | _ -> None)
                    pairs
              | _ -> []
            in
            Counterexample
              (List.filter_map
                 (fun (symbol, canonical) ->
                   Option.map (fun value -> (symbol, value)) (List.assoc_opt canonical pairs))
                 requested)
        | _ -> Out_of_steps
      in
      locked (fun () -> Hashtbl.replace cache key answer);
      (match file with
      | Some file -> (
          let text =
            match answer with
            | Proven -> "proven\n"
            | Out_of_steps -> "out_of_steps\n"
            | Counterexample values ->
                "counterexample\n"
                ^ String.concat ""
                    (List.map
                       (fun (symbol, value) ->
                         Printf.sprintf "%s %s\n" (List.assoc symbol requested) value)
                       values)
          in
          try
            make_directories (Filename.dirname file);
            (* Written whole, then moved into place, so a reader never sees half of it. *)
            let partial = file ^ ".partial" in
            Out_channel.with_open_bin partial (fun channel -> output_string channel text);
            Sys.rename partial file
          with Sys_error _ -> ())
      | None -> ());
      answer

let solve_all solver queries =
  let queries = Array.of_list queries in
  let answers = Array.make (Array.length queries) Out_of_steps in
  let next = Atomic.make 0 in
  let rec work () =
    let index = Atomic.fetch_and_add next 1 in
    if index < Array.length queries then begin
      let values, query = queries.(index) in
      answers.(index) <- solve solver ~values query;
      work ()
    end
  in
  let others = min (Array.length queries) (Domain.recommended_domain_count ()) - 1 in
  let domains = List.init (max 0 others) (fun _ -> Domain.spawn work) in
  work ();
  List.iter Domain.join domains;
  Array.to_list answers

let solved solver = locked (fun () -> solver.solved)
