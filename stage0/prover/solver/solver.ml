(* The pinned solver. See PROVER.md, "The solver". *)

let version = "5.3.3"
let steps = 2_000_000

type t = { program : string }

let find () =
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
      then Ok { program }
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

let key query = Logic.hash (Printf.sprintf "z3 %s\n%s%s" version header (Logic.text query))

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

let solve solver ?(values = []) query =
  let named = Logic.symbols query in
  let requested =
    List.filter_map
      (fun symbol ->
        List.assoc_opt symbol named |> Option.map (fun canonical -> (symbol, canonical)))
      values
  in
  let key = key query ^ String.concat "," (List.map snd requested) in
  match Hashtbl.find_opt cache key with
  | Some answer -> answer
  | None ->
      let text = Logic.text query in
      let input =
        header ^ text
        ^
        if requested = [] then ""
        else Printf.sprintf "(get-value (%s))\n" (String.concat " " (List.map snd requested))
      in
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
      Hashtbl.replace cache key answer;
      answer
