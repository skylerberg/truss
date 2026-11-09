(* The scanner and layout run together as one pipeline: layout pulls each raw
   token from the scanner as it needs it. Only a file with brackets still
   open at its end is read twice, the second time with bracket recovery
   turned on.

   Every fix is then checked by applying it and lexing the result again. A
   fix is built from the text around one error, but whether it is right can
   depend on things it cannot see, such as where recovery from another error
   guesses a construct ends. Checking makes LEXER.md's rule hold by
   construction: applying any fix removes its diagnostic and adds no other.
   Only a file with errors pays for this, one lexing per fix. *)

let attempt source ~recovery =
  let diagnostics = Diagnostic.Collector.create () in
  let scanner = Scanner.create source diagnostics in
  let tokens =
    Layout.run ~source ~diagnostics ~mode:(Layout.File { recovery }) (fun () -> Scanner.next scanner)
  in
  Option.map (fun tokens -> (tokens, Diagnostic.Collector.to_list diagnostics)) tokens

let lex_unchecked source =
  match attempt source ~recovery:false with
  | Some result -> result
  | None -> (
      match attempt source ~recovery:true with
      | Some result -> result
      | None -> assert false)

let codes_of diagnostics = List.sort compare (List.map (fun (d : Diagnostic.t) -> d.code) diagnostics)

(* Whether the sorted list [smaller] is contained in the sorted list [larger],
   counting repeats. *)
let rec is_contained smaller larger =
  match (smaller, larger) with
  | [], _ -> true
  | _ :: _, [] -> false
  | first :: rest, candidate :: larger_rest ->
      if first = candidate then is_contained rest larger_rest
      else if first > candidate then is_contained smaller larger_rest
      else false

let rec remove_one code = function
  | [] -> []
  | first :: rest -> if first = code then rest else first :: remove_one code rest

let fix_works source ~codes ~(diagnostic : Diagnostic.t) fix =
  match Diagnostic.apply_fix (Source.text source) fix with
  | exception Invalid_argument _ -> false
  | fixed ->
      let _, after = lex_unchecked (Source.create ~path:(Source.path source) fixed) in
      is_contained (codes_of after) (remove_one diagnostic.code codes)

let keep_working_fixes source diagnostics =
  let codes = codes_of diagnostics in
  List.map
    (fun (diagnostic : Diagnostic.t) ->
      { diagnostic with fixes = List.filter (fix_works source ~codes ~diagnostic) diagnostic.fixes })
    diagnostics

let lex ?(check_fixes = true) source =
  let tokens, diagnostics = lex_unchecked source in
  (tokens, if check_fixes then keep_working_fixes source diagnostics else diagnostics)
