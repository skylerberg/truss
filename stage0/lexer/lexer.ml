(* The scanner and layout run together as one pipeline: layout pulls each raw
   token from the scanner as it needs it. Only a file with brackets still
   open at its end is read twice, the second time with bracket recovery
   turned on.

   Every fix is then checked by applying it and lexing the result again. A
   fix is built from the text around one error, but whether it is right can
   depend on things it cannot see, such as where recovery from another error
   guesses a construct ends. Checking makes LEXER.md's rule hold by
   construction: applying any fix removes its diagnostic and adds no other.

   Only the part of the file around a fix is lexed again. A token that
   starts a line outside any bracket begins with the lexer's state empty:
   no bracket, string, or comment is open there. So the text between two
   such tokens lexes the same on its own as in the whole file, and is
   usually one top-level statement or definition, as long as it is lexed in
   the same mode: bracket recovery is turned on for the whole file when any
   bracket is left open, and then a definition keyword in column 0 closes
   brackets anywhere. So a part is lexed with recovery exactly when the
   file needed it. A fix that closes the file's last open bracket turns
   recovery off for the file, but then no other part had a bracket closed
   by recovery, and lexing the fixed part with recovery can only reject a
   fix, never accept a wrong one. A fix that leaves
   something open at the end of that text is reported there as an error,
   so it fails the check rather than affecting what follows unseen.

   Only the fixes of the diagnostics that are shown (Diagnostic.limit) are
   checked, which bounds the work for a file full of errors. The others
   are left without fixes until earlier errors are fixed and they come into
   view. *)

let with_recovery source =
  let diagnostics = Diagnostic.Collector.create () in
  let scanner = Scanner.create source diagnostics in
  let tokens = Layout.file_with_recovery ~source ~diagnostics (fun () -> Scanner.next scanner) in
  (tokens, Diagnostic.Collector.to_list diagnostics)

(* The tokens and diagnostics, and whether the file needed bracket
   recovery. *)
let lex_unchecked source =
  let diagnostics = Diagnostic.Collector.create () in
  let scanner = Scanner.create source diagnostics in
  match Layout.file ~source ~diagnostics (fun () -> Scanner.next scanner) with
  | `Complete tokens -> (tokens, Diagnostic.Collector.to_list diagnostics, false)
  | `Unclosed_at_end ->
      let tokens, diagnostics = with_recovery source in
      (tokens, diagnostics, true)

(* The offsets where the parts of the file that lex on their own begin: the
   start of the file, and each token that starts a line outside brackets. *)
let part_starts source (tokens : Token.t array) =
  let depth = ref 0 in
  let starts = ref [ 0 ] in
  Array.iter
    (fun (token : Token.t) ->
      match token.kind with
      | Punctuation (Open _) -> incr depth
      | Punctuation (Close _) -> decr depth
      | Newline | End_of_file -> ()
      | _ when !depth = 0 && Source.starts_line source token.span.start ->
          starts := token.span.start :: !starts
      | _ -> ())
    tokens;
  List.sort_uniq compare !starts

let sorted_codes diagnostics = List.sort compare (List.map (fun (d : Diagnostic.t) -> d.code) diagnostics)

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

let keep_working_fixes source ~recovery tokens diagnostics =
  let text = Source.text source in
  let starts = part_starts source tokens in
  (* The codes of each part as it was, lexed on its own, by where it starts. *)
  let original_codes = Hashtbl.create 16 in
  let lex_part part_text =
    let part = Source.create ~path:(Source.path source) part_text in
    let diagnostics =
      if recovery then snd (with_recovery part)
      else
        let _, diagnostics, _ = lex_unchecked part in
        diagnostics
    in
    sorted_codes diagnostics
  in
  let works (diagnostic : Diagnostic.t) (fix : Diagnostic.fix) =
    (* The text to lex again covers the diagnostic and the fix's edits: from
       the last part start before them to the first one after. An edit at a
       part's start belongs to the part before it too, as a closing bracket
       inserted before a definition does. *)
    let first =
      List.fold_left (fun low (edit : Diagnostic.edit) -> min low edit.span.start) diagnostic.span.start fix.edits
    in
    let last =
      List.fold_left (fun high (edit : Diagnostic.edit) -> max high edit.span.stop) diagnostic.span.stop fix.edits
    in
    let start = List.fold_left (fun found offset -> if offset < first then offset else found) 0 starts in
    let stop =
      List.fold_left (fun found offset -> if offset > last && offset < found then offset else found) (String.length text) starts
    in
    let part = String.sub text start (stop - start) in
    let before =
      match Hashtbl.find_opt original_codes (start, stop) with
      | Some codes -> codes
      | None ->
          let codes = lex_part part in
          Hashtbl.add original_codes (start, stop) codes;
          codes
    in
    let shifted =
      Diagnostic.fix fix.title
        (List.map
           (fun (edit : Diagnostic.edit) ->
             Diagnostic.replace (Source.span (edit.span.start - start) (edit.span.stop - start)) edit.replacement)
           fix.edits)
    in
    match Diagnostic.apply_fix part shifted with
    | exception Invalid_argument _ -> false
    | fixed -> is_contained (lex_part fixed) (remove_one diagnostic.code before)
  in
  List.mapi
    (fun index (diagnostic : Diagnostic.t) ->
      let fixes = if index < Diagnostic.limit then List.filter (works diagnostic) diagnostic.fixes else [] in
      { diagnostic with fixes })
    diagnostics

let lex ?(check_fixes = true) source =
  let tokens, diagnostics, recovery = lex_unchecked source in
  (tokens, if check_fixes then keep_working_fixes source ~recovery tokens diagnostics else diagnostics)
