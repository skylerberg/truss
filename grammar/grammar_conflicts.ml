(* The grammar's conflicts are exactly three: `{` after `return`, a name
   after `return`, and `else` after `let pattern = if ...`. All are resolved
   by shifting. Menhir reports conflicts in one state together, on a line
   "** Tokens involved: LOWER LBRACE", and a lone conflict on a line
   "** Token involved: ELSE". *)

let documented = [ "ELSE"; "LBRACE"; "LOWER" ]

let conflict_tokens line =
  match
    List.find_opt
      (fun prefix -> String.starts_with ~prefix line)
      [ "** Token involved: "; "** Tokens involved: " ]
  with
  | Some prefix ->
      String.split_on_char ' '
        (String.sub line (String.length prefix) (String.length line - String.length prefix))
      |> List.filter (fun token -> token <> "")
  | None -> []

let () =
  let channel = open_in "truss.conflicts" in
  let rec scan tokens =
    match input_line channel with
    | line -> scan (conflict_tokens line @ tokens)
    | exception End_of_file -> List.sort_uniq compare tokens
  in
  let tokens = scan [] in
  close_in channel;
  if tokens <> documented then begin
    Printf.printf
      "Menhir finds conflicts on [%s], but SPECIFICATION.md documents conflicts only on [%s]. \
       Resolve the new conflict, or explain it in SPECIFICATION.md and here.\n"
      (String.concat "; " tokens) (String.concat "; " documented);
    exit 1
  end
