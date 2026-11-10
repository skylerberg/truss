(* The grammar's conflicts are exactly two: `{` after `return`, and `else`
   after `let pattern = if ...`. Both are resolved by shifting. *)

let () =
  let channel = open_in "truss.conflicts" in
  let rec tokens found =
    match input_line channel with
    | line ->
        let prefix = "** Token involved: " in
        if String.starts_with ~prefix line then
          tokens
            (String.sub line (String.length prefix) (String.length line - String.length prefix)
            :: found)
        else tokens found
    | exception End_of_file -> List.sort compare found
  in
  let found = tokens [] in
  close_in channel;
  if found <> [ "ELSE"; "LBRACE" ] then begin
    Printf.printf
      "Menhir finds conflicts on [%s], but GRAMMAR.md documents conflicts only on [ELSE; LBRACE]. \
       Resolve the new conflict, or explain it in GRAMMAR.md and here.\n"
      (String.concat "; " found);
    exit 1
  end
