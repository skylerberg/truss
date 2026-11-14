(* Operators of other languages, which extend a Truss operator: `..<`,
   `<>`, `===`, `++`, and the others. *)

open Token
open Cursor

type scanned = Lexed of Token.kind | Skipped

let scan cursor ~follows_operand ~operand_follows =
  let start = cursor.position in
  let is offset character = byte cursor (start + offset) = Char.code character in
  let lexed kind length =
    cursor.position <- start + length;
    Some (Lexed kind)
  in
  let replaced ~length ~replacements ~message kind =
    report cursor ~code:Foreign_operator
      ~fixes:
        (List.map
           (fun replacement ->
             Diagnostic.fix
               ("Write `" ^ replacement ^ "`")
               [ Diagnostic.replace (span start (start + length)) replacement ])
           replacements)
      (span start (start + length))
      message;
    lexed kind length
  in
  if is 0 ':' && is 1 '=' then lexed (Foreign Colon_equal) 2
  else if is 0 '-' && is 1 '-' then lexed (Foreign Minus_minus) 2
  else if is 0 '+' && is 1 '+' then lexed (Foreign Plus_plus) 2
  else if is 0 '*' && is 1 '*' then lexed (Foreign Star_star) 2
  else if is 0 '|' && is 1 '>' then lexed (Foreign Pipe_greater) 2
  else if is 0 '.' && is 1 '.' && is 2 '<' then
    replaced ~length:3 ~replacements:[ ".." ] ~message:"Truss has no `..<`; write `..`."
      (Punctuation Dot_dot)
  else if is 0 '<' && is 1 '>' then
    replaced ~length:2 ~replacements:[ "!=" ] ~message:"Truss has no `<>`; write `!=`."
      (Punctuation Not_equal)
  else if (is 0 '=' || is 0 '!') && is 1 '=' && is 2 '=' && not (is 3 '=') then (
    let written, replacement, kind =
      if is 0 '=' then ("===", "==", Equal_equal) else ("!==", "!=", Not_equal)
    in
    report cursor ~code:Strict_equality
      ~fixes:
        [
          Diagnostic.fix
            ("Write `" ^ replacement ^ "`")
            [ Diagnostic.replace (span start (start + 3)) replacement ];
        ]
      (span start (start + 3))
      (Printf.sprintf "Truss has no `%s`. `%s` already compares values of the same type." written
         replacement);
    lexed (Punctuation kind) 3)
  else if is 0 '.' && is 1 '.' && is 2 '.' then begin
    (* Between two operands a range, whose end Ruby excludes and Swift
       includes; with neither, Python's placeholder, `todo`; before an
       operand only, a spread, which lexes as nothing. Scanning ahead, it is
       `..=`, so that it does not scan ahead again. *)
    cursor.line_is_blank <- false;
    if cursor.is_peek then lexed (Punctuation Dot_dot_equal) 3
    else
      match (follows_operand, operand_follows (start + 3)) with
      | true, true ->
          replaced ~length:3 ~replacements:[ ".."; "..=" ]
            ~message:
              "Truss has no `...`. A range that leaves out its end is written `..`, and one that \
               includes its end is written `..=`."
            (Punctuation Dot_dot_equal)
      | false, false ->
          replaced ~length:3 ~replacements:[ "todo" ]
            ~message:"Truss has no `...`; code that is not written yet is `todo`." (Keyword Todo)
      | _ ->
          cursor.position <- start + 3;
          report cursor ~code:Foreign_operator
            (span start (start + 3))
            "Truss has no `...`: it has no spread or rest operator, and a function takes a list \
             where it takes any number of values.";
          Some Skipped
  end
  else None
