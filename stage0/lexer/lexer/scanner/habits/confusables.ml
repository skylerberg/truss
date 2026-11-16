open Confusable_characters

let token spelling : Token.kind option =
  match List.assoc_opt spelling Token.punctuation with
  | Some punctuation -> Some (Punctuation punctuation)
  | None -> Token.word spelling

type scanned = Lexed of Token.kind | Spaced

let scan (cursor : Cursor.t) ~value ~length =
  let start = cursor.position in
  let report ~replacement ~name =
    Cursor.report cursor ~code:Confusable_character
      ~fixes:(Cursor.code_fixes cursor (Cursor.span start (start + length)) [ replacement ])
      (Cursor.span start (start + length))
      (Printf.sprintf "%s is not %s. Truss is written with ASCII punctuation."
         (Cursor.show_character cursor start)
         name);
    cursor.position <- start + length;
    cursor.line_is_blank <- false
  in
  match find value with
  | Some Space ->
      report ~replacement:" " ~name:"the space character";
      Some Spaced
  | Some (Spelled spelling) -> (
      match token spelling with
      | Some kind ->
          report ~replacement:spelling ~name:("`" ^ spelling ^ "`");
          Some (Lexed kind)
      | None -> None)
  | Some (Opening_quote closing) ->
      Option.map
        (fun kind -> Lexed kind)
        (String_forms.curly_quoted_string cursor ~opening_length:length ~closing)
  | None -> None
