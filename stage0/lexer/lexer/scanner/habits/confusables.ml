(* Characters outside ASCII that look like Truss punctuation, and reach
   source code from word processors, input methods, and the notation of
   Lean and Agda. The table is chosen by hand: each entry is a character
   that people type or paste for the ASCII spelling beside it. *)

type entry =
  | Space  (** A space that is not U+0020. *)
  | Spelled of string  (** The ASCII spelling of one token. *)
  | Opening_quote of string
      (** A curly quote that opens a string, with the quote that closes it. *)

let table =
  [
    (0x00A0, Space);
    (0x1680, Space);
    (0x202F, Space);
    (0x205F, Space);
    (0x3000, Space);
    (0x201C, Opening_quote "\u{201D}");
    (0x2018, Opening_quote "\u{2019}");
    (0xFF08, Spelled "(");
    (0xFF09, Spelled ")");
    (0xFF3B, Spelled "[");
    (0xFF3D, Spelled "]");
    (0xFF5B, Spelled "{");
    (0xFF5D, Spelled "}");
    (0xFF0C, Spelled ",");
    (0xFF1A, Spelled ":");
    (0xFF1D, Spelled "=");
    (0x2013, Spelled "-");
    (0x2014, Spelled "-");
    (0x2264, Spelled "<=");
    (0x2265, Spelled ">=");
    (0x2260, Spelled "!=");
    (0x2192, Spelled "->");
    (0x21D2, Spelled "=>");
    (0x2200, Spelled "forall");
    (0x2203, Spelled "exists");
  ]

let find code_point : entry option =
  if code_point >= 0x2000 && code_point <= 0x200A then Some Space
  else List.assoc_opt code_point table

(* The token that an ASCII spelling in the table lexes as. *)
let token spelling : Token.kind option =
  match List.assoc_opt spelling Token.punctuation with
  | Some punctuation -> Some (Punctuation punctuation)
  | None -> Token.word spelling

type scanned = Lexed of Token.kind | Spaced

(* The confusable character [value], [length] bytes at the cursor: reported,
   and lexed as its ASCII spelling, or skipped when it is a space. [None]
   when it is not a confusable character. *)
let scan (cursor : Cursor.t) ~value ~length =
  let start = cursor.position in
  let report ~replacement ~name =
    Cursor.report cursor ~code:Confusable_character
      ~fixes:
        [
          Diagnostic.fix
            ("Write `" ^ replacement ^ "`")
            [ Diagnostic.replace (Cursor.span start (start + length)) replacement ];
        ]
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
