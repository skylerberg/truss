(* Characters outside ASCII that look like Truss punctuation, and reach
   source code from word processors, input methods, and the notation of
   Lean and Agda. The table is chosen by hand: each entry is a character
   that people type or paste for the ASCII spelling beside it. *)

type t =
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

let find code_point =
  if code_point >= 0x2000 && code_point <= 0x200A then Some Space
  else List.assoc_opt code_point table

(* The token that an ASCII spelling in the table lexes as. *)
let token spelling : Token.kind option =
  match List.assoc_opt spelling Token.punctuation with
  | Some punctuation -> Some (Punctuation punctuation)
  | None -> Token.word spelling
