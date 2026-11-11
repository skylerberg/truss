(* Splits a file into pieces, its [use] lines and definitions, before they
   are parsed, and finds where a method inside a trait, an [impl], or a
   capability ends.

   The lexer balances brackets, so this needs no parsing: a [Newline] outside
   every bracket ends a piece, unless a [{] follows it, which opens a body
   that starts on a line of its own. No piece starts with [{], so the rule
   never splits a definition in two. *)

open Token

(* The indexes of a piece's first token and one past its last. *)
type piece = { first : int; stop : int }

(* One past the last token of the piece that starts at [first]: the end of
   its line, the closer of the enclosing bracket, or the end of the tokens. *)
let stop (tokens : Token.t array) ~first =
  let rec go index depth =
    if index >= Array.length tokens then index
    else
      match tokens.(index).kind with
      | End_of_file -> index
      | Newline when depth = 0 ->
          if index + 1 < Array.length tokens && tokens.(index + 1).kind = Punctuation (Open Curly)
          then go (index + 1) depth
          else index
      | Punctuation (Open _) -> go (index + 1) (depth + 1)
      | Punctuation (Close _) -> if depth = 0 then index else go (index + 1) (depth - 1)
      | _ -> go (index + 1) depth
  in
  go first 0

let pieces (tokens : Token.t array) =
  let rec go index pieces =
    if index >= Array.length tokens then List.rev pieces
    else
      match tokens.(index).kind with
      | End_of_file -> List.rev pieces
      | Newline -> go (index + 1) pieces
      | _ ->
          let stop = max (index + 1) (stop tokens ~first:index) in
          go stop ({ first = index; stop } :: pieces)
  in
  go 0 []
