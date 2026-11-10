(* Splitting a file into its [use] lines and definitions before parsing them,
   and a trait, an [impl], or a capability into its methods.

   The lexer balances brackets, so this needs no parsing: a [Newline] outside
   every bracket ends an item, unless a [{] follows it, which opens a body
   that starts on its own line. No item starts with [{], so the rule never
   splits a definition in two. *)

open Token

(* The indexes of an item's first token and one past its last. *)
type item = { first : int; stop : int }

(* One past the last token of the item that starts at [first]: where its
   line ends, or the bracket around it closes, or the tokens do. *)
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

let items (tokens : Token.t array) =
  let rec go index items =
    if index >= Array.length tokens then List.rev items
    else
      match tokens.(index).kind with
      | End_of_file -> List.rev items
      | Newline -> go (index + 1) items
      | _ ->
          let stop = max (index + 1) (stop tokens ~first:index) in
          go stop ({ first = index; stop } :: items)
  in
  go 0 []
