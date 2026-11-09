(* Splitting a file into its [use] lines and definitions before parsing them.
   See PARSER.md, "Splitting a file into definitions".

   The lexer balances brackets, so this needs no parsing: a [Newline] outside
   every bracket ends an item, unless a [{] follows it, which opens a body
   that starts on its own line. No item starts with [{], so the rule never
   splits a definition in two. *)

open Token

(* The indexes of an item's first token and one past its last. *)
type item = { first : int; stop : int }

let items (tokens : Token.t array) =
  let items = ref [] and depth = ref 0 and first = ref (-1) in
  let close index =
    if !first >= 0 then items := { first = !first; stop = index } :: !items;
    first := -1
  in
  Array.iteri
    (fun index (token : Token.t) ->
      match token.kind with
      | End_of_file -> close index
      | Newline when !depth = 0 ->
          let next =
            if index + 1 < Array.length tokens then tokens.(index + 1).kind else End_of_file
          in
          if next <> Punctuation (Open Curly) then close index
      | kind -> (
          if !first < 0 then first := index;
          match kind with
          | Punctuation (Open _) -> incr depth
          | Punctuation (Close _) -> decr depth
          | _ -> ()))
    tokens;
  List.rev !items
