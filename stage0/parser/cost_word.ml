(* The words of a [cost] clause. The lexer reads them as names, and the
   parser recognizes them by their spelling where a clause expects them. See
   GRAMMAR.md, "Keywords". *)

type t = Amortized | Time | Allocations | Allocated_bytes | Calls | O | Finite | Potential

(* The one place each word is spelled. A test checks the list against
   GRAMMAR.md. *)
let spellings =
  [
    ("amortized", Amortized);
    ("time", Time);
    ("allocations", Allocations);
    ("allocated_bytes", Allocated_bytes);
    ("calls", Calls);
    ("O", O);
    ("finite", Finite);
    ("potential", Potential);
  ]

let spelling word = fst (List.find (fun (_, candidate) -> candidate = word) spellings)

(* The word a token spells: a name, uppercase only for [O]. *)
let of_token (kind : Token.kind) =
  match kind with Lower text | Upper text -> List.assoc_opt text spellings | _ -> None

let resources = [ Time; Allocations; Allocated_bytes; Calls ]

let edit_distance a b =
  let previous = Array.init (String.length b + 1) Fun.id in
  for i = 1 to String.length a do
    let current = Array.make (String.length b + 1) i in
    for j = 1 to String.length b do
      let cost = if a.[i - 1] = b.[j - 1] then 0 else 1 in
      current.(j) <- min (min (previous.(j) + 1) (current.(j - 1) + 1)) (previous.(j - 1) + cost)
    done;
    Array.blit current 0 previous 0 (Array.length current)
  done;
  previous.(String.length b)

(* Reports a name where one of the cost words [words] was expected. When
   exactly one of them is close to it, the fix writes that word, and parsing
   goes on as if it had been written, so that what follows is checked too. *)
let misspelled cursor (token : Token.t) written ~words ~what =
  let message =
    Printf.sprintf "Expected %s, one of %s, found `%s`." what
      (String.concat ", " (List.map (fun word -> "`" ^ spelling word ^ "`") words))
      written
  in
  match List.filter (fun word -> edit_distance written (spelling word) <= 2) words with
  | [ word ] ->
      let spelling = spelling word in
      Cursor.report cursor Diagnostic.Code.Cost_word token.span message
        ~fixes:
          [
            Diagnostic.fix
              (Printf.sprintf "Write `%s`" spelling)
              [ Diagnostic.replace token.span spelling ];
          ];
      word
  | _ ->
      Cursor.report cursor Diagnostic.Code.Cost_word token.span message;
      raise Cursor.Failed

(* The cost word the current token spells, among [accepted], or the one of
   [suggested] it misspells. *)
let expect ?suggested cursor ~accepted ~what ~expected =
  let token = Cursor.peek cursor in
  let word =
    match (of_token token.kind, token.kind) with
    | Some word, _ when List.mem word accepted -> word
    | _, (Lower written | Upper written) ->
        misspelled cursor token written ~words:(Option.value suggested ~default:accepted) ~what
    | _ -> Cursor.fail cursor expected
  in
  Cursor.advance cursor;
  word
