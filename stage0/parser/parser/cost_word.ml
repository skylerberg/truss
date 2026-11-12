(* The words of a [cost] clause. The lexer reads them as names, and the
   parser recognizes them by their spelling where a clause expects them. *)

type t = Amortized | Time | Allocations | Allocated_bytes | Calls | O | Finite | Potential

(* The only place each word is spelled. A test checks the list against
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

(* Reports the name [name] where one of the cost words [words] was
   expected. When exactly one of them is within an edit distance of 2, the
   fix replaces the name with that word, and the function returns the word,
   so that the rest of the clause is parsed and checked. *)
let misspelled cursor (token : Token.t) name ~words ~what =
  let message =
    Printf.sprintf "Expected %s, one of %s, found `%s`." what
      (String.concat ", " (List.map (fun word -> "`" ^ spelling word ^ "`") words))
      name
  in
  match List.filter (fun word -> Diagnostic.edit_distance name (spelling word) <= 2) words with
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
    | _, (Lower name | Upper name) ->
        misspelled cursor token name ~words:(Option.value suggested ~default:accepted) ~what
    | _ -> Cursor.fail cursor expected
  in
  Cursor.advance cursor;
  word
