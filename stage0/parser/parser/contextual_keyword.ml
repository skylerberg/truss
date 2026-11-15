type t =
  | Amortized
  | Time
  | Allocations
  | Allocated_bytes
  | Calls
  | O
  | Finite
  | Potential
  | By
  | Bit_vector

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
    ("by", By);
    ("bit_vector", Bit_vector);
  ]

let spelling word = fst (List.find (fun (_, candidate) -> candidate = word) spellings)

let of_token (kind : Token.kind) =
  match kind with Lower text | Upper text -> List.assoc_opt text spellings | _ -> None

let resources = [ Time; Allocations; Allocated_bytes; Calls ]

let correct_misspelling cursor (token : Token.t) name ~words ~category =
  let message =
    Printf.sprintf "Expected %s, one of %s, found `%s`." category
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

let expect ?suggested cursor ~accepted ~category ~expected =
  let token = Cursor.peek cursor in
  let word =
    match (of_token token.kind, token.kind) with
    | Some word, _ when List.mem word accepted -> word
    | _, (Lower name | Upper name) ->
        correct_misspelling cursor token name
          ~words:(Option.value suggested ~default:accepted)
          ~category
    | _ -> Cursor.fail cursor expected
  in
  Cursor.advance cursor;
  word
