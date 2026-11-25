type t =
  | Amortized
  | Metric of Language.Metric.t
  | Calls
  | O
  | Potential
  | By
  | Bit_vector
  | Evaluation

let spellings =
  ("amortized", Amortized)
  :: List.map (fun metric -> (Language.Metric.show metric, Metric metric)) Language.Metric.all
  @ [
      ("calls", Calls);
      ("O", O);
      ("potential", Potential);
      ("by", By);
      ("bit_vector", Bit_vector);
      ("evaluation", Evaluation);
    ]

let spell word = fst (List.find (fun (_, candidate) -> candidate = word) spellings)

let of_token (kind : Token.kind) =
  match kind with Lower text | Upper text -> List.assoc_opt text spellings | _ -> None

let resources = List.map (fun metric -> Metric metric) Language.Metric.all @ [ Calls ]

let correct_misspelling cursor (token : Token.t) name ~words ~category =
  let report correction =
    Cursor.report cursor token.span
      (Misspelled_cost_word { category; words = List.map spell words; found = name; correction })
  in
  match List.filter (fun word -> String.edit_distance name (spell word) <= 2) words with
  | [ word ] ->
      report (Some (spell word));
      word
  | _ ->
      report None;
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
