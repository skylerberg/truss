let insert_line_before_body (names : Resolve.Names.lookups) key spans (body : Syntax.block) line =
  let text = names.read_text key and brace = (Source.Definition_span.locate spans body.id).start in
  if brace > 0 && text.[brace - 1] = '\n' then
    Some (Diagnostic.insert (Source.Definition_span.make_zero_width brace) ("  " ^ line ^ "\n"))
  else if brace > 0 && text.[brace - 1] = ' ' then
    Some (Diagnostic.replace (Source.Definition_span.make (brace - 1) brace) ("\n  " ^ line ^ "\n"))
  else None

let find_clause_insertion (names : Resolve.Names.lookups) key clause =
  match names.read_definition key with
  | { kind = Function { body; _ }; _ } ->
      insert_line_before_body names key (names.read_spans key) body clause
  | _ -> None

let find_capability_insertion (names : Resolve.Names.lookups) key capability =
  match names.read_definition key with
  | { kind = Function { signature; body }; _ } -> (
      let spans = names.read_spans key in
      let locate id = Source.Definition_span.locate spans id in
      match
        ( List.find_opt
            (fun (clause : Syntax.clause) -> match clause.kind with Uses _ -> true | _ -> false)
            signature.clauses,
          signature.clauses )
      with
      | Some uses, _ ->
          Some
            (Diagnostic.insert
               (Source.Definition_span.make_zero_width (locate uses.id).stop)
               (", " ^ capability))
      | None, first :: _ ->
          Some
            (Diagnostic.insert
               (Source.Definition_span.make_zero_width (locate first.id).start)
               ("uses " ^ capability ^ "\n  "))
      | None, [] -> insert_line_before_body names key spans body ("uses " ^ capability))
  | _ -> None
