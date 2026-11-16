type part = Header | Body | Member_header of int | Member_body of int

let list_part_spans (spans : Source.Definition_span.t array) (definition : Syntax.definition) =
  let split header body (whole : Source.Definition_span.t) (body_span : Source.Definition_span.t) =
    [ (header, Source.Definition_span.make whole.start body_span.start); (body, body_span) ]
  in
  let members lines body_of =
    List.concat
      (List.mapi
         (fun index (line : _ Syntax.node) ->
           match body_of line.kind with
           | Some (body : Source.Definition_span.t) ->
               split (Member_header index) (Member_body index) spans.(line.id) body
           | None -> [ (Member_header index, spans.(line.id)) ])
         lines)
  in
  let with_members lines body_of =
    let header =
      match lines with
      | (first : _ Syntax.node) :: _ ->
          Source.Definition_span.make spans.(definition.id).start spans.(first.id).start
      | [] -> spans.(definition.id)
    in
    (Header, header) :: members lines body_of
  in
  match definition.kind with
  | Function { body; _ } | Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ } ->
      split Header Body spans.(definition.id) spans.(body.id)
  | Constant { value; _ } -> split Header Body spans.(definition.id) spans.(value.id)
  | Method_declaration _ | Type_definition _ | Definition_error _ ->
      [ (Header, spans.(definition.id)) ]
  | Trait { members; _ } ->
      with_members members (function
        | Law { body; _ } -> Some spans.(body.id)
        | Associated_type _ | Associated_capability _ | Trait_member_error -> None)
  | Impl { members; _ } -> with_members members (fun (_ : Syntax.impl_member) -> None)
  | Capability { members; _ } -> with_members members (fun (_ : Syntax.capability_member) -> None)

let lies_in all (recovered : Source.Definition_span.t) (part_span : Source.Definition_span.t) =
  if recovered.start < recovered.stop then
    recovered.start < part_span.stop && part_span.start < recovered.stop
  else
    let position = recovered.start in
    if List.exists (fun (_, (span : Source.Definition_span.t)) -> span.start = position) all then
      part_span.start = position
    else part_span.start <= position && position < part_span.stop

let find_recovered_report ~spans ~recovered definition part =
  let all = list_part_spans spans definition in
  match List.assoc_opt part all with
  | None -> None
  | Some span ->
      Option.map Diagnostic.recovered
        (List.find_opt (fun recovered -> lies_in all recovered span) recovered)
