open Syntax

type part = Header | Body | Member_header of int | Member_body of int

(* The spans of a definition's parts. A member's header runs from the
   member's start to its body's start, and a member without a body is all
   header. A trait's, an [impl]'s, or a capability's own header runs to the
   first member it holds itself. The methods written inside it are
   definitions of their own, and no part of it. *)
let spans (definition : definition) =
  let split header body (whole : span) (body_span : span) =
    [ (header, Span.make whole.start body_span.start); (body, body_span) ]
  in
  let members lines body_of =
    List.concat
      (List.mapi
         (fun index (line : _ line) ->
           match body_of line.kind with
           | Some (body : span) -> split (Member_header index) (Member_body index) line.span body
           | None -> [ (Member_header index, line.span) ])
         lines)
  in
  let with_members lines body_of =
    let header =
      match lines with
      | (first : _ line) :: _ -> Span.make definition.span.start first.span.start
      | [] -> definition.span
    in
    (Header, header) :: members lines body_of
  in
  match definition.kind with
  | Function { body; _ } | Test { body; _ } | Theorem { body; _ } | Law_proof { body; _ } ->
      split Header Body definition.span body.span
  | Constant { value; _ } -> split Header Body definition.span value.span
  | Method_declaration _ | Type_definition _ | Definition_error _ -> [ (Header, definition.span) ]
  | Trait { members; _ } ->
      with_members members (function
        | Law { body; _ } -> Some body.span
        | Associated_type _ | Associated_capability _ | Trait_member_error -> None)
  | Impl { members; _ } -> with_members members (fun (_ : impl_member) -> None)
  | Capability { members; _ } -> with_members members (fun (_ : capability_member) -> None)

let lies_in all (recovered : span) (part_span : span) =
  if recovered.start < recovered.stop then
    recovered.start < part_span.stop && part_span.start < recovered.stop
  else
    let position = recovered.start in
    if List.exists (fun (_, (span : span)) -> span.start = position) all then
      part_span.start = position
    else part_span.start <= position && position < part_span.stop

let error_node (span : span) = Diagnostic.recovered (Syntax.Span.to_source span)

let reported definition part =
  let all = spans definition in
  match List.assoc_opt part all with
  | None -> None
  | Some span ->
      Option.map error_node
        (List.find_opt (fun recovered -> lies_in all recovered span) definition.recovered)

let broken definition part = Option.is_some (reported definition part)
