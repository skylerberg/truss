open Syntax

let bodies ~opaque (spans : Source.Definition_span.t array) (definition : definition) =
  let function_body (function_definition : function_definition) =
    [ spans.(function_definition.body.id) ]
  in
  match definition.kind with
  | Function function_definition -> function_body function_definition
  | Theorem { body; _ } | Test { body; _ } | Law_proof { body; _ } -> [ spans.(body.id) ]
  | Trait { members; _ } ->
      List.concat_map
        (fun (member : trait_member node) ->
          match member.kind with Law law -> [ spans.(law.body.id) ] | _ -> [])
        members
  | Type_definition { name; generics; _ } when opaque ->
      let stop =
        List.fold_left
          (fun stop (generic : generic_parameter) -> max stop spans.(generic.id).stop)
          spans.(name.id).stop generics
      in
      let stop = if generics = [] then stop else stop + 1 in
      [ Source.Definition_span.make stop spans.(definition.id).stop ]
  | Method_declaration _ | Type_definition _ | Impl _ | Capability _ | Constant _
  | Definition_error _ ->
      []

let cut text spans =
  let spans =
    List.sort
      (fun (left : Source.Definition_span.t) (right : Source.Definition_span.t) ->
        compare left.start right.start)
      spans
  in
  let buffer = Buffer.create (String.length text) in
  let at =
    List.fold_left
      (fun at (span : Source.Definition_span.t) ->
        if span.start >= at && span.stop <= String.length text then begin
          Buffer.add_string buffer (String.sub text at (span.start - at));
          span.stop
        end
        else at)
      0 spans
  in
  Buffer.add_string buffer (String.sub text at (String.length text - at));
  String.split_on_char '\n' (Buffer.contents buffer)
  |> List.map (fun line ->
      let rec stop position =
        if position > 0 && (line.[position - 1] = ' ' || line.[position - 1] = '\t') then
          stop (position - 1)
        else position
      in
      String.sub line 0 (stop (String.length line)))
  |> List.filter (( <> ) "")
  |> String.concat "\n"

let text (names : Resolve.Names.lookups) ~body ~opaque (key : Resolve.Names.key) =
  match (names.text key, names.definition key, names.spans key) with
  | Some text, Some definition, Some spans ->
      let contained =
        match names.place key with
        | Some { base; _ } ->
            List.concat_map
              (fun member ->
                match (names.place member, names.definition member, names.spans member) with
                | Some { base = member_base; _ }, Some written, Some member_spans ->
                    List.map
                      (fun (span : Source.Definition_span.t) ->
                        Source.Definition_span.of_file ~base
                          (Source.Definition_span.to_file ~base:member_base span))
                      (bodies ~opaque:false member_spans written)
                | _ -> [])
              (names.contained key)
        | None -> []
      in
      Some
        (if body then String.trim text else cut text (bodies ~opaque spans definition @ contained))
  | _ -> None

let kind_word : Resolve.Names.kind -> string = function
  | Function -> "function"
  | Type -> "type"
  | Trait -> "trait"
  | Capability -> "capability"
  | Constant -> "constant"
  | Theorem -> "theorem"
  | Method -> "method"
  | Member_constant -> "constant"
  | Impl -> "impl"
  | Test -> "test"
  | Law_proof -> "law proof"

let of_path (names : Resolve.Names.lookups) path =
  match names.key path with Some key -> text names ~body:false ~opaque:false key | None -> None

let labeled label signature =
  let indent = String.make (String.length label) ' ' in
  String.concat "\n"
    (List.mapi
       (fun line_index line ->
         Printf.sprintf "    %s %s" (if line_index = 0 then label else indent) line)
       (String.split_on_char '\n' signature))

let is_signature : Database.Part.t -> bool = function
  | Header _ | Trait_header _ | Constant_value _ | Interface _ | Derived_interface _ | Type_facts _
  | Signature_check _ | Contract _ | Contract_mir _ ->
      true
  | Source _ | Parsed _ | Packages | Modules _ | Dependencies _ | Namespace _ | Entry _ | Entries _
  | Imports _ | Declaration _ | Tree _ | Text _ | Place _ | Container _ | Contained _
  | Module_declarations _ | File_declarations _ | Package_declarations _ | Members _
  | Traits_declaring _ | Impl_index _ | Impls_of_type _ | Impls_of_trait _ | Law_proofs _
  | Resolved _ | Grant _ | Checked_body _ | Derived_form _ | Body_mir _ | Generated_mir _
  | Call_edges _ | Patterns _ | Usage _ | Ownership _ | Used_packages _ | Import_check _
  | Package_check _ | Successors _ | Recursion_group _ | Proof _ | Ground_types _ | Layout _
  | Lowered _ | Test_key _ ->
      false
