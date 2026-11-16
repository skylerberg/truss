let list_bodies ~opaque (spans : Source.Definition_span.t array) (definition : Syntax.definition) =
  let function_body (function_definition : Syntax.function_definition) =
    [ spans.(function_definition.body.id) ]
  in
  match definition.kind with
  | Function function_definition -> function_body function_definition
  | Theorem { body; _ } | Test { body; _ } | Law_proof { body; _ } -> [ spans.(body.id) ]
  | Trait { members; _ } ->
      List.concat_map
        (fun (member : Syntax.trait_member Syntax.node) ->
          match member.kind with Law law -> [ spans.(law.body.id) ] | _ -> [])
        members
  | Type_definition { name; generics; _ } when opaque ->
      let stop =
        List.fold_left
          (fun stop (generic : Syntax.generic_parameter) -> max stop spans.(generic.id).stop)
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
  Buffer.add_string buffer (String.drop_first at text);
  String.split_on_char '\n' (Buffer.contents buffer)
  |> List.map (String.drop_last_while Char.Ascii.is_blank)
  |> List.filter (( <> ) "")
  |> String.concat "\n"

let render_signature (names : Resolve.Names.lookups) ~body ~opaque (key : Resolve.Names.key) =
  let text = names.read_text key in
  if body then String.trim text
  else
    let base = (names.read_place key).base in
    let contained =
      List.concat_map
        (fun member ->
          let member_base = (names.read_place member).base in
          List.map
            (fun (span : Source.Definition_span.t) ->
              Source.Definition_span.of_file ~base
                (Source.Definition_span.to_file ~base:member_base span))
            (list_bodies ~opaque:false (names.read_spans member) (names.read_definition member)))
        (names.list_contained key)
    in
    cut text (list_bodies ~opaque (names.read_spans key) (names.read_definition key) @ contained)

let show_kind : Resolve.Names.kind -> string = function
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

let find_signature (names : Resolve.Names.lookups) path =
  Option.map (render_signature names ~body:false ~opaque:false) (names.find_key path)

let label_signature label signature =
  let indent = String.make (String.length label) ' ' in
  String.concat "\n"
    (List.mapi
       (fun line_index line ->
         Printf.sprintf "    %s %s" (if line_index = 0 then label else indent) line)
       (String.split_on_char '\n' signature))

let is_signature : Database.Part.t -> bool = function
  | Stored
      (Computed
         ( Header _ | Trait_header _ | Constant_value _ | Interface _ | Derived_interface _
         | Type_facts _ | Signature_check _ | Contract _ | Contract_mir _ )) ->
      true
  | Stored
      (Computed
         ( Parsed _ | Namespace _ | Resolved _ | Grant _ | Checked_body _ | Derived_form _
         | Body_mir _ | Generated_mir _ | Mir_call_edges _ | Patterns _ | Usage _ | Ownership _
         | Import_check _ | Package_check _ | Call_edges _ | Proof _ | Lowering _ ))
  | Stored (Recursion_group _)
  | Input _ | Name _ ->
      false
