let list_bodies (spans : Source.Definition_span.t array) (definition : Syntax.definition) =
  match definition.kind with
  | Function { body; _ } | Theorem { body; _ } | Test { body; _ } | Law_proof { body; _ } ->
      [ spans.(body.id) ]
  | Trait { members; _ } ->
      List.concat_map
        (fun (member : Syntax.trait_member Syntax.node) ->
          match member.kind with Law law -> [ spans.(law.body.id) ] | _ -> [])
        members
  | Method_declaration _ | Type_definition _ | Impl _ | Capability _ | Constant _
  | Definition_error _ ->
      []

let list_representation text (spans : Source.Definition_span.t array)
    (definition : Syntax.definition) =
  match definition.kind with
  | Type_definition { name; generics; clauses; _ } ->
      let body_stop =
        match clauses with
        | [] -> spans.(definition.id).stop
        | (first : Syntax.type_clause) :: _ ->
            String.length
              (String.drop_last_while Char.Ascii.is_white
                 (String.take_first spans.(first.id).start text))
      in
      let head_stop =
        match List.rev generics with
        | [] -> spans.(name.id).stop
        | (last : Syntax.generic_parameter) :: _ -> (
            match String.index_from_opt text spans.(last.id).stop ']' with
            | Some closer when closer < body_stop -> closer + 1
            | Some _ | None -> spans.(last.id).stop)
      in
      Source.Definition_span.make head_stop body_stop
      :: List.filter_map
           (fun (clause : Syntax.type_clause) ->
             match clause.kind with
             | Derives _ -> None
             | Type_invariant _ | Potential _ -> Some spans.(clause.id))
           clauses
  | Function _ | Method_declaration _ | Theorem _ | Test _ | Law_proof _ | Trait _ | Impl _
  | Capability _ | Constant _ | Definition_error _ ->
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
            (list_bodies (names.read_spans member) (names.read_definition member)))
        (names.list_contained key)
    in
    let spans = names.read_spans key and definition = names.read_definition key in
    let representation = if opaque then list_representation text spans definition else [] in
    cut text (list_bodies spans definition @ representation @ contained)

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

let is_signature_part : type a. a Database.Part.stored -> bool = function
  | Header _ | Trait_header _ | Constant_value _ | Interface _ | Derived_interface _ | Type_facts _
  | Signature_check _ | Contract _ | Contract_mir _ ->
      true
  | Parsed _ | Namespace _ | Resolved _ | Grant _ | Checked_body _ | Body_mir _ | Generated_mir _
  | Mir_call_edges _ | Usage _ | Ownership _ | Import_check _ | Package_check _ | Call_edges _
  | Recursion_group _ | Proof _ | Lowered _ | Test_key _ ->
      false

let is_signature : Database.Part.t -> bool = function
  | Stored (Any part) -> is_signature_part part
  | Input _ | Name _ -> false
