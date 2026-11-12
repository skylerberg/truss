(* A definition's signature as text: its source with every body left out.
   Truss has no comments, so a signature is the whole of a definition's
   documentation. [truss show] prints these, and [truss impact] shows the
   old and new ones of a changed interface. Stage0 has no formatter, so
   the text is the source as written, with the bodies cut out. *)

open Syntax

(* The spans, relative to the definition, of the parts that are not its
   signature: bodies, and for an opaque type seen from another package, its
   contents. *)
let bodies ~opaque (definition : definition) =
  let function_body (function_definition : function_definition) =
    [ function_definition.body.span ]
  in
  match definition.kind with
  | Function function_definition -> function_body function_definition
  | Theorem { body; _ } -> [ body.span ]
  | Test { body; _ } -> [ body.span ]
  | Law_proof { body; _ } -> [ body.span ]
  | Trait { members; _ } ->
      List.concat_map
        (fun (member : trait_member line) ->
          match member.kind with Law law -> [ law.body.span ] | _ -> [])
        members
  | Type_definition { name; generics; _ } when opaque ->
      (* Everything after the name and its generic parameters. *)
      let stop =
        List.fold_left
          (fun stop (generic : generic_parameter) -> max stop generic.span.stop)
          name.span.stop generics
      in
      (* The closing bracket of the generic parameters. *)
      let stop = if generics = [] then stop else stop + 1 in
      [ Span.make stop definition.span.stop ]
  | Method_declaration _ | Type_definition _ | Impl _ | Capability _ | Constant _
  | Definition_error _ ->
      []

(* Removes the spans from the text, and the spaces left at the end of each
   line, and the lines left empty. *)
let cut text spans =
  let spans =
    List.sort (fun (left : span) (right : span) -> compare left.start right.start) spans
  in
  let buffer = Buffer.create (String.length text) in
  let at =
    List.fold_left
      (fun at (span : span) ->
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

(* The text of the definition with that key: whole with [body], and
   otherwise its signature. *)
let text database ~body ~opaque (key : Resolve.Names.key) =
  match
    ( Query.demand database Resolve.Names.text key,
      Query.demand database Resolve.Names.definition key )
  with
  | Some text, Some definition ->
      (* The bodies of the methods written inside it, which are definitions
         of their own, at their places in its text. *)
      let contained =
        match Query.demand database Resolve.Names.base key with
        | Some (_, base) ->
            List.concat_map
              (fun member ->
                match
                  ( Query.demand database Resolve.Names.base member,
                    Query.demand database Resolve.Names.definition member )
                with
                | Some (_, member_base), Some written ->
                    List.map
                      (fun (span : span) ->
                        Span.make (span.start + member_base - base) (span.stop + member_base - base))
                      (bodies ~opaque:false written)
                | _ -> [])
              (Query.demand database Resolve.Names.contained key)
        | None -> []
      in
      Some (if body then String.trim text else cut text (bodies ~opaque definition @ contained))
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

let parts = [ "interface"; "signature"; "shape" ]

(* The signature of the definition at [path], as [text] gives it. *)
let of_path context path =
  match Query.demand context Interface.Summary.key path with
  | Some key -> text context ~body:false ~opaque:false key
  | None -> None

let labeled label signature =
  let indent = String.make (String.length label) ' ' in
  String.concat "\n"
    (List.mapi
       (fun line_index line ->
         Printf.sprintf "    %s %s" (if line_index = 0 then label else indent) line)
       (String.split_on_char '\n' signature))
