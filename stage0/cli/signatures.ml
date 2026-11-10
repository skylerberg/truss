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
  let function_body (f : function_definition) = [ f.body.span ] in
  match definition.kind with
  | Function f -> function_body f
  | Theorem { body; _ } -> [ body.span ]
  | Test { body; _ } -> [ body.span ]
  | Law_proof { body; _ } -> [ body.span ]
  | Trait { members; _ } ->
      List.concat_map
        (fun (member : trait_member line) ->
          match member.kind with
          | Trait_method { body = Some body; _ } -> [ body.span ]
          | Law law -> [ law.body.span ]
          | _ -> [])
        members
  | Impl { members; _ } ->
      List.concat_map
        (fun (member : impl_member line) ->
          match member.kind with Impl_method f -> function_body f | _ -> [])
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
  | Type_definition _ | Capability _ | Constant _ | Definition_error _ -> []

(* Removes the spans from the text, and the spaces left at the end of each
   line, and the lines left empty. *)
let cut text spans =
  let spans = List.sort (fun (a : span) (b : span) -> compare a.start b.start) spans in
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
      let rec stop n =
        if n > 0 && (line.[n - 1] = ' ' || line.[n - 1] = '\t') then stop (n - 1) else n
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
      Some (if body then String.trim text else cut text (bodies ~opaque definition))
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
