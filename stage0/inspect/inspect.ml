(* What the tools ask about one definition: its holes, with the type each
   must have and the names in scope there, and what is at a position. These
   read the type checker's results, and decide nothing of their own. *)

open Syntax

type hole = {
  offset : int;  (** Relative to the definition *)
  expected : string option;
      (** The type the hole must have, or [None] for a type defined as [todo] *)
  scope : (string * string) list;  (** Each name in scope, with its type, by name *)
}

(* A type as tools show it. The checked form holds no unsolved type, so the
   type of a [todo] nothing fixes, such as one that is interpolated, is the
   error type there, and is not decided yet. *)
let show_type (checked : Checked.t) id =
  match if id < Array.length checked.types then checked.types.(id) else None with
  | Some (Types.Error _ | Types.Hole) -> "not decided yet"
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

let local_type (checked : Checked.t) id =
  match if id < Array.length checked.local_types then checked.local_types.(id) else None with
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

(* The span of the expression with that id. *)
let expression_span (definition : definition) id =
  let found = ref None in
  let rec visit (value : expression) =
    if value.id = id then found := Some value.span else Syntax_walk.children visit value
  in
  Syntax_walk.definition visit definition;
  !found

(* Each [todo] of a definition, in order: the names in scope come from name
   resolution, which records them at each [todo] as it walks, and their
   types from the checked form. *)
let holes (definition : definition) (resolved : Resolve.resolved) (checked : Checked.t) =
  let values =
    List.filter_map
      (fun (id, scope) ->
        Option.map
          (fun (span : span) ->
            {
              offset = span.start;
              expected = Some (show_type checked id);
              scope =
                List.map
                  (fun (name, (value : Resolve.value)) ->
                    ( name,
                      match value with
                      | Value_local binding -> local_type checked binding
                      | Value_generic _ -> "USize"
                      | Value_field _ -> "a field" ))
                  scope;
            })
          (expression_span definition id))
      resolved.holes
  in
  match definition.kind with
  | Type_definition { name; body = Type_todo; _ } ->
      { offset = name.span.start; expected = None; scope = [] } :: values
  | _ -> values

(* What is at a position *)

type explanation = {
  text : string;  (** The name or expression as written *)
  meaning : string option;  (** What a name refers to *)
  refers_to : Path.t option;  (** The definition a name refers to, for its signature *)
  type_ : string option;
}

let describe_target (target : Resolve.target) =
  match target with
  | Definition (_, path) -> (Printf.sprintf "the definition %s" (Path.show path), Some path)
  | Local _ -> ("a local variable or parameter", None)
  | Binding -> ("a name bound here", None)
  | Type_parameter _ | Capability_parameter _ | Value_parameter _ -> ("a generic parameter", None)
  | Variant (path, name) -> (Printf.sprintf "the variant %s of %s" name (Path.show path), None)
  | Module module_ -> (Printf.sprintf "the module %s" (Path.show_module module_), None)
  | Field name -> (Printf.sprintf "the field %s" name, None)
  | Result_value -> ("the result, in a specification", None)
  | Old -> ("a value as it was when the function was called", None)
  | Identical -> ("identity of two values, in a specification", None)
  | Yielded -> ("the parts handed out so far, in a specification", None)
  | Finished -> ("whether the method has ended, in a specification", None)
  | Cost_function _ -> ("a cost function", None)
  | Unknown _ -> ("nothing: the name is not known", None)

let contains (span : span) offset = span.start <= offset && offset <= span.stop

(* The innermost expression at an offset, relative to the definition, and
   what it means. *)
let at (definition : definition) (resolved : Resolve.resolved) (checked : Checked.t option) ~text
    offset =
  let best = ref None in
  let rec visit (value : expression) =
    if contains value.span offset then begin
      (match value.kind with
      | Name _ | Member _ | Call _ | Bracket _ -> best := Some value
      | _ -> if !best = None then best := Some value);
      Syntax_walk.children visit value
    end
  in
  Syntax_walk.definition visit definition;
  match !best with
  | None -> None
  | Some value ->
      let written =
        let start = max 0 value.span.start and stop = min (String.length text) value.span.stop in
        if stop > start then String.sub text start (stop - start) else ""
      in
      let meaning, refers_to =
        match value.kind with
        | Name path -> (
            match
              if path.last.id < Array.length resolved.names then resolved.names.(path.last.id)
              else None
            with
            | Some target ->
                let meaning, refers_to = describe_target target in
                (Some meaning, refers_to)
            | None -> (None, None))
        | _ -> (
            match checked with
            | Some checked when value.id < Array.length checked.meanings -> (
                match checked.meanings.(value.id) with
                | Some (Global { path; _ }) ->
                    (Some (Printf.sprintf "the definition %s" (Path.show path)), Some path)
                | Some meaning -> (Some (Checked.show_meaning meaning), None)
                | None -> (None, None))
            | _ -> (None, None))
      in
      let type_ = Option.map (fun checked -> show_type checked value.id) checked in
      Some { text = written; meaning; refers_to; type_ }
