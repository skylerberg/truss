(* Queries about one definition for the agent tools: its holes, with each
   one's expected type and the bindings in scope, and the expression at a
   position. They only read the type checker's results. *)

open Syntax

type hole = {
  offset : int;  (** Relative to the definition *)
  expected : string option;  (** The hole's expected type, or [None] for a type defined as [todo] *)
  scope : (string * string) list;  (** Each binding in scope with its type, sorted by name *)
}

(* A type as the tools print it. The type checker's tables hold no
   unsolved type variable, so an unconstrained [todo], such as an
   interpolated one, has the error type, which is printed as not decided
   yet. *)
let show_type (tables : Infer.tables) id =
  match if id < Array.length tables.types then tables.types.(id) else None with
  | Some (Types.Error _ | Types.Hole) -> "not decided yet"
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

let local_type (tables : Infer.tables) id =
  match if id < Array.length tables.local_types then tables.local_types.(id) else None with
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

let expression_span (definition : definition) id =
  let span = ref None in
  let rec visit (value : expression) =
    if value.id = id then span := Some value.span else Syntax_walk.children visit value
  in
  Syntax_walk.definition visit definition;
  !span

(* Each [todo] of a definition, in source order. Name resolution records
   the bindings in scope at each [todo], and the type checker's tables give
   their types. *)
let holes (definition : definition) (resolved : Resolve.resolved) (tables : Infer.tables) =
  let values =
    List.filter_map
      (fun (id, scope) ->
        Option.map
          (fun (span : span) ->
            {
              offset = span.start;
              expected = Some (show_type tables id);
              scope =
                List.map
                  (fun (name, (value : Resolve.value)) ->
                    ( name,
                      match value with
                      | Value_local binding -> local_type tables binding
                      | Value_generic _ -> "USize"
                      | Value_field _ -> "a field"
                      | Value_law_parameter _ -> "a parameter of the law" ))
                  scope;
            })
          (expression_span definition id))
      resolved.holes
  in
  match definition.kind with
  | Type_definition { name; body = Type_todo; _ } ->
      { offset = name.span.start; expected = None; scope = [] } :: values
  | _ -> values

type explanation = {
  text : string;  (** The name or expression as written *)
  meaning : string option;  (** The meaning of a name *)
  refers_to : Path.t option;  (** The definition a name refers to, for its signature *)
  type_ : string option;
}

let describe_target (target : Resolve.target) =
  match target with
  | Definition (_, path) -> (Printf.sprintf "the definition %s" (Path.show path), Some path)
  | Local _ -> ("a local variable or parameter", None)
  | Law_parameter _ -> ("a parameter of the law that this proves", None)
  | Binding -> ("a name bound here", None)
  | Type_parameter _ | Capability_parameter _ | Value_parameter _ -> ("a generic parameter", None)
  | Variant (path, name) -> (Printf.sprintf "the variant %s of %s" name (Path.show path), None)
  | Module module_ -> (Printf.sprintf "the module %s" (Path.show_module module_), None)
  | Field name -> (Printf.sprintf "the field %s" name, None)
  | Result_value -> ("the result, in a specification", None)
  | Old -> ("a value as it was when the function was called", None)
  | Identical -> ("identity of two values, in a specification", None)
  | Yielded -> ("the parts yielded so far, in a specification", None)
  | Finished -> ("whether the method has ended, in a specification", None)
  | Specification_function _ -> ("a specification function", None)
  | Unknown _ -> ("nothing: the name is not known", None)

let contains (span : span) offset = span.start <= offset && offset <= span.stop

(* The innermost expression at an offset relative to the definition, and
   its meaning. *)
let explain_at (definition : definition) (resolved : Resolve.resolved)
    (tables : Infer.tables option) ~text offset =
  let innermost = ref None in
  let rec visit (value : expression) =
    if contains value.span offset then begin
      (match value.kind with
      | Name _ | Member _ | Call _ | Bracket _ -> innermost := Some value
      | _ -> if !innermost = None then innermost := Some value);
      Syntax_walk.children visit value
    end
  in
  Syntax_walk.definition visit definition;
  match !innermost with
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
            match tables with
            | Some tables when value.id < Array.length tables.resolutions -> (
                match tables.resolutions.(value.id) with
                | Some (Global { path; _ }) ->
                    (Some (Printf.sprintf "the definition %s" (Path.show path)), Some path)
                | Some resolution -> (Some (Infer.show_resolution resolution), None)
                | None -> (None, None))
            | _ -> (None, None))
      in
      let type_ = Option.map (fun tables -> show_type tables value.id) tables in
      Some { text = written; meaning; refers_to; type_ }
