(* Queries about one definition for the agent tools: its holes, with each
   one's expected type and the bindings in scope, and the name or
   expression at a position. They only read the type checker's results. *)

open Syntax

type hole = {
  offset : int;  (** Relative to the definition *)
  expected : string option;  (** The hole's expected type, or [None] for a type defined as [todo] *)
  scope : (string * string) list;  (** Each binding in scope with its type, sorted by name *)
}

let at table id = if id < Array.length table then table.(id) else None

(* A type as the tools print it. The type checker's tables hold no
   unsolved type variable, so an unconstrained [todo], such as an
   interpolated one, has the error type, which is printed as not decided
   yet. *)
let show_type (tables : Infer.tables) id =
  match at tables.types id with
  | Some (Types.Error _ | Types.Hole) -> "not decided yet"
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

let local_type (tables : Infer.tables) id =
  match at tables.local_types id with Some type_ -> Types.show type_ | None -> "an unknown type"

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

(* The meaning of a name that name resolution resolved, and the
   definition it refers to. *)
let resolved_meaning (resolved : Resolve.resolved) (name : name) =
  match at resolved.names name.id with
  | Some target ->
      let meaning, refers_to = describe_target target in
      (Some meaning, refers_to)
  | None -> (None, None)

let definition_meaning path = (Some (Printf.sprintf "the definition %s" (Path.show path)), Some path)
let contains (span : span) offset = span.start <= offset && offset <= span.stop

(* An expression's type, or [None] where the type checker recorded none,
   as for a method call's callee. *)
let known_type (tables : Infer.tables) id =
  Option.map (fun _ -> show_type tables id) (at tables.types id)

(* The meaning of a name that is not an expression: the definition's
   declared name, a binding, or a type or trait named in a signature. *)
let explain_name ~(path : Path.t) (definition : definition) (resolved : Resolve.resolved)
    (tables : Infer.tables option) (name : name) =
  let is_declared =
    match References.declared_name definition with
    | Some declared -> declared.id = name.id
    | None -> false
  in
  let meaning, refers_to =
    if is_declared then definition_meaning path else resolved_meaning resolved name
  in
  let type_ =
    Option.bind tables (fun (tables : Infer.tables) ->
        Option.map Types.show (at tables.local_types name.id))
  in
  { text = name.text; meaning; refers_to; type_ }

(* The name or expression at an offset in the definition [path], relative
   to the definition, and its meaning. The innermost [Name], [Member],
   [Call], or [Bracket] expression at the offset is explained, or else the
   innermost expression. A name at the offset that the expression does not
   write, such as the declared name or a parameter, is explained instead. *)
let explain_at ~path (definition : definition) (resolved : Resolve.resolved)
    (tables : Infer.tables option) ~text offset =
  let innermost = ref None in
  (* The call of each method callee, by the callee's id: the type checker
     records the callee's path by the call's id. *)
  let calls = Hashtbl.create 8 in
  let rec visit (value : expression) =
    if contains value.span offset then begin
      (match value.kind with
      | Call (({ kind = Member _; _ } as callee), _) -> Hashtbl.replace calls callee.id value.id
      | _ -> ());
      (match value.kind with
      | Name _ | Member _ | Call _ | Bracket _ -> innermost := Some value
      | _ -> if !innermost = None then innermost := Some value);
      Syntax_walk.children visit value
    end
  in
  Syntax_walk.definition visit definition;
  let name_at =
    List.find_opt (fun (name : name) -> contains name.span offset) (Syntax_walk.names definition)
  in
  (* Whether a name is written as part of an expression: a [Name]'s path,
     or a [Member]'s member. *)
  let is_written_in (value : expression) (name : name) =
    match value.kind with
    | Name written ->
        List.exists (fun (part : name) -> part.id = name.id) (written.last :: written.modules)
    | Member (_, member) -> member.id = name.id
    | _ -> false
  in
  match (!innermost, name_at) with
  | Some value, Some name when not (is_written_in value name) ->
      Some (explain_name ~path definition resolved tables name)
  | None, Some name -> Some (explain_name ~path definition resolved tables name)
  | None, None -> None
  | Some value, _ ->
      let written =
        let start = max 0 value.span.start and stop = min (String.length text) value.span.stop in
        if stop > start then String.sub text start (stop - start) else ""
      in
      let meaning, refers_to =
        match value.kind with
        | Name path -> resolved_meaning resolved path.last
        | _ -> (
            match tables with
            | Some tables -> (
                match at tables.resolutions value.id with
                | Some (Global { path; _ }) -> definition_meaning path
                | Some resolution -> (Some (Infer.show_resolution resolution), None)
                | None -> (
                    match Option.bind (Hashtbl.find_opt calls value.id) (at tables.callees) with
                    | Some callee -> definition_meaning callee
                    | None -> (None, None)))
            | None -> (None, None))
      in
      let type_ = Option.bind tables (fun tables -> known_type tables value.id) in
      Some { text = written; meaning; refers_to; type_ }
