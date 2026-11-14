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

(* A [todo] or an [echo] of a definition, at its span relative to the
   definition. A [todo] expression has its id; a type defined as [todo] has
   none and is at its name. *)
type unfinished = { keyword : [ `Todo | `Echo ]; id : id option; span : span }

(* Each [todo] and [echo] of a definition, in source order. *)
let unfinished (definition : definition) =
  let found = ref [] in
  let add keyword id (span : span) = found := { keyword; id; span } :: !found in
  let rec visit (value : expression) =
    (match value.kind with
    | Todo -> add `Todo (Some value.id) value.span
    | Echo _ -> add `Echo (Some value.id) value.span
    | _ -> ());
    Syntax_walk.children visit value
  in
  Syntax_walk.definition visit definition;
  (match definition.kind with
  | Type_definition { name; body = Type_todo; _ } -> add `Todo None name.span
  | _ -> ());
  List.sort (fun left right -> compare left.span.start right.span.start) !found

(* Each [todo] of a definition, in source order. Name resolution records
   the bindings in scope at each [todo], and the type checker's tables give
   their types. *)
let holes (definition : definition) (resolved : Resolve.resolved) (tables : Infer.tables) =
  List.filter_map
    (fun { keyword; id; span } ->
      match (keyword, id) with
      | `Echo, _ -> None
      | `Todo, None -> Some { offset = span.start; expected = None; scope = [] }
      | `Todo, Some id ->
          Option.map
            (fun scope ->
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
            (List.assoc_opt id resolved.holes))
    (unfinished definition)

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
