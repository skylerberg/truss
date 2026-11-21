module References = References

let find_at table id = if id < Array.length table then table.(id) else None

let show_type (tables : Infer.tables) id =
  match find_at tables.types id with
  | Some (Types.Error _ | Types.Hole) -> "not decided yet"
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

let show_local_type (tables : Infer.tables) id =
  match find_at tables.local_types id with
  | Some type_ -> Types.show type_
  | None -> "an unknown type"

let show_from_tables (tables : Infer.tables option) show id =
  match tables with Some tables -> show tables id | None -> "an unknown type"

type unfinished = {
  keyword : [ `Todo | `Echo ];
  id : Syntax.id option;
  span : Source.Definition_span.t;
}

let list_unfinished (spans : Source.Definition_span.t array) (definition : Syntax.definition) =
  let found = ref [] in
  let add keyword id (span : Source.Definition_span.t) = found := { keyword; id; span } :: !found in
  let rec visit (value : Syntax.expression) =
    (match value.kind with
    | Todo -> add `Todo (Some value.id) spans.(value.id)
    | Echo _ -> add `Echo (Some value.id) spans.(value.id)
    | _ -> ());
    Syntax_walk.visit_children visit value
  in
  Syntax_walk.visit_definition visit definition;
  (match definition.kind with
  | Type_definition { name; body = Type_todo; _ } -> add `Todo None spans.(name.id)
  | _ -> ());
  List.sort (fun left right -> compare left.span.start right.span.start) !found

type hole = { offset : int; expected : string option; scope : (string * string) list }

let list_holes spans definition (resolved : Resolve.resolved) tables =
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
                expected = Some (show_from_tables tables show_type id);
                scope =
                  List.map
                    (fun (name, (value : Resolve.value)) ->
                      ( name,
                        match value with
                        | Value_local binding -> show_from_tables tables show_local_type binding
                        | Value_generic _ -> "UInt64"
                        | Value_field _ -> "a field"
                        | Value_law_parameter _ -> "a parameter of the law" ))
                    scope;
              })
            (List.assoc_opt id resolved.holes))
    (list_unfinished spans definition)

type explanation = {
  text : string;
  meaning : string option;
  refers_to : Path.t option;
  type_ : string option;
}

let describe_target (target : Resolve.target) =
  match target with
  | Definition (_, path) -> (Printf.sprintf "the definition %s" (Path.show path), Some path)
  | Local _ -> ("a local variable or parameter", None)
  | Law_parameter _ -> ("a parameter of the law that this proves", None)
  | Binding -> ("a name bound here", None)
  | Type_parameter _ | Value_parameter _ -> ("a generic parameter", None)
  | Capability_parameter _ -> ("a capability parameter", None)
  | Variant (path, name) -> (Printf.sprintf "the variant %s of %s" name (Path.show path), None)
  | Module { module_; _ } -> (Printf.sprintf "the module %s" (Path.show_module module_), None)
  | Field name -> (Printf.sprintf "the field %s" name, None)
  | Result_value -> ("the result, in a specification", None)
  | Old -> ("a value as it was when the function was called", None)
  | Identical -> ("identity of two values, in a specification", None)
  | Visited -> ("the values of the loop's iterations before, in a loop's clauses", None)
  | Final -> ("a lending method's part as the caller left it, in its `ensures`", None)
  | Specification_function _ -> ("a specification function", None)
  | Unknown _ -> ("nothing: the name is not known", None)

let explain_resolved (resolved : Resolve.resolved) (name : Syntax.name) =
  match find_at resolved.names name.id with
  | Some target ->
      let meaning, refers_to = describe_target target in
      (Some meaning, refers_to)
  | None -> (None, None)

let explain_definition path = (Some (Printf.sprintf "the definition %s" (Path.show path)), Some path)
let is_inside (span : Source.Definition_span.t) offset = span.start <= offset && offset <= span.stop

let find_known_type (tables : Infer.tables) id =
  Option.map (fun _ -> show_type tables id) (find_at tables.types id)

let explain_name ~(path : Path.t) (definition : Syntax.definition) (resolved : Resolve.resolved)
    (tables : Infer.tables option) (name : Syntax.name) =
  let is_declared =
    match References.find_declared_name definition with
    | Some declared -> declared.id = name.id
    | None -> false
  in
  let meaning, refers_to =
    if is_declared then explain_definition path else explain_resolved resolved name
  in
  let type_ =
    Option.bind tables (fun (tables : Infer.tables) ->
        Option.map Types.show (find_at tables.local_types name.id))
  in
  { text = name.text; meaning; refers_to; type_ }

let explain_at ~path (spans : Source.Definition_span.t array) (definition : Syntax.definition)
    (resolved : Resolve.resolved) (tables : Infer.tables option) ~text offset =
  let innermost = ref None in
  let calls = Hashtbl.create 8 in
  let rec visit (value : Syntax.expression) =
    if is_inside spans.(value.id) offset then begin
      (match value.kind with
      | Call (({ kind = Member _; _ } as callee), _) -> Hashtbl.replace calls callee.id value.id
      | _ -> ());
      (match value.kind with
      | Name _ | Member _ | Call _ | Bracket _ -> innermost := Some value
      | _ -> if !innermost = None then innermost := Some value);
      Syntax_walk.visit_children visit value
    end
  in
  Syntax_walk.visit_definition visit definition;
  let name_at =
    List.find_opt
      (fun (name : Syntax.name) -> is_inside spans.(name.id) offset)
      (Syntax_walk.collect_names spans definition)
  in
  let is_written_in (value : Syntax.expression) (name : Syntax.name) =
    match value.kind with Name written | Member (_, written) -> written.id = name.id | _ -> false
  in
  match (!innermost, name_at) with
  | Some value, Some name when not (is_written_in value name) ->
      Some (explain_name ~path definition resolved tables name)
  | None, Some name -> Some (explain_name ~path definition resolved tables name)
  | None, None -> None
  | Some value, _ ->
      let written = Source.Definition_span.quote text spans.(value.id) in
      let meaning, refers_to =
        match value.kind with
        | Name name -> explain_resolved resolved name
        | _ -> (
            match tables with
            | Some tables -> (
                match find_at tables.resolutions value.id with
                | Some (Global { path; _ }) -> explain_definition path
                | Some resolution -> (Some (Infer.show_resolution resolution), None)
                | None -> (
                    match
                      Option.bind (Hashtbl.find_opt calls value.id) (find_at tables.callees)
                    with
                    | Some callee -> explain_definition callee
                    | None -> (None, None)))
            | None -> (None, None))
      in
      let type_ = Option.bind tables (fun tables -> find_known_type tables value.id) in
      Some { text = written; meaning; refers_to; type_ }
