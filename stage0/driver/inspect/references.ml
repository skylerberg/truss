type target = Definition of Path.t | Module of Path.module_
type occurrence = { span : Source.Definition_span.t; target : target }

let find_declared_name (definition : Syntax.definition) : Syntax.name option =
  match definition.kind with
  | Function { signature = { name = Plain_name name | Member_name (_, name); _ }; _ }
  | Method_declaration { name = Plain_name name | Member_name (_, name); _ }
  | Constant { name = Plain_name name | Member_name (_, name); _ }
  | Type_definition { name; _ }
  | Trait { name; _ }
  | Capability { name; _ }
  | Theorem { name; _ } ->
      Some name
  | Impl _ | Test _ | Law_proof _ | Definition_error _ -> None

let list_member_targets (tables : Infer.tables) (definition : Syntax.definition) =
  let members = ref [] in
  let add (name : Syntax.name) path = members := (name, path) :: !members in
  let find_at table id = if id < Array.length table then table.(id) else None in
  let rec visit (expression : Syntax.expression) =
    (match expression.kind with
    | Call ({ kind = Member (_, name); _ }, _) -> (
        match find_at tables.callees expression.id with
        | Some ((Method _ | Member_constant _) as path) -> add name path
        | _ -> ())
    | Member (_, name) -> (
        match find_at tables.resolutions expression.id with
        | Some (Global { path = (Method _ | Member_constant _) as path; _ }) -> add name path
        | _ -> ())
    | _ -> ());
    Syntax_walk.visit_children visit expression
  in
  Syntax_walk.visit_definition visit definition;
  !members

let list_occurrences ~(path : Path.t) (spans : Source.Definition_span.t array)
    (definition : Syntax.definition) (resolved : Resolve.resolved) (tables : Infer.tables option) =
  let names = Syntax_walk.collect_names spans definition in
  let make_occurrence span target = { span; target } in
  let resolved_names =
    List.concat
      (List.mapi
         (fun index (name : Syntax.name) ->
           match
             if name.id < Array.length resolved.names then resolved.names.(name.id) else None
           with
           | Some (Definition (_, path)) -> [ make_occurrence spans.(name.id) (Definition path) ]
           | Some (Module module_) ->
               let parts = Path.list_module_parts module_ in
               let written_in_full =
                 List.length parts > 1
                 && List.for_all Fun.id
                      (List.mapi
                         (fun offset part ->
                           match List.nth_opt names (index + offset) with
                           | Some (written : Syntax.name) -> written.text = part
                           | None -> false)
                         parts)
               in
               let length = if written_in_full then List.length parts - 1 else 0 in
               let last =
                 match List.nth_opt names (index + length) with
                 | Some (last : Syntax.name) -> last
                 | None -> name
               in
               [
                 make_occurrence
                   (Source.Definition_span.make spans.(name.id).start spans.(last.id).stop)
                   (Module module_);
               ]
           | _ -> [])
         names)
  in
  let declared =
    match find_declared_name definition with
    | Some name -> [ make_occurrence spans.(name.id) (Definition path) ]
    | None -> []
  in
  let members =
    match tables with
    | Some tables ->
        List.map
          (fun ((name : Syntax.name), path) -> make_occurrence spans.(name.id) (Definition path))
          (list_member_targets tables definition)
    | None -> []
  in
  List.sort
    (fun left right -> compare left.span.start right.span.start)
    (declared @ resolved_names @ members)

let list_uses ~(resolve_module : Syntax.path -> Path.module_) (items : Syntax.path Syntax.item list)
    =
  List.map
    (fun (item : Syntax.path Syntax.item) ->
      let path = item.value in
      let first = match path.modules with first :: _ -> first | [] -> path.last in
      ( resolve_module path,
        Source.Definition_span.to_file ~base:item.base
          (Source.Definition_span.make item.positions.spans.(first.id).start
             item.positions.spans.(path.last.id).stop) ))
    items

let is_named_by (definition : Path.t) target =
  match (target, definition) with
  | Definition (Method { owner; name; _ }), Method { owner = other_owner; name = other_name; _ } ->
      Path.equal owner other_owner && name = other_name
  | Definition path, definition -> Path.equal path definition
  | Module _, _ -> false
