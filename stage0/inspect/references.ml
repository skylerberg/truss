(* The occurrences of each definition, method, and module in a
   definition's code, as name resolution and type checking resolved each
   name, for [truss rename]. *)

module Names = Resolve.Names

type target = Definition of Path.t | Module of Path.module_
type occurrence = { span : Syntax.span; target : target }

(* The definition's declared name, if it has one. *)
let declared_name (definition : Syntax.definition) : Syntax.name option =
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

(* The method or member that a type-checked expression refers to, if any:
   the callee of a method call on a type, or a method or constant used as a
   value. *)
let member_targets (tables : Infer.tables) (definition : Syntax.definition) =
  let members = ref [] in
  let add (name : Syntax.name) path = members := (name, path) :: !members in
  let at table id = if id < Array.length table then table.(id) else None in
  let rec visit (expression : Syntax.expression) =
    (match expression.kind with
    | Call ({ kind = Member (_, name); _ }, _) -> (
        match at tables.callees expression.id with
        | Some ((Method _ | Member_constant _) as path) -> add name path
        | _ -> ())
    | Member (_, name) -> (
        match at tables.resolutions expression.id with
        | Some (Global { path = (Method _ | Member_constant _) as path; _ }) -> add name path
        | _ -> ())
    | _ -> ());
    Syntax_walk.children visit expression
  in
  Syntax_walk.definition visit definition;
  !members

(* Every occurrence in one definition, in order, in the definition's
   offsets, so that a definition that only moved has the same ones. *)
let occurrences =
  Query.query ~name:"occurrences" ~phase:Phases.inspection ~show:Names.show_key
    (fun database (key : Names.key) ->
      match
        (Query.demand database Names.definition key, Query.demand database Resolve.resolved key)
      with
      | Some definition, Some resolved ->
          let names = Syntax_walk.names definition in
          let occurrence span target = { span; target } in
          let resolved_names =
            List.concat
              (List.mapi
                 (fun index (name : Syntax.name) ->
                   match
                     if name.id < Array.length resolved.names then resolved.names.(name.id)
                     else None
                   with
                   | Some (Definition (_, path)) -> [ occurrence name.span (Definition path) ]
                   | Some (Module module_) ->
                       (* A module is written either as its import's name, one
                      segment, or as its full path: the package's segments
                      followed by each module's. *)
                       let parts = Path.module_parts module_ in
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
                         occurrence
                           (Syntax.Span.make name.span.start last.span.stop)
                           (Module module_);
                       ]
                   | _ -> [])
                 names)
          in
          let declared =
            match declared_name definition with
            | Some name -> [ occurrence name.span (Definition key.path) ]
            | None -> []
          in
          let members =
            match Query.demand database Infer.type_check_result key with
            | Some { tables; _ } ->
                List.map
                  (fun ((name : Syntax.name), path) -> occurrence name.span (Definition path))
                  (member_targets tables definition)
            | None -> []
          in
          List.sort
            (fun left right -> compare left.span.start right.span.start)
            (declared @ resolved_names @ members)
      | _ -> [])

(* Each [use] line of a file, with the module it names and the span of its
   path in the file's offsets. *)
let uses =
  Query.query ~name:"use_lines" ~phase:Phases.inspection ~show:Path.show_file
    (fun database (file : Path.file) ->
      List.map
        (fun (item : Syntax.path Syntax.item) ->
          let path = item.value in
          let first = match path.modules with first :: _ -> first | [] -> path.last in
          ( Names.used_module database ~from:file.module_ path,
            Source.span (item.base + first.span.start) (item.base + path.last.span.stop) ))
        (Query.demand database Parsed.file file).uses)

(* Whether an occurrence refers to a definition or, for a method, to any
   version of it. *)
let names_definition (definition : Path.t) target =
  match (target, definition) with
  | Definition (Method { owner; name; _ }), Method { owner = other_owner; name = other_name; _ } ->
      Path.equal owner other_owner && name = other_name
  | Definition path, definition -> Path.equal path definition
  | Module _, _ -> false
