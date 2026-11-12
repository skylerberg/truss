(* The occurrences of each definition, method, and module in a package's
   code, as name resolution and type checking resolved each name. [truss
   rename] edits the occurrences, and [truss impact] finds a definition's
   dependents through them. *)

module Names = Resolve.Names

type target = Definition of Path.t | Module of Path.module_

type occurrence = {
  module_ : Path.module_;  (** The occurrence's file *)
  span : Source.span;  (** In offsets of the file *)
  target : target;
  in_definition : Names.key;  (** The enclosing definition *)
  declares : bool;  (** Whether this occurrence is the definition's declared name *)
}

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

(* Every occurrence in one definition, in order. *)
let of_definition database (key : Names.key) =
  match
    ( Query.demand database Names.definition key,
      Query.demand database Resolve.resolved key,
      Query.demand database Names.base key )
  with
  | Some definition, Some resolved, Some (module_, base) ->
      let names = Syntax_walk.names definition in
      let absolute = Syntax.Span.to_source ~base in
      let occurrence ?(declares = false) span target =
        { module_; span = absolute span; target; in_definition = key; declares }
      in
      let resolved_names =
        List.concat
          (List.mapi
             (fun index (name : Syntax.name) ->
               match
                 if name.id < Array.length resolved.names then resolved.names.(name.id) else None
               with
               | Some (Definition (_, path)) -> [ occurrence name.span (Definition path) ]
               | Some (Module m) ->
                   (* A module is written either as its import's name, one
                      segment, or as its full path: the package's segments
                      followed by each module's. *)
                   let parts = Path.module_parts m in
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
                   [ occurrence (Syntax.Span.make name.span.start last.span.stop) (Module m) ]
               | _ -> [])
             names)
      in
      let declared =
        match declared_name definition with
        | Some name -> [ occurrence ~declares:true name.span (Definition key.path) ]
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
      List.sort (fun a b -> compare a.span.start b.span.start) (declared @ resolved_names @ members)
  | _ -> []

(* Every occurrence in the package's code, in order of file and position. *)
let all (project : Project.t) =
  List.concat_map
    (fun module_ ->
      List.concat_map
        (fun declaration -> of_definition project.context (Names.key_of declaration))
        (Query.demand project.context Names.declarations module_))
    (Project.modules project)

(* The [use] declarations of each file that name a module, with the span of
   the path in offsets of the file. *)
let uses (project : Project.t) (target_module : Path.module_) =
  List.concat_map
    (fun module_ ->
      let file = Project.parsed project module_ in
      List.filter_map
        (fun (item : Syntax.path Syntax.item) ->
          let path = item.value in
          if Names.used_module project.context ~from:module_ path = target_module then
            let first = match path.modules with first :: _ -> first | [] -> path.last in
            Some
              (module_, Source.span (item.base + first.span.start) (item.base + path.last.span.stop))
          else None)
        file.uses)
    (Project.modules project)

(* Whether an occurrence refers to a definition or, for a method, to any
   version of it. *)
let names_definition (definition : Path.t) occurrence =
  match (occurrence.target, definition) with
  | Definition (Method { owner; name; _ }), Method { owner = o; name = n; _ } ->
      Path.equal owner o && name = n
  | Definition path, definition -> Path.equal path definition
  | Module _, _ -> false
