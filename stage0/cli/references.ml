(* Where each definition, method, and module is named in a package's code,
   from what resolution and type checking decided each name means. [truss
   rename] edits these places, and [truss impact] finds what depends on a
   definition through them. *)

module Names = Resolve.Names

type target = Definition of Path.t | Module of Path.module_

type occurrence = {
  module_ : Path.module_;  (** The file it is in *)
  span : Source.span;  (** In the file's offsets *)
  target : target;
  in_definition : Names.key;  (** The definition it is written in *)
  declares : bool;  (** Whether this is the name a definition declares itself with *)
}

(* The name a definition declares itself with, if it has one. *)
let declared_name (definition : Syntax.definition) : Syntax.name option =
  match definition.kind with
  | Function { signature = { name = Plain_name name | Member_name (_, name); _ }; _ }
  | Constant { name = Plain_name name | Member_name (_, name); _ }
  | Type_definition { name; _ }
  | Trait { name; _ }
  | Capability { name; _ }
  | Theorem { name; _ } ->
      Some name
  | Impl _ | Test _ | Law_proof _ | Definition_error _ -> None

(* The method or member a type-checked expression names, if any: a call to
   a type's own method, or a method or constant used as a value. *)
let member_targets (checked : Checked.t) (definition : Syntax.definition) =
  let found = ref [] in
  let add (name : Syntax.name) path = found := (name, path) :: !found in
  let at table id = if id < Array.length table then table.(id) else None in
  let rec visit (expression : Syntax.expression) =
    (match expression.kind with
    | Call ({ kind = Member (_, name); _ }, _) -> (
        match at checked.calls expression.id with
        | Some { callee = Function { path = (Method _ | Member_constant _) as path; _ }; _ } ->
            add name path
        | _ -> ())
    | Member (_, name) -> (
        match at checked.meanings expression.id with
        | Some (Global { path = (Method _ | Member_constant _) as path; _ }) -> add name path
        | _ -> ())
    | _ -> ());
    Syntax_walk.children visit expression
  in
  Syntax_walk.definition visit definition;
  !found

(* Every occurrence in one definition, in order. *)
let of_definition database (key : Names.key) =
  match
    ( Query.demand database Names.definition key,
      Query.demand database Resolve.resolved key,
      Query.demand database Names.base key )
  with
  | Some definition, Some resolved, Some (module_, base) ->
      let names = Syntax_walk.names definition in
      let absolute (span : Syntax.span) = Source.span (base + span.start) (base + span.stop) in
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
               | Some (Definition path) -> [ occurrence name.span (Definition path) ]
               | Some (Module m) ->
                   (* A module is written as its import's name, one name, or
                      as its full path, the package's name and then each
                      module's, which follow it among the names. *)
                   let length =
                     if name.text = m.package && m.modules <> [] then List.length m.modules else 0
                   in
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
        match Query.demand database Infer.checked key with
        | Some { checked; _ } ->
            List.map
              (fun ((name : Syntax.name), path) -> occurrence name.span (Definition path))
              (member_targets checked definition)
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

(* The [use] lines that name a module: each file's, with the span of the
   path in the file's offsets. *)
let uses (project : Project.t) (wanted : Path.module_) =
  List.concat_map
    (fun module_ ->
      let file = Project.parsed project module_ in
      List.filter_map
        (fun (item : Syntax.path Syntax.item) ->
          let path = item.value in
          if Names.used_module path = wanted then
            let first = match path.modules with first :: _ -> first | [] -> path.last in
            Some
              (module_, Source.span (item.base + first.span.start) (item.base + path.last.span.stop))
          else None)
        file.uses)
    (Project.modules project)

(* Whether an occurrence names a definition or, for a method, any version
   of it. *)
let names_definition (wanted : Path.t) occurrence =
  match (occurrence.target, wanted) with
  | Definition (Method { owner; name; _ }), Method { owner = o; name = n; _ } ->
      Path.equal owner o && name = n
  | Definition path, wanted -> Path.equal path wanted
  | Module _, _ -> false

(* The definitions, apart from itself, whose code names [wanted]. *)
let dependents occurrences (wanted : Path.t) =
  List.filter_map
    (fun occurrence ->
      if
        names_definition wanted occurrence
        && (not occurrence.declares)
        && not (Path.equal occurrence.in_definition.path wanted)
      then Some occurrence.in_definition.path
      else None)
    occurrences
  |> List.sort_uniq Path.compare
