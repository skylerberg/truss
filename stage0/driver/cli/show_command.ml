type shown_definition = {
  declaration : Resolve.Names.declaration;
  impl : Path.t option;
  file : string;
  line : int;
  text : string;
}

let list_top_level (names : Resolve.Names.lookups) declarations =
  List.filter
    (fun (declaration : Resolve.Names.declaration) ->
      declaration.key.ordinal = 0 && names.find_container declaration.key = None)
    declarations

let list_type_parts declarations (type_ : Path.t) =
  let is_member (declaration : Resolve.Names.declaration) =
    match declaration.key.path with
    | Method { owner; _ } | Member_constant { owner; _ } -> Path.equal owner type_
    | _ -> false
  and is_impl (declaration : Resolve.Names.declaration) =
    match declaration.key.path with Impl { for_type; _ } -> Path.equal for_type type_ | _ -> false
  in
  List.filter is_member declarations
  @ Path_argument.list_view_methods declarations type_
  @ List.filter is_impl declarations

let list_target_declarations (names : Resolve.Names.lookups) packages :
    Path_argument.target -> Resolve.Names.declaration list = function
  | Package package ->
      List.filter
        (fun (declaration : Resolve.Names.declaration) ->
          Resolve.Names.is_public declaration.visibility)
        (list_top_level names (names.list_package_declarations package))
  | Module module_ ->
      List.filter (Path_argument.is_shown packages)
        (list_top_level names (names.list_declarations module_))
  | Definition path -> (
      let declared = Option.to_list (Option.map names.read_declaration (names.find_key path)) in
      match Resolve.Names.find_kind names path with
      | Some Type ->
          declared @ list_type_parts (Path_argument.list_shown_declarations names packages) path
      | Some (Function | Trait | Capability | Constant | Theorem) | None -> declared)
  | Trait_member { member; _ } ->
      Option.to_list (Option.map names.read_declaration (names.find_key member))

let show_definition snapshot database (names : Resolve.Names.lookups) packages ~body ~impl
    (declaration : Resolve.Names.declaration) =
  let key = declaration.key in
  let opaque =
    declaration.visibility = Public_opaque && not (List.mem key.module_.package packages)
  in
  let ({ file = written; base } : Resolve.Names.place) = names.read_place key in
  let source = Command_packages.read_source snapshot database written in
  {
    declaration;
    impl;
    file = Source.path source;
    line = fst (Source.compute_position source base);
    text = Signatures.render_signature names ~body ~opaque key;
  }

let find snapshot database names packages ~body text =
  match Path_argument.resolve names packages (Path_argument.parse text) with
  | [] -> None
  | targets ->
      Some
        (List.concat_map
           (fun (target : Path_argument.target) ->
             let impl =
               match target with
               | Trait_member { impl; _ } -> Some impl
               | Package _ | Module _ | Definition _ -> None
             in
             List.map
               (show_definition snapshot database names packages ~body ~impl)
               (list_target_declarations names packages target))
           targets)

let describe_impl (definition : shown_definition) =
  let member = Path.show_name definition.declaration.key.path in
  match definition.impl with
  | Some (Impl { trait; for_type; _ }) ->
      Some
        (Printf.sprintf "`%s` has `%s` from its impl of `%s`." (Path.show_name for_type) member
           (Path.show_name trait.path))
  | Some (Derived { type_; trait }) ->
      Some
        (Printf.sprintf "`%s` has `%s` because it derives `%s`." (Path.show_name type_) member
           (Path.show_name trait))
  | Some _ | None -> None

let run ~paths ~body =
  let snapshot, packages = Command_packages.load_current () in
  let database = Workspace.open_database snapshot in
  let names = Database.make_name_lookups database in
  let results =
    List.map (fun path -> (path, find snapshot database names packages ~body path)) paths
  in
  let missing = List.filter (fun (_, definitions) -> definitions = None) results in
  let list_definitions (_, definitions) = Option.value ~default:[] definitions in
  if Output.json () then
    Json.print
      (Json.make_document ~diagnostics:[]
         [
           ( "definitions",
             Json.List
               (List.map
                  (fun definition ->
                    Json.Object
                      ([
                         ("path", Json.String (Path.show definition.declaration.key.path));
                         ("kind", Json.String (Signatures.show_kind definition.declaration.kind));
                         ("file", Json.String definition.file);
                         ("line", Json.Int definition.line);
                         ("text", Json.String definition.text);
                       ]
                      @ List.map
                          (fun impl -> ("impl", Json.String (Path.show impl)))
                          (Option.to_list definition.impl)))
                  (List.concat_map list_definitions results)) );
           ("not_found", Json.List (List.map (fun (path, _) -> Json.String path) missing));
         ])
  else begin
    let first = ref true in
    List.iter
      (fun definition ->
        if not !first then Output.print_line "";
        first := false;
        Option.iter Output.print_line (describe_impl definition);
        Output.printf "%s:%d\n%s\n" definition.file definition.line definition.text)
      (List.concat_map list_definitions results);
    List.iter
      (fun (path, definitions) ->
        match definitions with
        | None -> Output.eprint_line (Path_argument.explain_missing names packages path)
        | Some [] -> Output.eprintf "`%s` is visible here but has no definition to show.\n" path
        | Some (_ :: _) -> ())
      results
  end;
  if missing = [] then 0 else 2
