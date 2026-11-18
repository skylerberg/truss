type shown_definition = {
  declaration : Resolve.Names.declaration;
  file : string;
  line : int;
  text : string;
}

let list_top_level (names : Resolve.Names.lookups) declarations =
  List.filter
    (fun (declaration : Resolve.Names.declaration) ->
      declaration.ordinal = 0 && names.find_container (Resolve.Names.make_key declaration) = None)
    declarations

let list_type_parts declarations (type_ : Path.t) =
  let is_member (declaration : Resolve.Names.declaration) =
    match declaration.path with
    | Method { owner; _ } | Member_constant { owner; _ } -> Path.equal owner type_
    | _ -> false
  and is_impl (declaration : Resolve.Names.declaration) =
    match declaration.path with Impl { for_type; _ } -> Path.equal for_type type_ | _ -> false
  in
  List.filter is_member declarations @ List.filter is_impl declarations

let list_target_declarations (names : Resolve.Names.lookups) packages :
    Path_argument.target -> Resolve.Names.declaration list = function
  | Package package ->
      List.filter
        (fun (declaration : Resolve.Names.declaration) ->
          Resolve.Names.is_public declaration.visibility)
        (list_top_level names (names.list_package_declarations package))
  | Module module_ ->
      List.filter
        (Path_argument.is_shown names packages)
        (list_top_level names (names.list_declarations module_))
  | Definition path -> (
      let declared = Option.to_list (Option.map names.read_declaration (names.find_key path)) in
      match Resolve.Names.find_kind names path with
      | Some Type ->
          declared @ list_type_parts (Path_argument.list_shown_declarations names packages) path
      | Some (Function | Trait | Capability | Constant | Theorem) | None -> declared)

let show_definition snapshot database (names : Resolve.Names.lookups) packages ~body
    (declaration : Resolve.Names.declaration) =
  let key = Resolve.Names.make_key declaration in
  let opaque =
    declaration.visibility = Public_opaque && not (List.mem declaration.module_.package packages)
  in
  let ({ file = written; base } : Resolve.Names.place) = names.read_place key in
  let source = Command_packages.read_source snapshot database packages written in
  {
    declaration;
    file = Source.path source;
    line = fst (Source.compute_position source base);
    text = Signatures.render_signature names ~body ~opaque key;
  }

let find snapshot database names packages ~body text =
  match Path_argument.resolve names packages (Path_argument.parse text) with
  | [] -> None
  | targets ->
      Some
        (List.map
           (show_definition snapshot database names packages ~body)
           (List.concat_map (list_target_declarations names packages) targets))

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
                      [
                        ("path", Json.String (Path.show definition.declaration.path));
                        ("kind", Json.String (Signatures.show_kind definition.declaration.kind));
                        ("file", Json.String definition.file);
                        ("line", Json.Int definition.line);
                        ("text", Json.String definition.text);
                      ])
                  (List.concat_map list_definitions results)) );
           ("not_found", Json.List (List.map (fun (path, _) -> Json.String path) missing));
         ])
  else begin
    let first = ref true in
    List.iter
      (fun definition ->
        if not !first then Output.print_line "";
        first := false;
        Output.printf "%s:%d\n%s\n" definition.file definition.line definition.text)
      (List.concat_map list_definitions results);
    List.iter
      (fun (path, definitions) ->
        match definitions with
        | None -> Output.eprintf "Nothing named `%s` is visible here.\n" path
        | Some [] -> Output.eprintf "`%s` is visible here but has no definition to show.\n" path
        | Some (_ :: _) -> ())
      results
  end;
  if missing = [] then 0 else 2
