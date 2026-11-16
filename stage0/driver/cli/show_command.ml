type shown_definition = {
  declaration : Resolve.Names.declaration;
  file : string;
  line : int;
  text : string;
}

let find_module (names : Resolve.Names.lookups) written : Path.module_ option =
  match names.split_module written with
  | Some module_ when names.module_exists module_ -> Some module_
  | Some _ | None -> None

let list_module_declarations database (module_ : Path.module_) =
  (Database.make_name_lookups database [ module_.package ]).declarations module_
  |> List.filter (fun (declaration : Resolve.Names.declaration) -> declaration.ordinal = 0)

let list_package_declarations database package =
  (Database.make_name_lookups database [ package ]).package_declarations package
  |> List.filter (fun (declaration : Resolve.Names.declaration) -> declaration.ordinal = 0)

let is_visible packages (declaration : Resolve.Names.declaration) =
  List.mem declaration.module_.package packages || Resolve.Names.is_public declaration.visibility

let qualify_prelude_name (argument : Path_argument.t) =
  match (argument.prefix, Resolve.Prelude.find_type argument.last) with
  | [], Some module_ -> { argument with prefix = Path.module_parts module_ }
  | _ -> argument

let resolve database packages text =
  let names = Database.make_name_lookups database packages in
  let argument = qualify_prelude_name (Path_argument.parse text) in
  let written = argument.prefix @ [ argument.last ] in
  let module_ = if argument.member = None then find_module names written else None in
  match (names.split_module written, module_, argument.member) with
  | Some { package; modules = [] }, _, None ->
      List.filter
        (fun (declaration : Resolve.Names.declaration) ->
          Resolve.Names.is_public declaration.visibility)
        (list_package_declarations database package)
  | _, Some module_, _ ->
      List.filter (is_visible packages) (list_module_declarations database module_)
  | _, None, member -> (
      match find_module names argument.prefix with
      | None -> []
      | Some module_ -> (
          match member with
          | None -> (
              let path : Path.t = Top { module_; name = argument.last } in
              match
                List.filter
                  (fun (declaration : Resolve.Names.declaration) ->
                    Path.equal declaration.path path)
                  (list_module_declarations database module_)
              with
              | [ declaration ] when declaration.kind = Type ->
                  let package_declarations = list_package_declarations database module_.package in
                  let impls =
                    List.map snd
                      ((Database.make_name_lookups database [ module_.package ]).impls_of_type
                         module_.package path)
                  in
                  declaration
                  :: List.filter
                       (fun (declaration : Resolve.Names.declaration) ->
                         match declaration.path with
                         | Method { owner; _ } | Member_constant { owner; _ } ->
                             Path.equal owner path
                         | _ -> false)
                       package_declarations
                  @ List.filter
                      (fun (declaration : Resolve.Names.declaration) ->
                        List.exists (Path.equal declaration.path) impls)
                      package_declarations
                  |> List.filter (is_visible packages)
              | declarations -> List.filter (is_visible packages) declarations)
          | Some member ->
              let owner : Path.t = Top { module_; name = argument.last } in
              list_package_declarations database module_.package
              |> List.filter (fun (declaration : Resolve.Names.declaration) ->
                  match declaration.path with
                  | Method { owner = owning_path; name; _ }
                  | Member_constant { owner = owning_path; name } ->
                      Path.equal owning_path owner && name = member
                  | _ -> false)
              |> List.filter (is_visible packages)))

let find snapshot database packages ~body text =
  List.map
    (fun (declaration : Resolve.Names.declaration) ->
      let key = Resolve.Names.key_of declaration in
      let opaque =
        declaration.visibility = Public_opaque
        && not (List.mem declaration.module_.package packages)
      in
      let names = Database.make_name_lookups database [ key.module_.package ] in
      let ({ file = written; base } : Resolve.Names.place) = names.place key in
      let source = Command_packages.source snapshot packages written in
      {
        declaration;
        file = Source.path source;
        line = fst (Source.position source base);
        text = Signatures.text names ~body ~opaque key;
      })
    (resolve database packages text)

let run ~paths ~body =
  let snapshot, packages = Command_packages.current () in
  let database = Workspace.open_database snapshot in
  let results = List.map (fun path -> (path, find snapshot database packages ~body path)) paths in
  let missing = List.filter (fun (_, definitions) -> definitions = []) results in
  if Output.json () then
    Json.print
      (Json.document ~diagnostics:[]
         [
           ( "definitions",
             Json.List
               (List.concat_map
                  (fun (_, definitions) ->
                    List.map
                      (fun definition ->
                        Json.Object
                          [
                            ("path", Json.String (Path.show definition.declaration.path));
                            ("kind", Json.String (Signatures.kind_word definition.declaration.kind));
                            ("file", Json.String definition.file);
                            ("line", Json.Int definition.line);
                            ("text", Json.String definition.text);
                          ])
                      definitions)
                  results) );
           ("not_found", Json.List (List.map (fun (path, _) -> Json.String path) missing));
         ])
  else begin
    let first = ref true in
    List.iter
      (fun (_, definitions) ->
        List.iter
          (fun definition ->
            if not !first then Output.print_line "";
            first := false;
            Output.printf "%s:%d\n%s\n" definition.file definition.line definition.text)
          definitions)
      results;
    List.iter (fun (path, _) -> Output.eprintf "Nothing named `%s` is visible here.\n" path) missing
  end;
  if missing = [] then 0 else 2
