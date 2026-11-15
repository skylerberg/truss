module Names = Resolve.Names

type shown_definition = {
  declaration : Names.declaration;
  file : string;
  line : int;
  text : string;
}

let as_module (names : Names.lookups) written : Path.module_ option =
  match names.split_module written with
  | Some module_ when names.module_exists module_ -> Some module_
  | Some _ | None -> None

let declarations pipeline (module_ : Path.module_) =
  (Pipeline.names pipeline [ module_.package ]).declarations module_
  |> List.filter (fun (declaration : Names.declaration) -> declaration.ordinal = 0)

let visible packages (declaration : Names.declaration) =
  List.mem declaration.file.module_.package packages || Names.is_public declaration.visibility

let owner_of : Path.t -> Path.t option = function
  | Method { owner; _ } | Member_constant { owner; _ } -> Some owner
  | _ -> None

let impl_of_type (path : Path.t) name =
  match path with Impl { for_type; _ } -> for_type.type_name = name | _ -> false

let resolve pipeline packages text =
  let names = Pipeline.names pipeline packages in
  let argument = Path_argument.parse text in
  let in_package package =
    List.filter
      (fun (declaration : Names.declaration) -> declaration.ordinal = 0)
      ((Pipeline.names pipeline [ package ]).package_declarations package)
  in
  let module_ = if argument.member = None then as_module names argument.names else None in
  match (names.split_module argument.names, module_, argument.member) with
  | Some { package; modules = [] }, _, None ->
      List.filter
        (fun (declaration : Names.declaration) -> Names.is_public declaration.visibility)
        (in_package package)
  | _, Some module_, _ -> List.filter (visible packages) (declarations pipeline module_)
  | _, None, member -> (
      match (as_module names (Path_argument.prefix argument), List.rev argument.names) with
      | None, _ | _, [] -> []
      | Some module_, last :: _ -> (
          match member with
          | None -> (
              let path : Path.t = Top { module_; name = last } in
              match
                List.filter
                  (fun (declaration : Names.declaration) -> Path.equal declaration.path path)
                  (declarations pipeline module_)
              with
              | [ declaration ] when declaration.kind = Type ->
                  let package = in_package module_.package in
                  declaration
                  :: List.filter
                       (fun (declaration : Names.declaration) ->
                         match owner_of declaration.path with
                         | Some owning_path -> Path.equal owning_path path
                         | None -> false)
                       package
                  @ List.filter
                      (fun (declaration : Names.declaration) -> impl_of_type declaration.path last)
                      package
                  |> List.filter (visible packages)
              | declarations -> List.filter (visible packages) declarations)
          | Some member ->
              let owner : Path.t = Top { module_; name = last } in
              in_package module_.package
              |> List.filter (fun (declaration : Names.declaration) ->
                  match declaration.path with
                  | Method { owner = owning_path; name; _ }
                  | Member_constant { owner = owning_path; name } ->
                      Path.equal owning_path owner && name = member
                  | _ -> false)
              |> List.filter (visible packages)))

let find snapshot pipeline packages ~body text =
  List.filter_map
    (fun (declaration : Names.declaration) ->
      let key = Names.key_of declaration in
      let opaque =
        declaration.visibility = Public_opaque
        && not (List.mem declaration.file.module_.package packages)
      in
      let names = Pipeline.names pipeline [ key.module_.package ] in
      match Signatures.text names ~body ~opaque key with
      | None -> None
      | Some signature ->
          let file, line =
            match names.base key with
            | Some (written, base) ->
                let source = Command_packages.source snapshot packages written in
                (Source.path source, fst (Source.position source base))
            | None -> ("", 0)
          in
          Some { declaration; file; line; text = signature })
    (resolve pipeline packages text)

let run ~paths ~body =
  let snapshot, packages = Command_packages.current () in
  let pipeline = Database.pipeline snapshot in
  let results = List.map (fun path -> (path, find snapshot pipeline packages ~body path)) paths in
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
