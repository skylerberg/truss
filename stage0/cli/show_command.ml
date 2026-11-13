(* [truss show]: prints the signatures at each path. *)

module Names = Resolve.Names

type shown_definition = {
  declaration : Names.declaration;
  file : string;
  line : int;
  text : string;
}

(* The module a path names, if it names one: [weather], or
   [weather::forecast]. *)
let as_module database names : Path.module_ option =
  match Workspace.split_module database names with
  | Some module_ when Query.demand database Workspace.module_exists module_ -> Some module_
  | Some _ | None -> None

let declarations database (module_ : Path.module_) =
  Query.demand database Names.declarations module_
  |> List.filter (fun (declaration : Names.declaration) -> declaration.ordinal = 0)

let package_modules database package = Query.demand database Workspace.modules package

(* Whether a definition is visible from the command's packages: every
   definition in them, and only public definitions elsewhere. *)
let visible (project : Project.t) (declaration : Names.declaration) =
  Project.is_own project declaration.file.module_ || Names.is_public declaration.visibility

let owner_of : Path.t -> Path.t option = function
  | Method { owner; _ } | Member_constant { owner; _ } -> Some owner
  | _ -> None

(* An [impl] is shown with a type when its self type has the type's
   name. *)
let impl_of_type (path : Path.t) name =
  match path with Impl { for_type; _ } -> for_type.type_name = name | _ -> false

(* The definitions a path names, in printing order. *)
let resolve (project : Project.t) text =
  let database = project.context in
  let argument = Path_argument.parse text in
  let in_package package =
    List.concat_map (declarations database) (package_modules database package)
  in
  let module_ = if argument.member = None then as_module database argument.names else None in
  match (Workspace.split_module database argument.names, module_, argument.member) with
  | Some { package; modules = [] }, _, None ->
      (* A package: its public definitions. *)
      List.filter
        (fun (declaration : Names.declaration) -> Names.is_public declaration.visibility)
        (in_package package)
  | _, Some module_, _ -> List.filter (visible project) (declarations database module_)
  | _, None, member -> (
      match (as_module database (Path_argument.prefix argument), List.rev argument.names) with
      | None, _ | _, [] -> []
      | Some module_, last :: _ -> (
          match member with
          | None -> (
              let path : Path.t = Top { module_; name = last } in
              match
                List.filter
                  (fun (declaration : Names.declaration) -> Path.equal declaration.path path)
                  (declarations database module_)
              with
              | [ declaration ] when declaration.kind = Type ->
                  (* A type, then its methods and constants, then its impls. *)
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
                  |> List.filter (visible project)
              | declarations -> List.filter (visible project) declarations)
          | Some member ->
              let owner : Path.t = Top { module_; name = last } in
              in_package module_.package
              |> List.filter (fun (declaration : Names.declaration) ->
                  match declaration.path with
                  | Method { owner = owning_path; name; _ }
                  | Member_constant { owner = owning_path; name } ->
                      Path.equal owning_path owner && name = member
                  | _ -> false)
              |> List.filter (visible project)))

let find (project : Project.t) ~body text =
  List.filter_map
    (fun (declaration : Names.declaration) ->
      let key = Names.key_of declaration in
      let opaque =
        declaration.visibility = Public_opaque
        && not (Project.is_own project declaration.file.module_)
      in
      match Signatures.text project.context ~body ~opaque key with
      | None -> None
      | Some signature ->
          let file, line =
            match Query.demand project.context Names.base key with
            | Some (written, base) ->
                let source = Project.source project written in
                (Source.path source, fst (Source.position source base))
            | None -> ("", 0)
          in
          Some { declaration; file; line; text = signature })
    (resolve project text)

let run ~directory ~paths ~body ~json =
  let project = Project.load directory in
  let results = List.map (fun path -> (path, find project ~body path)) paths in
  let missing = List.filter (fun (_, definitions) -> definitions = []) results in
  if json then
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
  (* A path that names nothing is a bad argument, not an error in the
   code. *)
  if missing = [] then 0 else 2
