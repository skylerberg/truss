(* [truss show]: the signatures at each path. *)

module Names = Resolve.Names

type found = { declaration : Names.declaration; file : string; line : int; text : string }

(* The module a path names, if it names one: [weather], or
   [weather::forecast]. *)
let as_module database parts : Path.module_ option =
  match Workspace.split_path database parts with
  | None -> None
  | Some (package, modules) ->
      let module_ : Path.module_ = { package; modules } in
      if Query.demand database Workspace.module_exists module_ then Some module_ else None

let declarations database (module_ : Path.module_) =
  Query.demand database Names.declarations module_
  |> List.filter (fun (d : Names.declaration) -> d.ordinal = 0)

(* Every module of a package. *)
let package_modules database package =
  match Workspace.package database package with Some p -> p.modules | None -> []

(* Whether the packages a command is about can see a definition: anything
   in them, and only what is public elsewhere. *)
let visible (project : Project.t) (declaration : Names.declaration) =
  Project.is_own project declaration.module_ || Names.is_public declaration.visibility

let owner_of : Path.t -> Path.t option = function
  | Method { owner; _ } | Member_constant { owner; _ } -> Some owner
  | _ -> None

(* An [impl] is shown with a type when its name, which spells its trait
   and type as written, ends with the type's name. *)
let impl_of_type (path : Path.t) name =
  match path with
  | Impl { name = impl; _ } ->
      let suffix = " for " ^ name in
      let n = String.length suffix and m = String.length impl in
      let rec at i =
        i + n <= m
        && ((String.sub impl i n = suffix && (i + n = m || impl.[i + n] = '[')) || at (i + 1))
      in
      at 0
  | _ -> false

(* The definitions a path names, in the order to show them. *)
let resolve (project : Project.t) text =
  let database = project.context in
  let parts = String.split_on_char ':' text |> List.filter (( <> ) "") in
  let in_package package =
    List.concat_map (declarations database) (package_modules database package)
  in
  match (Workspace.split_path database parts, as_module database parts) with
  | Some (package, []), _ ->
      (* A package: what it makes public. *)
      List.filter (fun (d : Names.declaration) -> Names.is_public d.visibility) (in_package package)
  | _, Some module_ -> List.filter (visible project) (declarations database module_)
  | _, None -> (
      match List.rev parts with
      | [] -> []
      | last :: rest -> (
          let modules = List.rev rest in
          match (as_module database modules, String.index_opt last '.') with
          | None, _ -> []
          | Some module_, None -> (
              let path : Path.t = Top { module_; name = last } in
              match
                List.filter
                  (fun (d : Names.declaration) -> Path.equal d.path path)
                  (declarations database module_)
              with
              | [ declaration ] when declaration.kind = Type ->
                  (* A type, then its methods and constants, then its impls. *)
                  let package = in_package module_.package in
                  declaration
                  :: List.filter
                       (fun (d : Names.declaration) ->
                         match owner_of d.path with Some o -> Path.equal o path | None -> false)
                       package
                  @ List.filter (fun (d : Names.declaration) -> impl_of_type d.path last) package
                  |> List.filter (visible project)
              | found -> List.filter (visible project) found)
          | Some module_, Some dot ->
              let type_name = String.sub last 0 dot in
              let member = String.sub last (dot + 1) (String.length last - dot - 1) in
              let owner : Path.t = Top { module_; name = type_name } in
              in_package module_.package
              |> List.filter (fun (d : Names.declaration) ->
                  match d.path with
                  | Method { owner = o; name; _ } | Member_constant { owner = o; name } ->
                      Path.equal o owner && name = member
                  | _ -> false)
              |> List.filter (visible project)))

let find (project : Project.t) ~body text =
  List.filter_map
    (fun (declaration : Names.declaration) ->
      let key = Names.key_of declaration in
      let opaque =
        declaration.visibility = Public_opaque && not (Project.is_own project declaration.module_)
      in
      match Signatures.text project.context ~body ~opaque key with
      | None -> None
      | Some signature ->
          let file, line =
            match Query.demand project.context Names.base key with
            | Some (module_, base) ->
                let source = Project.source project module_ in
                (Source.path source, fst (Source.position source base))
            | None -> ("", 0)
          in
          Some { declaration; file; line; text = signature })
    (resolve project text)

let run ~directory ~paths ~body ~json =
  let project = Project.load directory in
  let found = List.map (fun path -> (path, find project ~body path)) paths in
  let missing = List.filter (fun (_, found) -> found = []) found in
  if json then
    Json.print
      (Json.document ~diagnostics:[]
         [
           ( "definitions",
             Json.List
               (List.concat_map
                  (fun (_, found) ->
                    List.map
                      (fun f ->
                        Json.Object
                          [
                            ("path", Json.String (Path.show f.declaration.path));
                            ("kind", Json.String (Signatures.kind_word f.declaration.kind));
                            ("file", Json.String f.file);
                            ("line", Json.Int f.line);
                            ("text", Json.String f.text);
                          ])
                      found)
                  found) );
           ("not_found", Json.List (List.map (fun (path, _) -> Json.String path) missing));
         ])
  else begin
    let first = ref true in
    List.iter
      (fun (_, found) ->
        List.iter
          (fun f ->
            if not !first then Output.print_line "";
            first := false;
            Output.printf "%s:%d\n%s\n" f.file f.line f.text)
          found)
      found;
    List.iter (fun (path, _) -> Output.eprintf "Nothing named `%s` is visible here.\n" path) missing
  end;
  (* A path that names nothing is a bad argument, not a problem in the code. *)
  if missing = [] then 0 else 2
