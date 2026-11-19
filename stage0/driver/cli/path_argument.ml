type t = { prefix : string list; last : string; member : string option }

let parse text =
  let refuse () =
    Outcome.raise_cannot_run
      "`%s` is not a path, such as `weather::forecast::parse` or \
       `weather::forecast::Forecast.summary`."
      text
  in
  match Option.map List.rev (Path.parse_names text) with
  | Some (last :: rest) -> (
      let prefix = List.rev rest in
      match String.split_on_char '.' last with
      | [ last ] -> { prefix; last; member = None }
      | [ last; member ] when last <> "" && member <> "" -> { prefix; last; member = Some member }
      | _ -> refuse ())
  | Some [] | None -> refuse ()

type target = Package of Path.package | Module of Path.module_ | Definition of Path.t

let is_visible packages (module_ : Path.module_) visibility =
  List.mem module_.package packages || Resolve.Names.is_public visibility

let is_shown packages (declaration : Resolve.Names.declaration) =
  is_visible packages declaration.key.module_ declaration.visibility

let list_shown_declarations (names : Resolve.Names.lookups) packages =
  List.sort_uniq Path.compare_package
    (packages @ List.concat_map (Resolve.Names.list_transitive_dependencies names) packages)
  |> List.concat_map names.list_package_declarations
  |> List.filter (fun (declaration : Resolve.Names.declaration) ->
      declaration.key.ordinal = 0 && is_shown packages declaration)

let find_module (names : Resolve.Names.lookups) written =
  match names.split_module written with
  | Some module_ when names.module_exists module_ -> Some module_
  | Some _ | None -> None

let list_bare_name_modules (names : Resolve.Names.lookups) packages name =
  match
    List.filter
      (fun module_ -> Option.is_some (names.find module_ name))
      (List.map (fun package : Path.module_ -> { package; modules = [] }) packages)
  with
  | [] -> Option.to_list (Resolve.Prelude.find_type name)
  | roots -> roots

let resolve_exactly (names : Resolve.Names.lookups) packages written =
  match (names.split_module written, find_module names written) with
  | Some { package; modules = [] }, _ -> [ Package package ]
  | _, Some module_ -> [ Module module_ ]
  | _, None -> (
      match List.rev written with
      | [] -> []
      | name :: reversed_prefix ->
          List.filter_map
            (fun (module_ : Path.module_) ->
              match names.find module_ name with
              | Some entry when is_visible packages module_ entry.visibility ->
                  Some (Definition (Top { module_; name }))
              | Some _ | None -> None)
            (match List.rev reversed_prefix with
            | [] -> list_bare_name_modules names packages name
            | prefix -> Option.to_list (find_module names prefix)))

let has_suffix names ~suffix =
  let skipped = List.length names - List.length suffix in
  skipped >= 0 && List.drop skipped names = suffix

let is_top_named written : Path.t -> bool = function
  | Top { module_; name } -> has_suffix (Path.list_module_parts module_ @ [ name ]) ~suffix:written
  | _ -> false

let find_member : Path.t -> (Path.t * string) option = function
  | Method { owner; name; _ } | Member_constant { owner; name } -> Some (owner, name)
  | _ -> None

let resolve_by_suffix declarations written =
  List.filter_map
    (fun (declaration : Resolve.Names.declaration) ->
      let is_named =
        is_top_named written declaration.key.path
        ||
        match (written, find_member declaration.key.path) with
        | [ last ], Some (_, name) -> name = last
        | _ -> false
      in
      if is_named then Some (Definition declaration.key.path) else None)
    declarations

let resolve_members names packages declarations owners member =
  let is_member_of type_ (declaration : Resolve.Names.declaration) =
    match find_member declaration.key.path with
    | Some ((Impl { for_type = owner; _ } | owner), name) -> name = member && Path.equal owner type_
    | None -> false
  in
  List.concat_map
    (fun owner ->
      List.map
        (fun (declaration : Resolve.Names.declaration) -> Definition declaration.key.path)
        (List.filter (is_member_of owner) declarations)
      @ List.map
          (fun (_, method_) -> Definition method_)
          (Resolve.Names.list_view_methods names ~is_visible:(is_shown packages) owner member))
    owners

let resolve names packages argument =
  let written = argument.prefix @ [ argument.last ] in
  let exact = resolve_exactly names packages written in
  let declarations = lazy (list_shown_declarations names packages) in
  match argument.member with
  | None -> if exact = [] then resolve_by_suffix (Lazy.force declarations) written else exact
  | Some member ->
      let owners =
        match List.filter_map (function Definition path -> Some path | _ -> None) exact with
        | [] ->
            List.filter_map
              (fun (declaration : Resolve.Names.declaration) ->
                if is_top_named written declaration.key.path then Some declaration.key.path
                else None)
              (Lazy.force declarations)
        | owners -> owners
      in
      resolve_members names packages (Lazy.force declarations) owners member
