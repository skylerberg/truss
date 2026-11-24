type t = { prefix : string list; last : string; member : string option }

let parse text =
  let refuse () =
    Outcome.raise_cannot_run
      "`%s` is not a path, such as `weather.forecast.parse` or `weather.forecast.Forecast.summary`."
      text
  in
  let is_type_name name = Char.uppercase_ascii name.[0] = name.[0] in
  match Option.map List.rev (Path.parse_names text) with
  | Some (member :: last :: rest) when is_type_name last ->
      { prefix = List.rev rest; last; member = Some member }
  | Some (last :: rest) -> { prefix = List.rev rest; last; member = None }
  | Some [] | None -> refuse ()

type target =
  | Package of Path.package
  | Module of Path.module_
  | Definition of Path.t
  | Trait_member of { member : Path.t; impl : Path.t }

let is_visible packages (module_ : Path.module_) visibility =
  Resolve.Names.is_public visibility
  || List.exists
       (fun package -> Resolve.Names.is_visible_to_package ~package module_ visibility)
       packages

let is_shown packages (declaration : Resolve.Names.declaration) =
  is_visible packages declaration.key.module_ declaration.visibility

let list_shown_packages (names : Resolve.Names.lookups) packages =
  List.sort_uniq Path.compare_package
    (packages @ List.concat_map (Resolve.Names.list_transitive_dependencies names) packages)

let list_shown_declarations (names : Resolve.Names.lookups) packages =
  list_shown_packages names packages
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

let is_member_of type_ (declaration : Resolve.Names.declaration) =
  match find_member declaration.key.path with
  | Some (Impl { for_type = owner; _ }, _) | Some (owner, _) -> Path.equal owner type_
  | None -> false

let list_view_methods declarations type_ =
  match Well_known.find_view type_ with
  | None -> []
  | Some view ->
      let own_overloads =
        List.filter_map
          (fun (declaration : Resolve.Names.declaration) ->
            match declaration.key.path with
            | Method { name; receiver; _ } when is_member_of type_ declaration ->
                Some (name, receiver)
            | _ -> None)
          declarations
      in
      List.filter
        (fun (declaration : Resolve.Names.declaration) ->
          match declaration.key.path with
          | Method { owner; name; receiver = Instance _ as receiver } ->
              Path.equal owner view && not (List.mem (name, receiver) own_overloads)
          | _ -> false)
        declarations

let list_named_members declarations member =
  List.filter
    (fun (declaration : Resolve.Names.declaration) ->
      match find_member declaration.key.path with Some (_, name) -> name = member | None -> false)
    declarations

let list_implemented_traits (names : Resolve.Names.lookups) packages type_ =
  let list_impls type_ =
    List.concat_map
      (fun package -> names.list_impls_of_type package type_)
      (list_shown_packages names packages)
  in
  List.fold_left
    (fun traits (trait, impl) ->
      if List.exists (fun (kept, _) -> Path.equal kept trait) traits then traits
      else traits @ [ (trait, impl) ])
    []
    (list_impls type_ @ Option.fold ~none:[] ~some:list_impls (Well_known.find_view type_))

let list_type_members names packages candidates type_ =
  let is_written_in impl (declaration : Resolve.Names.declaration) =
    match find_member declaration.key.path with
    | Some (owner, _) -> Path.equal owner impl
    | None -> false
  in
  let list_trait_members (trait, impl) =
    if List.exists (is_written_in impl) candidates then []
    else
      List.filter_map
        (fun (declaration : Resolve.Names.declaration) ->
          match declaration.key.path with
          | Method { owner; _ } when Path.equal owner trait ->
              Some (Trait_member { member = declaration.key.path; impl })
          | _ -> None)
        candidates
  in
  List.map
    (fun (declaration : Resolve.Names.declaration) -> Definition declaration.key.path)
    (List.filter (is_member_of type_) candidates @ list_view_methods candidates type_)
  @ List.concat_map list_trait_members (list_implemented_traits names packages type_)

let list_owners (names : Resolve.Names.lookups) packages argument declarations =
  let written = argument.prefix @ [ argument.last ] in
  match
    List.filter_map
      (function Definition path -> Some path | Package _ | Module _ | Trait_member _ -> None)
      (resolve_exactly names packages written)
  with
  | [] ->
      List.filter_map
        (fun (declaration : Resolve.Names.declaration) ->
          if is_top_named written declaration.key.path then Some declaration.key.path else None)
        (Lazy.force declarations)
  | owners -> owners

let resolve names packages argument =
  let declarations = lazy (list_shown_declarations names packages) in
  match argument.member with
  | None -> (
      let written = argument.prefix @ [ argument.last ] in
      match resolve_exactly names packages written with
      | [] -> resolve_by_suffix (Lazy.force declarations) written
      | exact -> exact)
  | Some member ->
      let candidates = list_named_members (Lazy.force declarations) member in
      List.concat_map
        (list_type_members names packages candidates)
        (list_owners names packages argument declarations)

let is_related ~type_ other =
  let name = Path.show_name type_ and other_name = Path.show_name other in
  (not (Path.equal type_ other))
  && (String.includes ~affix:name other_name
     || String.includes ~affix:other_name name
     || Option.exists (Path.equal other) (Well_known.find_view type_)
     || Option.exists (Path.equal type_) (Well_known.find_view other))

let explain_missing names packages text =
  let argument = parse text in
  let declarations = lazy (list_shown_declarations names packages) in
  match argument.member with
  | None -> Printf.sprintf "Nothing named `%s` is visible here." text
  | Some member -> (
      match list_owners names packages argument declarations with
      | [] -> Printf.sprintf "Nothing named `%s` is visible here." text
      | owners ->
          let candidates = list_named_members (Lazy.force declarations) member in
          let types =
            List.sort_uniq Path.compare
              (List.filter_map
                 (fun (declaration : Resolve.Names.declaration) ->
                   if
                     declaration.kind = Type
                     && List.exists (fun type_ -> is_related ~type_ declaration.key.path) owners
                   then Some declaration.key.path
                   else None)
                 (Lazy.force declarations))
          in
          let related =
            List.sort_uniq String.compare
              (List.filter_map
                 (fun type_ ->
                   if list_type_members names packages candidates type_ = [] then None
                   else Some (Printf.sprintf "`%s.%s`" (Path.show_name type_) member))
                 types)
          in
          let existing =
            match related with
            | [] -> ""
            | [ only ] -> Printf.sprintf " %s exists." only
            | _ -> Printf.sprintf " %s exist." (Output.show_list related)
          in
          Printf.sprintf
            "`%s` has no member `%s`.%s `truss show %s` lists its methods and its impls."
            argument.last member existing
            (String.concat "." (argument.prefix @ [ argument.last ])))
