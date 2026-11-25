let is_package (database : Tracker.t) package =
  List.mem package (Store.list_project database.store)
  || Store.locate_schema database.store package <> Main

let is_worked_on (database : Tracker.t) package =
  List.mem package (Store.list_project database.store)

let list_dependency_names (database : Tracker.t) (package : Path.package) =
  List.filter_map
    (fun (dependency : Store.dependency) -> Path.parse_package dependency.dependency)
    (Store.list_dependencies database.store
       (Store.locate_schema database.store package)
       ~package:(Path.show_package package))

let sort_in_dependency_order database packages =
  let visited = Hashtbl.create 8 in
  let order = ref [] in
  let rec visit package =
    if not (Hashtbl.mem visited package) then begin
      Hashtbl.replace visited package ();
      List.iter visit (List.sort Path.compare_package (list_dependency_names database package));
      order := package :: !order
    end
  in
  visit Path.standard_package;
  List.iter visit packages;
  List.rev !order

let make_names (database : Tracker.t) (recorder : Tracker.recorder) =
  let names =
    Declarations.make_lookups database.store
      ~note:(fun lookup scope name -> recorder.note Reads (Lookup lookup) scope name)
      ~is_package:(is_package database) ~list_dependency_names:(list_dependency_names database)
  in
  if recorder == Tracker.untracked then names
  else
    {
      names with
      list_package_declarations =
        (fun _ ->
          Compiler_bug.raise_bug ~stage:"Database"
            "a unit lists the declarations of a package, and no edge records that read");
    }

let make_interface (database : Tracker.t) (recorder : Tracker.recorder) ~is_checked :
    Interface.Lookups.t =
  let names = make_names database recorder in
  let of_key view (key : Resolve.Names.key) read =
    read database recorder view key.module_.package ~id:(Ids.of_key key)
  in
  let of_path view path read =
    read database recorder view (Path.locate_package path) ~id:(Ids.of_path path)
  in
  let interface = if is_checked then Facts.checked_interface else Facts.interface in
  let read_interface key = of_key interface key Tracker.read_value in
  let find_interface (path : Path.t) =
    match path with
    | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ } ->
        if module_ = Well_known.intrinsic_module then None
        else of_key interface { module_; path; ordinal = 0 } Tracker.find_value
    | Method _ | Member_constant _ -> Option.map read_interface (names.find_key path)
    | Derived _ | Unresolved _ -> None
  in
  {
    names;
    read_resolved =
      (fun section key -> of_key (Facts.resolved section).whole key Tracker.read_value);
    find_trait_header =
      (fun path ->
        Option.bind (names.find_key path) (fun key ->
            of_key Facts.trait_header.whole key Tracker.find_value));
    find_constant_value =
      (fun path -> Option.join (of_path Facts.constant_value.whole path Tracker.find_value));
    find_header = (fun key -> of_key Facts.header.whole key Tracker.find_value);
    read_interface;
    find_interface;
    read_elaborated_interface =
      (fun key ->
        of_key
          (if is_checked then Facts.checked_elaborated else Facts.elaborated.whole)
          key Tracker.read_value);
    find_derived_interface =
      (fun ~type_ ~trait ->
        Option.iter (fun key -> ignore (read_interface key)) (names.find_key type_);
        of_path Facts.derived_interface.whole (Path.Derived { type_; trait }) Tracker.find_value);
    read_type_facts = (fun path -> of_path Facts.type_facts.whole path Tracker.read_value);
    find_grant =
      (fun package dependency ->
        Tracker.find_value database recorder Facts.grant.whole package
          ~id:(Ids.of_dependency package dependency));
  }

let read_of_key (database : Tracker.t) recorder view (key : Resolve.Names.key) =
  Tracker.read_value database recorder view key.module_.package ~id:(Ids.of_key key)

let make_infer database recorder : Infer.Lookups.t =
  {
    interface = make_interface database recorder ~is_checked:true;
    read_contract = read_of_key database recorder Facts.contract.whole;
  }

let list_group (database : Tracker.t) recorder (group : Path.t list Tracker.fact) path =
  Option.value ~default:[]
    (Tracker.find_value database recorder group.whole (Path.locate_package path)
       ~id:(Ids.of_path path))

let list_recursion_group database recorder = list_group database recorder Facts.recursion_group

let make_usage database recorder : Usage.Lookups.t =
  {
    interface = make_interface database recorder ~is_checked:true;
    read_resolved =
      (fun key ->
        Resolve.merge
          (List.map
             (fun section -> read_of_key database recorder (Facts.resolved section).whole key)
             Resolve.sections));
    read_tables = read_of_key database recorder Facts.body_tables;
    uses_run_forever = read_of_key database recorder Facts.uses_run_forever;
    is_recursive = (fun path -> list_recursion_group database recorder path <> []);
  }

let make_ownership database recorder : Ownership.Lookups.t =
  {
    find_code =
      (fun key ->
        match read_of_key database recorder Facts.body_mir.whole key with
        | Body code | Initializer code -> Some code
        | No_code -> None);
    list_places_without_keyword =
      (fun key -> fst (read_of_key database recorder Facts.ownership_modes key));
    list_mode_keywords = (fun key -> snd (read_of_key database recorder Facts.ownership_modes key));
    interface = make_interface database recorder ~is_checked:true;
  }

let make_mir (database : Tracker.t) recorder : Mir.lookups =
  let read_of_path view path =
    Tracker.read_value database recorder view (Path.locate_package path) ~id:(Ids.of_path path)
  in
  {
    find_form_origin =
      Interface.find_form_origin (make_interface database recorder ~is_checked:true)
        ~is_derived:(fun path ->
          Option.is_some
            (Tracker.find database recorder Facts.generated_mir.whole (Path.locate_package path)
               ~id:(Ids.of_path path)));
    read_body_part = read_of_key database recorder Facts.body_mir.whole;
    read_contract_part = read_of_key database recorder Facts.contract_mir.whole;
    read_generated_parts = read_of_path Facts.generated_mir.whole;
  }

let make_call_edges database recorder : Mir.Call_edges.lookups =
  {
    interface = make_interface database recorder ~is_checked:true;
    mir = make_mir database recorder;
  }

let read_source (database : Tracker.t) (recorder : Tracker.recorder) (file : Path.file) =
  let id = Ids.of_file file in
  recorder.note Reads (Lookup Source) id "";
  match
    Store.find_file database.store (Store.locate_schema database.store file.module_.package) ~id
  with
  | Some row -> Source.create ~path:(Path.show_file file) row.text
  | None ->
      Compiler_bug.raise_bug ~stage:"Database" "%s is not a file of the build" (Path.show_file file)

let make_proof (database : Tracker.t) (recorder : Tracker.recorder) : Prover.Lookups.t =
  {
    read_source = read_source database recorder;
    interface = make_interface database recorder ~is_checked:true;
    mir = make_mir database recorder;
    list_must_be_disjoint = read_of_key database recorder Facts.ownership.whole;
    list_recursion_group = list_recursion_group database recorder;
    list_proof_group = list_group database recorder Facts.proof_group;
  }

let make_package_checks (database : Tracker.t) (recorder : Tracker.recorder) :
    Package_checks.Lookups.t =
  let body_kind = Kind.rank_stage Check_body in
  let definition_kind = Kind.rank_target (Entity Definition) in
  let references = Kind.encode_markers [ References ] in
  let list_body_targets (key : Resolve.Names.key) ~markers =
    Store.list_target_definitions database.store
      ~source:(Tracker.locate_unit Check_body (Ids.of_key key))
      ~target_kind:definition_kind ~markers:(Kind.encode_markers markers)
      ~origin:Declarations.written_origin
  in
  let require_untracked () =
    if recorder != Tracker.untracked then
      Compiler_bug.raise_bug ~stage:"Database"
        "a unit reads the uses of a definition, and no edge records that read"
  in
  let rec list_users_from path ~from_ () =
    match
      Store.find_source_definition database.store
        ~target:(Tracker.locate (Entity Definition) (Ids.of_path path) "")
        ~source_kind:body_kind ~markers:references ~from_
    with
    | Some row ->
        Seq.Cons (Declarations.decode_declaration row, list_users_from path ~from_:(row.id + 1))
    | None -> Seq.Nil
  in
  {
    interface = make_interface database recorder ~is_checked:true;
    list_tests =
      (fun package name ->
        recorder.note Reads (Lookup Tests) (Ids.of_package package) name;
        Declarations.list_tests database.store package name);
    list_instantiations =
      (fun key ->
        require_untracked ();
        List.map
          (fun ((row : Store.definition), markers) ->
            (Declarations.decode_key row.key, Kind.has_marker markers Grows))
          (list_body_targets key ~markers:[ Instantiates ]));
    list_users =
      (fun path ->
        require_untracked ();
        list_users_from path ~from_:min_int);
    list_used =
      (fun key ->
        require_untracked ();
        List.map
          (fun (row, _) -> Declarations.decode_declaration row)
          (list_body_targets key ~markers:[ References ]));
    was_unused =
      (fun path ->
        require_untracked ();
        Store.has_diagnostic database.store
          ~stage:(Kind.rank_stage Check_unexported)
          ~unit:(Ids.of_path path));
    is_package_used =
      (fun ~by dependency ->
        let name = Path.show_package dependency in
        recorder.note Reads (Selection Package_references) (Ids.of_package by) name;
        Store.has_source database.store
          ~target:(Tracker.locate (Entity Package) (Ids.of_package by) name)
          ~source_kind:body_kind ~markers:references);
  }

let locate_items (database : Tracker.t) =
  match Store.list_project database.store with
  | package :: _ -> package
  | [] -> Compiler_bug.raise_bug ~stage:"Database" "code is lowered in a database with no project"

let make_lowering database recorder : Lowering.Lookups.t =
  {
    interface = make_interface database recorder ~is_checked:true;
    mir = make_mir database recorder;
  }
