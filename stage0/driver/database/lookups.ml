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
  Declarations.make_lookups database.store
    ~note:(fun lookup scope name -> recorder.note Reads (Lookup lookup) scope name)
    ~is_package:(is_package database) ~list_dependency_names:(list_dependency_names database)

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
    list_recursion_group =
      (fun path ->
        Option.value ~default:[]
          (Tracker.find_value database recorder Facts.recursion_group.whole
             (Path.locate_package path) ~id:(Ids.of_path path)));
    requires_run_forever = read_of_key database recorder Facts.requires_run_forever;
  }

let make_package_checks (database : Tracker.t) (recorder : Tracker.recorder) :
    Package_checks.Lookups.t =
  let interface = make_interface database recorder ~is_checked:true in
  let unit_kind = Kind.rank_stage Check_body in
  let definition_kind = Kind.rank_target (Entity Definition) in
  let require_checked package ~generic_kinds =
    recorder.note Reads (Selection Unchecked_bodies) (Ids.of_package package) "";
    if Store.has_unchecked_body database.store ~package:(Path.show_package package) ~generic_kinds
    then raise Tracker.Reads_failed_fact
  in
  let list_edges package selection ~markers =
    recorder.note Reads (Selection selection) (Ids.of_package package) "";
    let keys = Hashtbl.create 64 and paths = Hashtbl.create 64 in
    List.iter
      (fun (declaration : Resolve.Names.declaration) ->
        Hashtbl.replace keys (Ids.of_key declaration.key) declaration.key;
        Hashtbl.replace paths (Ids.of_path declaration.key.path) declaration.key.path)
      (interface.names.list_package_declarations package);
    List.filter_map
      (fun (source, target, edge_markers) ->
        match (Hashtbl.find_opt keys source, Hashtbl.find_opt paths target) with
        | Some key, Some path -> Some (key, path, edge_markers)
        | _ -> None)
      (Store.list_definition_edges database.store ~package:(Path.show_package package) ~unit_kind
         ~target_kind:definition_kind ~markers:(Kind.encode_markers markers))
  in
  {
    interface;
    read_core = read_of_key database recorder Facts.body_form;
    list_uses =
      (fun package ->
        require_checked package ~generic_kinds:[];
        List.map
          (fun (key, path, _) -> (key, path))
          (list_edges package Body_uses ~markers:[ References ]));
    list_instantiations =
      (fun package ->
        require_checked package
          ~generic_kinds:[ Declarations.rank_kind Function; Declarations.rank_kind Method ];
        List.map
          (fun ((key : Resolve.Names.key), callee, markers) ->
            (key.path, callee, Kind.has_marker markers Grows))
          (list_edges package Instantiations ~markers:[ Instantiates ]));
    list_used_packages =
      (fun package ->
        require_checked package ~generic_kinds:[];
        recorder.note Reads (Selection Package_references) (Ids.of_package package) "";
        List.filter_map Path.parse_package
          (Store.list_definition_edge_names database.store ~package:(Path.show_package package)
             ~unit_kind
             ~target_kind:(Kind.rank_target (Entity Package))));
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
