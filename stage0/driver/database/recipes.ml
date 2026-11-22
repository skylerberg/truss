type unit_id = Of_definition | Of_path

type definition_stage = {
  stage : Kind.stage;
  unit_id : unit_id;
  applies : Store.definition -> bool;
  facts : Tracker.any_fact list;
  run : Tracker.t -> Store.definition -> unit;
}

let reads = Kind.encode_markers [ Reads ]
let file_stages : Kind.stage list = [ Parse; Check_imports ]
let references = Kind.encode_markers [ References ]

let read_file (database : Tracker.t) id =
  match Store.find_file database.store Main ~id with
  | Some file -> (Declarations.decode_file file.key, file.text)
  | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale file has no row"

let parse (file : Path.file) text =
  Parser.parse_source (Source.create ~path:(Path.show_file file) text)

let replace_entries (database : Tracker.t) ~source (module_ : Path.module_) ~file_name entries =
  let module_id = Ids.of_module module_ in
  let names = Lookups.make_names database Tracker.untracked in
  let entries = List.mapi (Declarations.encode_entry ~source ~module_ ~file_name) entries in
  let entries_before = Store.list_file_entries database.store ~file:source in
  if entries_before <> entries then begin
    let list_names rows = List.map (fun (entry : Store.entry) -> entry.name) rows in
    let touched = List.sort_uniq String.compare (list_names entries_before @ list_names entries) in
    let entries_found_before = List.map (names.find module_) touched in
    let existed = names.module_exists module_ in
    Store.replace_file_entries database.store ~file:source entries;
    List.iter2
      (fun name before ->
        if names.find module_ name <> before then
          Tracker.mark_readers database (Lookup Entry) module_id name)
      touched entries_found_before;
    Tracker.mark_readers database (Lookup Entries) module_id "";
    if names.module_exists module_ <> existed then
      Tracker.mark_readers database (Lookup Module) module_id ""
  end;
  entries_before <> entries

let replace_builtin_entries database =
  ignore
    (replace_entries database
       ~source:(Ids.of_module Well_known.intrinsic_module)
       Well_known.intrinsic_module ~file_name:"" Resolve.Namespace.builtin_entries)

let run_parse (database : Tracker.t) id =
  let file, text = read_file database id in
  let tree, diagnostics =
    Tracker.record database Parse id (fun recorder ->
        recorder.note Reads (Lookup Source) id "";
        parse file text)
  in
  let is_diagnosed_otherwise =
    Tracker.replace_file_diagnostics database Parse ~package:file.module_.package ~file:id
      diagnostics
  in
  let is_named_otherwise =
    replace_entries database ~source:id file.module_ ~file_name:file.name
      (Resolve.Namespace.list_entries tree)
  in
  Tracker.report Parse id ~is_changed:(is_diagnosed_otherwise || is_named_otherwise)

let write_file (database : Tracker.t) ~package (file : Path.file) text =
  let id = Ids.of_file file and module_id = Ids.of_module file.module_ in
  let names = Lookups.make_names database Tracker.untracked in
  let existed = names.module_exists file.module_ in
  let is_new = Option.is_none (Store.find_file database.store Main ~id) in
  Store.replace_file database.store
    { id; package; module_ = module_id; name = file.name; key = Ids.encode file; text };
  Store.replace_module database.store ~id:module_id ~package ~name:(Path.show_module file.module_)
    ~key:(Ids.encode file.module_);
  List.iter (fun stage -> Tracker.mark_stale database stage id) file_stages;
  Tracker.mark_stale database Declare module_id;
  Tracker.mark_readers database (Lookup Source) id "";
  if is_new then Tracker.mark_readers database (Lookup Files) module_id "";
  if not existed then Tracker.mark_readers database (Lookup Module) module_id ""

let remove_file (database : Tracker.t) (file : Path.file) =
  let id = Ids.of_file file and module_id = Ids.of_module file.module_ in
  if Option.is_some (Store.find_file database.store Main ~id) then begin
    Store.remove_file database.store ~id;
    ignore (replace_entries database ~source:id file.module_ ~file_name:file.name []);
    Store.replace_imports database.store ~file:id [];
    List.iter (fun stage -> Tracker.forget database stage id ~facts:[]) file_stages;
    Tracker.mark_stale database Declare module_id;
    Tracker.mark_readers database (Lookup Source) id "";
    Tracker.mark_readers database (Lookup Files) module_id "";
    if not ((Lookups.make_names database Tracker.untracked).module_exists file.module_) then
      Tracker.mark_readers database (Lookup Module) module_id ""
  end

let is_unresolved : Tracker.state option -> bool = function
  | Some (Has_failed | Is_blocked) -> true
  | Some Has_value | None -> false

let run_resolve (database : Tracker.t) (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  let outcomes =
    Tracker.record database Resolve row.id (fun recorder ->
        let names = Lookups.make_names database recorder in
        List.map
          (fun (section, outcome) ->
            match (outcome : (Resolve.resolution, _) result option) with
            | Some (Ok { resolved; used_imports }) ->
                List.iter
                  (fun path ->
                    if not (Path.equal path key.path) then
                      recorder.note References (Entity Definition) (Ids.of_path path) "")
                  (Resolve.list_referenced_definitions resolved);
                Option.iter
                  (fun file ->
                    List.iter (recorder.note References (Entity Import) file) used_imports)
                  row.file;
                (section, Tracker.Value resolved, [])
            | Some (Error diagnostics) -> (section, Failed, diagnostics)
            | None -> (section, Blocked, []))
          (Resolve.resolve names key))
  in
  let states_before =
    List.map
      (fun (section, outcome, _) ->
        Tracker.write database (Facts.resolved section) ~id:row.id (Some outcome))
      outcomes
  in
  let is_unresolved_now =
    List.exists
      (fun (_, outcome, _) ->
        match outcome with Tracker.Value _ -> false | Failed | Blocked -> true)
      outcomes
  in
  if List.exists is_unresolved states_before <> is_unresolved_now then
    Option.iter (fun file -> Tracker.mark_readers database (Selection Unresolved) file "") row.file;
  let has_failed = List.exists (fun (_, _, diagnostics) -> diagnostics <> []) outcomes in
  if List.mem (Some Tracker.Has_failed) states_before || has_failed then
    Tracker.replace_definition_diagnostics database Resolve ~package:key.module_.package
      ~definition:row.id
      (List.concat_map (fun (_, _, diagnostics) -> diagnostics) outcomes)

let run_check_imports (database : Tracker.t) id =
  let file, text = read_file database id in
  let diagnostics =
    Tracker.record database Check_imports id (fun recorder ->
        recorder.note Reads (Lookup Source) id "";
        recorder.note Reads (Selection Unresolved) id "";
        recorder.note Reads (Selection Import_references) id "";
        Resolve.list_file_diagnostics
          (Lookups.make_names database recorder)
          file
          (fst (parse file text))
          ~text
          ~used:
            (if Store.has_unresolved database.store ~file:id then None
             else
               Some
                 (Store.list_names_of_edges_into database.store
                    ~kind:(Kind.rank_target (Entity Import))
                    ~id ~markers:references)))
  in
  Tracker.report Check_imports id
    ~is_changed:
      (Tracker.replace_file_diagnostics database Check_imports ~package:file.module_.package
         ~file:id diagnostics)

let block compute = try compute () with Tracker.Reads_failed_fact -> (Tracker.Blocked, [])

let run_fact database stage fact (row : Store.definition) ~id compute =
  let outcome, diagnostics =
    Tracker.record database stage id (fun recorder -> block (fun () -> compute recorder))
  in
  let state_before = Tracker.write database fact ~id (Some outcome) in
  if state_before = Some Tracker.Has_failed || diagnostics <> [] then
    Tracker.replace_definition_diagnostics database stage
      ~package:(Declarations.decode_key row.key).module_.package ~definition:id diagnostics

let run_trait_header database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Read_trait_header Facts.trait_header row ~id:row.id (fun recorder ->
      let definition = (Lookups.make_names database recorder).read_definition key in
      let resolved =
        Tracker.read_value database recorder (Facts.resolved Interface).whole key.module_.package
          ~id:row.id
      in
      match Resolve.make_trait_header definition resolved with
      | Some header -> (Value header, [])
      | None -> (Blocked, []))

let run_constant_value database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Evaluate_constant Facts.constant_value row ~id:row.path (fun recorder ->
      ( Value
          (Interface.Constants.evaluate_constant
             (Lookups.make_interface database recorder ~is_checked:false)
             key.path),
        [] ))

let run_header database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Elaborate_header Facts.header row ~id:row.id (fun recorder ->
      match
        Interface.Elaborator.elaborate_header
          (Lookups.make_interface database recorder ~is_checked:false)
          key
      with
      | Ok header -> (Value header, [])
      | Error [] -> (Blocked, [])
      | Error diagnostics -> (Failed, diagnostics))

let run_elaborate database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Elaborate Facts.elaborated row ~id:row.id (fun recorder ->
      let elaborated =
        Interface.Elaborator.elaborate_definition
          (Lookups.make_interface database recorder ~is_checked:false)
          key
      in
      match (elaborated.diagnostics, elaborated.interface) with
      | [], Error_interface _ -> (Blocked, [])
      | [], _ -> (Value elaborated, [])
      | diagnostics, _ -> (Failed, diagnostics))

let run_derive_interface database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Derive_interface Facts.derived_interface row ~id:row.path (fun recorder ->
      match key.path with
      | Derived { type_; trait } -> (
          match
            Interface.Impls.derive_interface
              (Lookups.make_interface database recorder ~is_checked:false)
              ~type_ ~trait
          with
          | Some interface -> (Value interface, [])
          | None -> (Blocked, []))
      | _ -> Compiler_bug.raise_bug ~stage:"Database" "%s is no derived impl" (Path.show key.path))

let find_type_interface lookups path =
  try Interface.Definition.find_type_interface lookups path with Tracker.Reads_failed_fact -> None

let run_type_facts (database : Tracker.t) paths =
  let facts =
    Tracker.record_group database Compute_type_facts (List.map Ids.of_path paths)
      ~own:[ Type_facts ] (fun recorder ->
        let lookups = Lookups.make_interface database recorder ~is_checked:false in
        let interfaces = List.map (fun path -> (path, find_type_interface lookups path)) paths in
        if List.for_all (fun (_, interface) -> Option.is_some interface) interfaces then
          try
            Some
              (Interface.Properties.compute_component_facts lookups
                 (List.filter_map
                    (fun (path, interface) ->
                      Option.map (fun interface -> (path, interface)) interface)
                    interfaces))
          with Tracker.Reads_failed_fact -> None
        else None)
  in
  List.iter
    (fun path ->
      let outcome : _ Tracker.outcome =
        match facts with
        | Some facts -> (
            match List.assoc_opt path facts with
            | Some facts -> Value facts
            | None ->
                Compiler_bug.raise_bug ~stage:"Database" "the type facts of a component omit %s"
                  (Path.show path))
        | None -> Blocked
      in
      ignore (Tracker.write database Facts.type_facts ~id:(Ids.of_path path) (Some outcome)))
    paths

let run_check_signature database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Check_signature Facts.signature_check row ~id:row.id (fun recorder ->
      match
        Tracker.read database recorder Facts.elaborated.whole key.module_.package ~id:row.id
      with
      | Value _ -> (
          match
            Interface.Check.list_diagnostics
              (Lookups.make_interface database recorder ~is_checked:false)
              key
          with
          | [] -> (Value (), [])
          | diagnostics -> (Failed, diagnostics))
      | Failed | Blocked -> (Blocked, []))

let check_types check database recorder key : Infer.checked Tracker.outcome * _ =
  match check (Lookups.make_infer database recorder) key with
  | Ok checked -> (Value checked, [])
  | Error [] -> (Blocked, [])
  | Error diagnostics -> (Failed, diagnostics)

let run_check_contract database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Check_contract Facts.contract row ~id:row.id (fun recorder ->
      match check_types Infer.check_contract database recorder key with
      | Value checked, diagnostics -> (Value checked.form, diagnostics)
      | Failed, diagnostics -> (Failed, diagnostics)
      | Blocked, diagnostics -> (Blocked, diagnostics))

let run_check_body (database : Tracker.t) (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  let package = Ids.of_package key.module_.package in
  let is_checked_for_instantiation =
    row.is_generic && row.ordinal = 0
    && match Declarations.decode_kind row.kind with Function | Method -> true | _ -> false
  in
  let outcome, diagnostics =
    Tracker.record database ~package Check_body row.id (fun recorder ->
        block (fun () ->
            let outcome, diagnostics = check_types Infer.check_body database recorder key in
            (match outcome with
            | Value checked ->
                List.iter
                  (fun used ->
                    recorder.note References (Entity Package) (Ids.of_package used)
                      (Path.show_package used))
                  checked.used_packages;
                List.iter
                  (fun path -> recorder.note References (Entity Definition) (Ids.of_path path) "")
                  (Package_checks.list_uses checked.form
                  @ Inspect.References.list_named_members checked.tables
                      ((Lookups.make_names database recorder).read_definition key));
                if is_checked_for_instantiation then
                  List.iter
                    (fun (callee, grows) ->
                      let note marker =
                        recorder.note marker (Entity Definition) (Ids.of_path callee) ""
                      in
                      note Instantiates;
                      if grows then note Grows)
                    (Package_checks.list_instantiations key checked.form)
            | Failed | Blocked -> ());
            (outcome, diagnostics)))
  in
  let state_before = Tracker.write database Facts.body ~id:row.id (Some outcome) in
  let was_unchecked =
    match state_before with
    | Some (Tracker.Has_failed | Is_blocked) -> true
    | Some Has_value | None -> false
  and is_unchecked = match outcome with Value _ -> false | Failed | Blocked -> true in
  if was_unchecked <> is_unchecked then
    Tracker.mark_readers database (Selection Unchecked_bodies) package "";
  if state_before = Some Tracker.Has_failed || diagnostics <> [] then
    Tracker.replace_definition_diagnostics database Check_body ~package:key.module_.package
      ~definition:row.id diagnostics

let run_build_body_mir (database : Tracker.t) (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Build_body_mir Facts.body_mir row ~id:row.id (fun recorder ->
      match Tracker.read database recorder Facts.body_form key.module_.package ~id:row.id with
      | Value form ->
          let interface =
            (Lookups.make_interface database recorder ~is_checked:true).read_interface key
          in
          (Value (Mir.make_body_part ~interface form), [])
      | Failed | Blocked -> (Blocked, []))

let run_build_contract_mir (database : Tracker.t) (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Build_contract_mir Facts.contract_mir row ~id:row.id (fun recorder ->
      match Tracker.read database recorder Facts.contract.whole key.module_.package ~id:row.id with
      | Value form ->
          ( Value
              (Mir.make_contract_part
                 ~find_type_interface:
                   (Interface.Definition.find_type_interface
                      (Lookups.make_interface database recorder ~is_checked:true))
                 key.path form),
            [] )
      | Failed | Blocked -> (Blocked, []))

let run_check_usage database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Check_usage Facts.usage_check row ~id:row.id (fun recorder ->
      match Usage.check (Lookups.make_usage database recorder) key with
      | [] -> (Value (), [])
      | diagnostics -> (Failed, diagnostics))

let run_check_ownership database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Check_ownership Facts.ownership row ~id:row.id (fun recorder ->
      let result = Ownership.check (Lookups.make_ownership database recorder) key in
      match result.diagnostics with
      | [] -> (Value result.must_be_disjoint, [])
      | diagnostics -> (Failed, diagnostics))

let run_generate_mir (database : Tracker.t) (row : Store.definition) =
  let path = (Declarations.decode_key row.key).path in
  let outcome =
    Tracker.record database Generate_mir row.path (fun recorder ->
        try
          Option.map
            (fun form : _ Tracker.outcome ->
              Value
                ( Mir.make_body_part form,
                  Mir.make_contract_part
                    ~find_type_interface:
                      (Interface.Definition.find_type_interface
                         (Lookups.make_interface database recorder ~is_checked:true))
                    path form ))
            (Infer.derive_form (Lookups.make_infer database recorder) path)
        with Tracker.Reads_failed_fact -> Some Blocked)
  in
  ignore (Tracker.write database Facts.generated_mir ~id:row.path outcome)

let run_list_calls database (row : Store.definition) =
  let path = (Declarations.decode_key row.key).path in
  run_fact database List_calls Facts.call_node row ~id:row.path (fun recorder ->
      let lookups = Lookups.make_call_edges database recorder in
      (match path with
      | Method
          { owner = (Impl { trait = { path = trait; _ }; _ } | Derived { trait; _ }) as impl; _ }
        when List.exists (Path.equal impl)
               (lookups.interface.names.list_impls_of_trait (Path.locate_package impl) trait) -> (
          match Interface.Definition.find_impl_interface lookups.interface impl with
          | exception Tracker.Reads_failed_fact ->
              recorder.note Implements (Entity Unknown_implementation) (Ids.of_path trait) ""
          | None -> ()
          | Some impl_interface -> (
              match
                Mir.Call_edges.find_implemented_declaration lookups.interface impl_interface ~impl
                  path
              with
              | Some declaration ->
                  recorder.note Implements (Entity Definition) (Ids.of_path declaration) ""
              | None | (exception Tracker.Reads_failed_fact) -> ()))
      | Top _ | Method _ | Member_constant _ | Impl _ | Derived _ | Test _ | Law_proof _
      | Unresolved _ ->
          ());
      let callees = Mir.Call_edges.list_path_edges lookups path in
      let node = Mir.Call_edges.find_node lookups path in
      List.iter
        (fun callee -> recorder.note Calls (Entity Definition) (Ids.of_path callee) "")
        callees;
      (Value { Facts.node; callees }, []))

module Integer_node = struct
  type t = int

  let equal = Int.equal
  let hash = Hashtbl.hash
  let compare = Int.compare
end

let group_recursion (database : Tracker.t) ~is_node (rows : Store.definition list) =
  let rank = Kind.rank_stage Group_recursion in
  let names = Lookups.make_names database Tracker.untracked in
  List.iter
    (fun package ->
      let package_name = Path.show_package package in
      let visible =
        List.map Path.show_package
          (package :: Resolve.Names.list_transitive_dependencies names package)
      in
      let graph = Tracker.make_call_graph ~visible in
      let seeds =
        List.filter_map
          (fun (row : Store.definition) ->
            if List.mem row.package visible then Some row.path else None)
          rows
      in
      let own_seeds =
        List.filter_map
          (fun (row : Store.definition) ->
            if row.package = package_name then Some row.path else None)
          rows
      in
      if seeds <> [] then begin
        let nodes = Store.list_cycle_nodes database.store graph ~seeds in
        let successors = Hashtbl.create 64 in
        List.iter
          (fun (source, target) -> Hashtbl.add successors source target)
          (Store.list_call_pairs database.store graph ~nodes);
        let members_of = Hashtbl.create 64 in
        List.iter
          (fun component ->
            match component with
            | [ single ] ->
                if List.mem single (Hashtbl.find_all successors single) then
                  Hashtbl.replace members_of single component
            | members -> List.iter (fun member -> Hashtbl.replace members_of member members) members)
          (Strongly_connected.list_components
             (module Integer_node)
             ~list_successors:(Hashtbl.find_all successors) nodes);
        let paths = Hashtbl.create 64 in
        List.iter
          (fun (id, key) -> Hashtbl.replace paths id (Declarations.decode_key key).path)
          (Store.list_keys_of_paths database.store
             ~paths:
               (List.sort_uniq Int.compare
                  (Hashtbl.fold (fun _ members ids -> members @ ids) members_of [])));
        let blocked = Hashtbl.create 16 in
        (match
           Store.list_targets_of_kind database.store
             ~kind:(Kind.rank_target (Entity Unknown_implementation))
             ~visible
         with
        | [] -> ()
        | traits ->
            List.iter
              (fun node -> Hashtbl.replace blocked node ())
              (Store.list_callers_closure database.store graph
                 ~seeds:(Store.list_paths_owned_by database.store ~owners:traits)));
        let targets =
          List.sort_uniq Int.compare
            (own_seeds @ List.filter (fun node -> is_node ~package:package_name node) nodes)
        in
        Tracker.report_computed Group_recursion targets;
        let flipped =
          List.filter
            (fun node ->
              ignore (Store.unmark_stale database.store ~stage:rank ~id:node);
              let outcome : Path.t list Tracker.outcome option =
                if Hashtbl.mem blocked node then Some Blocked
                else
                  Option.map
                    (fun members : _ Tracker.outcome ->
                      Value
                        (List.sort Path.compare (List.filter_map (Hashtbl.find_opt paths) members)))
                    (Hashtbl.find_opt members_of node)
              in
              let state_before = Tracker.write database Facts.recursion_group ~id:node outcome in
              state_before = Some Tracker.Is_blocked <> Hashtbl.mem blocked node)
            targets
        in
        if flipped <> [] then Tracker.mark_callers_to_group database ~seeds:flipped
      end)
    (Store.list_project database.store)

let replace_placed (database : Tracker.t) stage ~package ~unit placed =
  Tracker.report stage unit
    ~is_changed:
      (Tracker.replace_placed_diagnostics database stage ~package ~unit
         (List.map
            (fun ({ key; diagnostic } : Package_checks.placed) -> (Ids.of_key key, diagnostic))
            placed))

let run_package_check database stage ~package ~unit check =
  replace_placed database stage ~package ~unit
    (Tracker.record database stage unit (fun recorder ->
         match Package_checks.run (Lookups.make_package_checks database recorder) package check with
         | Placed placed -> placed
         | Unused_dependencies _ -> []
         | exception Tracker.Reads_failed_fact -> []))

let run_definition_check stage make_check database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_package_check database stage ~package:key.module_.package ~unit:row.id (make_check key)

let run_check_dependencies (database : Tracker.t) package =
  let unit = Ids.of_package package in
  let outcome : Path.package list Tracker.outcome =
    Tracker.record database Check_dependencies unit (fun recorder ->
        match
          Package_checks.run (Lookups.make_package_checks database recorder) package Dependencies
        with
        | Unused_dependencies unused -> Tracker.Value unused
        | Placed _ -> Value []
        | exception Tracker.Reads_failed_fact -> Blocked)
  in
  ignore (Tracker.write database Facts.unused_dependencies ~id:unit (Some outcome))

let item_kind = Kind.rank_target (Entity Item)

let item_graph : Store.item_graph =
  {
    lower_kind = Kind.rank_stage Lower;
    item_kind;
    references = Kind.encode_markers [ References ];
    claims = Kind.encode_markers [ Claims ];
    claim_kinds = [ Kind.rank_stage Claim_roots; Kind.rank_stage Prove ];
  }

let ensure_item (database : Tracker.t) (item : Lowered.Item.t) =
  let id = Ids.of_item item in
  if
    Store.insert_item database.store
      {
        id;
        key = Ids.encode item;
        label = Lowered.Item.to_string item;
        definition = Option.map Ids.of_path (Lowered.Item.find_definition item);
      }
  then begin
    Tracker.mark_stale database Lower id;
    Tracker.mark_stale database Key_tests id
  end

let list_item_targets (database : Tracker.t) stage id =
  List.filter_map
    (fun (edge : Store.edge) -> if edge.target.kind = item_kind then Some edge.target.id else None)
    (Store.list_edges database.store Main ~source:(Tracker.locate_unit stage id))

let rec collect_items (database : Tracker.t) candidates =
  List.iter
    (fun id ->
      if
        Option.is_some (Store.find_item_key database.store ~id)
        && not (Store.is_item_claimed database.store item_graph ~item:id)
      then begin
        let referenced = list_item_targets database Lower id in
        Tracker.forget database Lower id ~facts:[ Any Facts.lowered ];
        Tracker.forget database Key_tests id ~facts:[ Any Facts.test_key ];
        Store.remove_item database.store ~id;
        collect_items database referenced
      end)
    candidates

let follow_item_edges database ~items (changes : Store.edge_change list) =
  let items_by_id = Hashtbl.create 16 in
  List.iter (fun item -> Hashtbl.replace items_by_id (Ids.of_item item) item) items;
  collect_items database
    (List.filter_map
       (fun (change : Store.edge_change) ->
         if change.changed.kind <> item_kind then None
         else if change.after = 0 then Some change.changed.id
         else begin
           Option.iter (ensure_item database) (Hashtbl.find_opt items_by_id change.changed.id);
           None
         end)
       changes)

let make_evaluation_root : Prover.Obligation.evaluation -> Lowered.Item.t = function
  | Constant_value path -> Constant path
  | Assertion { definition; condition } -> Assertion { definition; condition }

let run_prove (database : Tracker.t) (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  let (outcome, roots, holes), changes =
    Tracker.record_observed database Prove row.id (fun recorder ->
        let lookups = Lookups.make_proof database recorder in
        match Prover.prove lookups key with
        | proof -> (
            let roots =
              if Result.is_ok Libc.host then
                List.map make_evaluation_root (Prover.list_evaluations proof)
              else []
            in
            List.iter (fun root -> recorder.note Claims (Entity Item) (Ids.of_item root) "") roots;
            ( Tracker.Value proof,
              roots,
              match proof with
              | Obligations outcome ->
                  List.map
                    (fun ((home : Resolve.Names.key), location) : Store.hole ->
                      let span = Prover.resolve_location lookups.interface.names home location in
                      { home = Ids.of_key home; start = span.start; stop = span.stop })
                    outcome.holes
              | Unsupported _ | Not_proven_here -> [] ))
        | exception Tracker.Reads_failed_fact -> (Blocked, [], []))
  in
  let state_before = Tracker.write database Facts.proof ~id:row.id (Some outcome) in
  Store.replace_holes database.store ~definition:row.id holes;
  let warnings =
    match outcome with Value proof -> Prover.list_warnings proof | Failed | Blocked -> []
  in
  if state_before <> None || warnings <> [] then
    Tracker.replace_definition_diagnostics database Prove ~package:key.module_.package
      ~definition:row.id warnings;
  follow_item_edges database ~items:roots changes

type posed_unit = { posed : Prover.posed; has_unfinished_run : bool }

let pose_unit (database : Tracker.t) (recorder : Tracker.recorder) ~runs (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  match Tracker.find database recorder Facts.proof.whole key.module_.package ~id:row.id with
  | Some (Value proof) ->
      let evaluations = Prover.list_evaluations proof in
      List.iter
        (fun evaluation ->
          recorder.note Reads (Fact Test_key) (Ids.of_item (make_evaluation_root evaluation)) "")
        evaluations;
      Some
        {
          posed = Prover.pose (Lookups.make_proof database recorder) ~runs key proof;
          has_unfinished_run =
            List.exists
              (fun evaluation ->
                match List.assoc_opt evaluation runs with
                | Some (Prover.Obligation.Unfinished _ | Failed _) -> true
                | Some (Evaluated _) | None -> false)
              evaluations;
        }
  | Some (Failed | Blocked) | None -> None

let solve_in_parallel (database : Tracker.t) ~runs solver rows =
  match
    List.filter_map (pose_unit database Tracker.untracked ~runs) rows
    |> List.map (fun { posed; _ } -> (posed, Prover.list_requests posed))
  with
  | exception (Compiler_bug.Bug _ | Interface.Properties.Recursion_limit _) -> ()
  | posed ->
      let answers = ref (Solver.solve_all solver (List.concat_map snd posed)) in
      ignore
        (Solver.solve_all solver
           (List.concat_map
              (fun (posed, requests) ->
                let count = List.length requests in
                let own = List.filteri (fun index _ -> index < count) !answers in
                answers := List.filteri (fun index _ -> index >= count) !answers;
                Prover.list_refutation_requests posed own)
              posed))

let run_decide (database : Tracker.t) ~runs solver (row : Store.definition) =
  let states, has_unfinished_run =
    Tracker.record database Decide row.id (fun recorder ->
        match pose_unit database recorder ~runs row with
        | Some { posed; has_unfinished_run; _ } ->
            let answers = List.map (Solver.solve solver) (Prover.list_requests posed) in
            ( Prover.list_states
                (Lookups.make_proof database recorder)
                posed ~answers
                ~refutations:
                  (List.map (Solver.solve solver) (Prover.list_refutation_requests posed answers)),
              has_unfinished_run )
        | None -> ([], false))
  in
  Tracker.report Decide row.id
    ~is_changed:
      (Store.replace_verdicts database.store ~definition:row.id
         (List.map
            (fun ({ site; is_proven; trusts_compiled_code; failure; citation } : Prover.state) :
                 Store.verdict ->
              {
                code = Diagnostic.Code.name (Prover site.code);
                start = site.span.start;
                stop = site.span.stop;
                shows = site.shows;
                is_proven;
                trusts_compiled_code;
                failure = Option.map (fun failure -> Marshal.to_string failure []) failure;
                citation =
                  Option.map
                    (fun ({ cited; clause } : Prover.citation) : Store.citation ->
                      {
                        cited = Ids.of_key cited;
                        clause_start = clause.start;
                        clause_stop = clause.stop;
                      })
                    citation;
              })
            states));
  if has_unfinished_run then Tracker.mark_stale database Decide row.id

let is_root (row : Store.definition) =
  row.origin = Declarations.written_origin
  && row.ordinal = 0
  &&
  match Declarations.decode_kind row.kind with
  | Test -> true
  | Function ->
      let key = Declarations.decode_key row.key in
      key.module_.modules = [] && Path.is_entry_point key.path
  | Type | Trait | Capability | Constant | Theorem | Method | Member_constant | Impl | Law_proof ->
      false

let run_claim_roots (database : Tracker.t) (row : Store.definition) =
  let path = (Declarations.decode_key row.key).path in
  let roots =
    if Result.is_error Libc.host then []
    else
      match path with
      | Test _ -> [ Lowering.test_runner; Lowering.make_root path ]
      | _ -> [ Lowering.make_root path ]
  in
  let (), changes =
    Tracker.record_observed database Claim_roots row.id (fun recorder ->
        List.iter (fun root -> recorder.note Claims (Entity Item) (Ids.of_item root) "") roots)
  in
  follow_item_edges database ~items:roots changes

let read_host_system () =
  match Libc.host with
  | Ok system -> system
  | Error _ ->
      Compiler_bug.raise_bug ~stage:"Database"
        "code is lowered on a host that Stage0 does not build for"

let read_item (database : Tracker.t) id : Lowered.Item.t =
  match Store.find_item_key database.store ~id with
  | Some key -> Marshal.from_string key 0
  | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale item has no row"

let find_call_edges (database : Tracker.t) (recorder : Tracker.recorder) path =
  let node = Ids.of_path path in
  match
    Tracker.find database recorder Facts.call_node.whole (Path.locate_package path) ~id:node
  with
  | Some (Value { node = Definition; callees }) -> Some callees
  | Some (Value { node = Trait_method_declaration; callees }) ->
      Some
        (callees
        @ List.map
            (fun (_, key) -> (Declarations.decode_key key).path)
            (Store.list_keys_of_paths database.store
               ~paths:
                 (Store.list_implementers database.store
                    (Tracker.make_call_graph ~visible:(Store.list_all_packages database.store))
                    ~node)))
  | Some (Failed | Blocked) -> Some []
  | None -> None

let run_lower (database : Tracker.t) id =
  let item = read_item database id in
  let (outcome, references), changes =
    Tracker.record_observed database Lower id (fun recorder ->
        let lookups = Lookups.make_lowering database recorder in
        match Lowering.lower (read_host_system ()) lookups item with
        | Ok lowered as code ->
            Lowering.check_calls lookups.interface
              ~find_call_edges:(find_call_edges database recorder)
              item lowered;
            let references = Lowering.list_references lowered in
            List.iter
              (fun referenced -> recorder.note References (Entity Item) (Ids.of_item referenced) "")
              references;
            (Tracker.Value code, references)
        | Error _ as code -> (Value code, [])
        | exception Tracker.Reads_failed_fact -> (Blocked, [])
        | exception (Lowering.Todo_type _ | Lowering.Infinite_size _) -> (Failed, []))
  in
  ignore (Tracker.write database Facts.lowered ~id (Some outcome));
  follow_item_edges database ~items:references changes

exception Reaches_unsupported of Lowering.unsupported

let run_key_tests (database : Tracker.t) ids =
  let items = List.map (fun id -> (id, read_item database id)) ids in
  let project = Lookups.locate_items database in
  let outcome =
    Tracker.record_group database Key_tests ids ~own:[ Test_key ] (fun recorder ->
        let read view item =
          match Tracker.read_value database recorder view project ~id:(Ids.of_item item) with
          | Ok value -> value
          | Error unsupported -> raise (Reaches_unsupported unsupported)
        in
        match
          Lowering.derive_test_keys ~read_lowered:(read Facts.lowered.whole)
            ~read_known_key:(read Facts.test_key.whole) (List.map snd items)
        with
        | keys -> Tracker.Value (Ok keys)
        | exception Reaches_unsupported unsupported -> Value (Error unsupported)
        | exception Tracker.Reads_failed_fact -> Blocked)
  in
  List.iter
    (fun (id, item) ->
      let key : _ Tracker.outcome =
        match outcome with
        | Value (Ok keys) -> Value (Ok (List.assoc item keys))
        | Value (Error unsupported) -> Value (Error unsupported)
        | Failed | Blocked -> Blocked
      in
      ignore (Tracker.write database Facts.test_key ~id (Some key)))
    items

let decode_kind (row : Store.definition) = Declarations.decode_kind row.kind
let is_written (row : Store.definition) = row.origin = Declarations.written_origin
let is_proven_definition = is_written
let is_first (row : Store.definition) = row.ordinal = 0

let has_call_node (row : Store.definition) =
  (is_written row && is_first row)
  || row.origin = Declarations.inherited_method_origin
  || row.origin = Declarations.derived_method_origin

let definition_stages =
  [
    {
      stage = Claim_roots;
      unit_id = Of_definition;
      applies = is_root;
      facts = [];
      run = run_claim_roots;
    };
    {
      stage = Resolve;
      unit_id = Of_definition;
      applies = is_written;
      facts = List.map (fun section -> Tracker.Any (Facts.resolved section)) Resolve.sections;
      run = run_resolve;
    };
    {
      stage = Read_trait_header;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && decode_kind row = Trait);
      facts = [ Any Facts.trait_header ];
      run = run_trait_header;
    };
    {
      stage = Evaluate_constant;
      unit_id = Of_path;
      applies =
        (fun row ->
          is_written row && is_first row
          && match decode_kind row with Constant | Member_constant -> true | _ -> false);
      facts = [ Any Facts.constant_value ];
      run = run_constant_value;
    };
    {
      stage = Elaborate_header;
      unit_id = Of_definition;
      applies =
        (fun row ->
          is_written row
          && match decode_kind row with Trait | Impl | Capability -> true | _ -> false);
      facts = [ Any Facts.header ];
      run = run_header;
    };
    {
      stage = Elaborate;
      unit_id = Of_definition;
      applies = is_written;
      facts = [ Any Facts.elaborated ];
      run = run_elaborate;
    };
    {
      stage = Derive_interface;
      unit_id = Of_path;
      applies = (fun row -> row.origin = Declarations.derived_impl_origin);
      facts = [ Any Facts.derived_interface ];
      run = run_derive_interface;
    };
    {
      stage = Compute_type_facts;
      unit_id = Of_path;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Type);
      facts = [ Any Facts.type_facts ];
      run = (fun database row -> run_type_facts database [ (Declarations.decode_key row.key).path ]);
    };
    {
      stage = Check_signature;
      unit_id = Of_definition;
      applies = is_written;
      facts = [ Any Facts.signature_check ];
      run = run_check_signature;
    };
    {
      stage = Check_contract;
      unit_id = Of_definition;
      applies = is_written;
      facts = [ Any Facts.contract ];
      run = run_check_contract;
    };
    {
      stage = Check_body;
      unit_id = Of_definition;
      applies = is_written;
      facts = [ Any Facts.body ];
      run = run_check_body;
    };
    {
      stage = Build_body_mir;
      unit_id = Of_definition;
      applies = is_written;
      facts = [ Any Facts.body_mir ];
      run = run_build_body_mir;
    };
    {
      stage = Build_contract_mir;
      unit_id = Of_definition;
      applies = is_written;
      facts = [ Any Facts.contract_mir ];
      run = run_build_contract_mir;
    };
    {
      stage = Generate_mir;
      unit_id = Of_path;
      applies = (fun row -> row.origin = Declarations.derived_method_origin);
      facts = [ Any Facts.generated_mir ];
      run = run_generate_mir;
    };
    {
      stage = List_calls;
      unit_id = Of_path;
      applies = has_call_node;
      facts = [ Any Facts.call_node ];
      run = run_list_calls;
    };
    {
      stage = Group_recursion;
      unit_id = Of_path;
      applies = has_call_node;
      facts = [ Any Facts.recursion_group ];
      run =
        (fun database row -> group_recursion database ~is_node:(fun ~package:_ _ -> false) [ row ]);
    };
    {
      stage = Check_usage;
      unit_id = Of_definition;
      applies = is_written;
      facts = [ Any Facts.usage_check ];
      run = run_check_usage;
    };
    {
      stage = Check_ownership;
      unit_id = Of_definition;
      applies = is_written;
      facts = [ Any Facts.ownership ];
      run = run_check_ownership;
    };
    {
      stage = Check_sealed;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Impl);
      facts = [];
      run = run_definition_check Check_sealed (fun key -> Sealed key);
    };
    {
      stage = Check_impl;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Impl);
      facts = [];
      run = run_definition_check Check_impl (fun key -> Impl key);
    };
    {
      stage = Check_type;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Type);
      facts = [];
      run = run_definition_check Check_type (fun key -> Type key);
    };
    {
      stage = Prove;
      unit_id = Of_definition;
      applies = is_proven_definition;
      facts = [ Any Facts.proof ];
      run = run_prove;
    };
  ]

let identify_unit recipe (row : Store.definition) =
  match recipe.unit_id with Of_definition -> row.id | Of_path -> row.path

let is_impl (row : Store.definition) =
  (is_written row && is_first row && decode_kind row = Impl)
  || row.origin = Declarations.derived_impl_origin

let is_supplied_method (row : Store.definition) =
  row.origin = Declarations.inherited_method_origin
  || row.origin = Declarations.derived_method_origin

let list_supplied_methods (database : Tracker.t) (impl : Store.definition) =
  List.filter is_supplied_method (Store.list_definitions database.store Main (Of_container impl.id))

let rec forget_definition (database : Tracker.t) (row : Store.definition) =
  let claimed =
    list_item_targets database Claim_roots row.id @ list_item_targets database Prove row.id
  in
  List.iter
    (fun recipe ->
      if recipe.applies row then
        Tracker.forget database recipe.stage (identify_unit recipe row) ~facts:recipe.facts)
    definition_stages;
  if is_proven_definition row then begin
    Tracker.forget database Decide row.id ~facts:[];
    Store.replace_holes database.store ~definition:row.id [];
    ignore (Store.replace_verdicts database.store ~definition:row.id []);
    Tracker.mark_readers database (Selection Unchecked_bodies) (Store.identify row.package) ""
  end;
  collect_items database claimed;
  if is_impl row then begin
    List.iter
      (fun (supplied : Store.definition) ->
        Store.remove_definition database.store ~id:supplied.id;
        forget_definition database supplied)
      (list_supplied_methods database row);
    Tracker.forget database Supply row.id ~facts:[]
  end

let create_units database (row : Store.definition) =
  List.iter
    (fun recipe ->
      if recipe.applies row then Tracker.mark_stale database recipe.stage (identify_unit recipe row))
    definition_stages;
  if is_proven_definition row then Tracker.mark_stale database Decide row.id;
  if is_impl row then Tracker.mark_stale database Supply row.id

let run_supply (database : Tracker.t) (impl : Store.definition) =
  let key = Declarations.decode_key impl.key in
  let trait =
    match key.path with
    | Impl { trait; _ } -> Some trait.path
    | Derived { trait; _ } -> Some trait
    | Top _ | Method _ | Member_constant _ | Test _ | Law_proof _ | Unresolved _ -> None
  in
  let supplied =
    Tracker.record database Supply impl.id (fun recorder ->
        let names = Lookups.make_names database recorder in
        match Option.bind trait names.find_key with
        | Some trait_key when (names.read_declaration trait_key).kind = Trait ->
            List.filter_map
              (fun (member : Resolve.Names.key) ->
                match member.path with
                | Method { name; receiver; _ } ->
                    let method_ = Path.Method { owner = key.path; name; receiver } in
                    if Option.is_some (names.find_key method_) then None
                    else
                      Some
                        (Declarations.encode_supplied
                           ~origin:
                             (if Infer.is_derived_method method_ then
                                Declarations.derived_method_origin
                              else Declarations.inherited_method_origin)
                           ~kind:Method
                           { module_ = key.module_; path = method_; ordinal = 0 }
                           ~supplied_from:(Ids.of_key member) ~container:(Some impl.id))
                | _ -> None)
              (names.list_contained trait_key)
        | Some _ | None -> [])
  in
  let supplied_before = list_supplied_methods database impl in
  let has_row rows (row : Store.definition) =
    List.exists (fun (candidate : Store.definition) -> candidate.id = row.id) rows
  in
  List.iter
    (fun (row : Store.definition) ->
      if not (has_row supplied row) then begin
        Store.remove_definition database.store ~id:row.id;
        forget_definition database row
      end)
    supplied_before;
  List.iter
    (fun (row : Store.definition) ->
      if not (List.mem row supplied_before) then Store.replace_definition database.store row;
      if not (has_row supplied_before row) then create_units database row)
    supplied

let run_declare (database : Tracker.t) id =
  let module_ : Path.module_ =
    match Store.find_module_key database.store Main ~id with
    | Some bytes -> Marshal.from_string bytes 0
    | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale module has no row"
  in
  let files =
    List.map
      (fun (file : Store.file) -> (Declarations.decode_file file.key, file.text))
      (Store.list_files database.store Main (Of_module id))
  in
  let declarations =
    Tracker.record database Declare id (fun recorder ->
        recorder.note Reads (Lookup Files) id "";
        List.iter
          (fun ((file : Path.file), _) -> recorder.note Reads (Lookup Source) (Ids.of_file file) "")
          files;
        Resolve.Namespace.declare
          (Lookups.make_names database recorder)
          (List.map (fun (file, text) -> (file, fst (parse file text), text)) files))
  in
  let written = Declarations.write_module database.store module_ ~files declarations in
  List.iter
    (fun ({ lookup; scope; name; is_spans_only } : Declarations.change) ->
      if is_spans_only then Tracker.mark_position_holders database (Lookup lookup) scope name
      else Tracker.mark_readers database (Lookup lookup) scope name)
    written.changes;
  List.iter (forget_definition database) written.removed;
  List.iter (create_units database) written.added;
  Tracker.report Declare id
    ~is_changed:(written.changes <> [] || written.added <> [] || written.removed <> []);
  if files = [] then begin
    Store.remove_module database.store ~id;
    Tracker.forget database Declare id ~facts:[]
  end

let run_grant (database : Tracker.t) id =
  let dependency =
    match Store.find_dependency database.store ~id with
    | Some dependency -> dependency
    | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale grant has no dependency"
  in
  let package =
    match Path.parse_package dependency.package with
    | Some package -> package
    | None -> Compiler_bug.raise_bug ~stage:"Database" "a dependency's package has no name"
  in
  let grant =
    Tracker.record database Resolve_grant id (fun recorder ->
        recorder.note Reads (Lookup Dependencies) (Ids.of_package package) "";
        Interface.Grants.resolve_grant
          (Lookups.make_names database recorder)
          ~package
          (Marshal.from_string dependency.capabilities 0))
  in
  ignore (Tracker.write database Facts.grant ~id (Some (Value grant)))

let forget_grant database id = Tracker.forget database Resolve_grant id ~facts:[ Any Facts.grant ]

let read_first_definition (database : Tracker.t) recipe id =
  let row =
    match recipe.unit_id with
    | Of_definition -> Store.find_definition database.store Main ~id
    | Of_path ->
        List.find_opt recipe.applies (Store.list_definitions database.store Main (Of_path id))
  in
  match row with
  | Some row -> row
  | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale definition has no row"

let find_recipe stage = List.find (fun recipe -> recipe.stage = stage) definition_stages

let drain_type_facts (database : Tracker.t) ~guard stale =
  let recipe = find_recipe Compute_type_facts in
  let rank = Kind.rank_stage Compute_type_facts in
  let closure = Hashtbl.create 64 in
  let rec close id =
    if not (Hashtbl.mem closure id) then begin
      Hashtbl.replace closure id ();
      List.iter
        (fun (reader : Store.endpoint) -> if reader.kind = rank then close reader.id)
        (Store.list_sources database.store
           ~target:(Tracker.locate (Fact Type_facts) id "")
           ~markers:reads)
    end
  in
  List.iter close stale;
  let paths =
    Hashtbl.fold
      (fun id () paths ->
        (Declarations.decode_key (read_first_definition database recipe id).key).path :: paths)
      closure []
  in
  let lookups = Lookups.make_interface database Tracker.untracked ~is_checked:false in
  List.iter
    (fun package ->
      let is_in_closure path = Hashtbl.mem closure (Ids.of_path path) in
      List.iter
        (fun component ->
          let was_stale =
            List.map
              (fun path -> Store.unmark_stale database.store ~stage:rank ~id:(Ids.of_path path))
              component
          in
          if List.exists Fun.id was_stale then
            guard (List.map Ids.of_path component) (fun () -> run_type_facts database component))
        (Strongly_connected.list_components
           (module Path)
           ~list_successors:(fun path ->
             match find_type_interface lookups path with
             | Some interface ->
                 List.filter is_in_closure
                   (Interface.Properties.list_field_type_paths ~package interface)
             | None -> [])
           (List.sort Path.compare
              (List.filter (fun path -> Path.locate_package path = package) paths))))
    (Lookups.sort_in_dependency_order database
       (List.sort_uniq Path.compare_package (List.map Path.locate_package paths)))

let package_stages : Kind.stage list =
  [ Check_instantiations; Check_tests; Check_unexported; Check_dependencies ]

let forget_package (database : Tracker.t) package =
  List.iter
    (fun stage ->
      Tracker.forget database stage (Ids.of_package package)
        ~facts:(if stage = Kind.Check_dependencies then [ Any Facts.unused_dependencies ] else []))
    package_stages

let run_package_stage (database : Tracker.t) (stage : Kind.stage) id =
  let package =
    match Option.bind (Store.find_package_name database.store ~id) Path.parse_package with
    | Some package -> package
    | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale package has no row"
  in
  match stage with
  | Check_instantiations -> run_package_check database stage ~package ~unit:id Instantiations
  | Check_tests -> run_package_check database stage ~package ~unit:id Tests
  | Check_unexported -> run_package_check database stage ~package ~unit:id Unexported
  | _ -> run_check_dependencies database package

let drain_test_keys (database : Tracker.t) ~guard stale =
  let rank = Kind.rank_stage Key_tests in
  let closure = Hashtbl.create 64 in
  let rec close id =
    if not (Hashtbl.mem closure id) then begin
      Hashtbl.replace closure id ();
      List.iter
        (fun (reader : Store.endpoint) -> if reader.kind = rank then close reader.id)
        (Store.list_sources database.store
           ~target:(Tracker.locate (Fact Test_key) id "")
           ~markers:reads)
    end
  in
  List.iter close stale;
  List.iter
    (fun component ->
      let was_stale =
        List.map (fun id -> Store.unmark_stale database.store ~stage:rank ~id) component
      in
      if List.exists Fun.id was_stale then
        guard component (fun () -> run_key_tests database component))
    (Strongly_connected.list_components
       (module Integer_node)
       ~list_successors:(fun id ->
         List.filter (Hashtbl.mem closure) (list_item_targets database Lower id))
       (List.sort Int.compare (Hashtbl.fold (fun id () ids -> id :: ids) closure [])))

let list_claimed_items (database : Tracker.t) packages =
  Store.list_claimed_items database.store item_graph
    ~packages:(Option.map (List.map Path.show_package) packages)

let list_definition_facts () =
  List.concat_map (fun recipe -> List.map Tracker.describe recipe.facts) definition_stages

let locate_entity (stage : Kind.stage) : Store.unit_entity =
  match stage with
  | Lower | Key_tests -> Item_unit
  | Parse | Check_imports -> File_unit
  | Declare -> Module_unit
  | Resolve_grant -> Dependency_unit
  | Supply | Decide -> Definition_unit
  | Check_instantiations | Check_tests | Check_unexported | Check_dependencies -> Package_unit
  | Claim_roots | Resolve | Read_trait_header | Evaluate_constant | Elaborate_header | Elaborate
  | Derive_interface | Compute_type_facts | Check_signature | Check_contract | Check_body
  | Build_body_mir | Build_contract_mir | Generate_mir | List_calls | Group_recursion | Check_usage
  | Check_ownership | Check_sealed | Check_impl | Check_type | Prove -> (
      match (find_recipe stage).unit_id with
      | Of_definition -> Definition_unit
      | Of_path -> Path_unit)

let list_stale_units (database : Tracker.t) (stage : Kind.stage) ~scope =
  List.filter
    (fun id -> not (Tracker.is_broken database stage id))
    (Store.list_stale database.store ~stage:(Kind.rank_stage stage) ~entity:(locate_entity stage)
       ~scope)

let guard_units (database : Tracker.t) ?on_bug (stage : Kind.stage) ids run =
  let fail bug =
    List.iter (Tracker.mark_stale database stage) ids;
    Tracker.record_bug database stage ids bug;
    match on_bug with Some on_bug -> on_bug bug | None -> raise (Compiler_bug.Bug bug)
  in
  match
    Tracker.fail_for_test stage ids;
    run ()
  with
  | () -> ()
  | exception Compiler_bug.Bug bug -> fail bug
  | exception Interface.Properties.Recursion_limit message ->
      fail
        {
          stage = "Database";
          message = "a stage after the checks reached a recursion limit: " ^ message;
          doing = [];
        }

let drain_decide (database : Tracker.t) ?on_bug ~scope ~runs solver =
  match
    List.filter_map
      (fun id -> Store.find_definition database.store Main ~id)
      (list_stale_units database Decide ~scope)
  with
  | [] -> ()
  | rows ->
      let solver = Lazy.force solver in
      solve_in_parallel database ~runs solver rows;
      List.iter
        (fun (row : Store.definition) ->
          if Store.unmark_stale database.store ~stage:(Kind.rank_stage Decide) ~id:row.id then
            guard_units database ?on_bug Decide [ row.id ] (fun () ->
                run_decide database ~runs solver row))
        rows

let drain_stage (database : Tracker.t) ?on_bug (stage : Kind.stage) ~scope =
  let rank = Kind.rank_stage stage in
  let stale = list_stale_units database stage ~scope in
  let guard = guard_units database ?on_bug stage in
  let run_each run =
    List.iter
      (fun id ->
        if Store.unmark_stale database.store ~stage:rank ~id then
          guard [ id ] (fun () -> run database id))
      stale
  in
  (match stage with
  | Parse -> run_each run_parse
  | Declare -> run_each run_declare
  | Resolve_grant -> run_each run_grant
  | Check_imports -> run_each run_check_imports
  | Compute_type_facts -> if stale <> [] then drain_type_facts database ~guard stale
  | Check_contract ->
      let recipe = find_recipe stage in
      let constants, others =
        List.partition
          (fun row -> Resolve.Names.is_constant (decode_kind row))
          (List.map (read_first_definition database recipe) stale)
      in
      List.iter
        (fun (row : Store.definition) ->
          if Store.unmark_stale database.store ~stage:rank ~id:row.id then
            guard [ row.id ] (fun () -> recipe.run database row))
        (constants @ others)
  | Group_recursion ->
      let recipe = find_recipe stage in
      let find_node id =
        List.find_opt recipe.applies (Store.list_definitions database.store Main (Of_path id))
      in
      let rows = List.filter_map find_node stale in
      List.iter
        (fun id ->
          if Option.is_none (find_node id) then
            ignore (Store.unmark_stale database.store ~stage:rank ~id))
        stale;
      if rows <> [] then
        guard
          (List.map (fun (row : Store.definition) -> row.path) rows)
          (fun () ->
            group_recursion database
              ~is_node:(fun ~package id ->
                match find_node id with Some row -> row.package = package | None -> false)
              rows)
  | Supply ->
      run_each (fun database id ->
          match Store.find_definition database.store Main ~id with
          | Some impl -> run_supply database impl
          | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale impl has no row")
  | Check_instantiations | Check_tests | Check_unexported | Check_dependencies ->
      run_each (fun database id -> run_package_stage database stage id)
  | Lower -> run_each run_lower
  | Key_tests -> if stale <> [] then drain_test_keys database ~guard stale
  | Decide ->
      Compiler_bug.raise_bug ~stage:"Database"
        "Decide is drained with the results of its evaluations and a solver"
  | Resolve | Read_trait_header | Evaluate_constant | Elaborate_header | Elaborate
  | Derive_interface | Check_signature | Check_body | Build_body_mir | Build_contract_mir
  | Generate_mir | List_calls | Check_usage | Check_ownership | Check_sealed | Check_impl
  | Check_type | Prove | Claim_roots ->
      let recipe = find_recipe stage in
      run_each (fun database id -> recipe.run database (read_first_definition database recipe id)));
  stale <> []
