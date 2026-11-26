type unit_id = Of_definition | Of_path

type definition_stage = {
  stage : Kind.stage;
  unit_id : unit_id;
  applies : Store.definition -> bool;
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

let parse_with_diagnostics file text =
  let tree, diagnostics = parse file text in
  (tree, List.map (fun diagnostic -> Renderer.Syntax diagnostic) diagnostics)

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
        parse_with_diagnostics file text)
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
    List.iter (fun stage -> Tracker.forget database stage id) file_stages;
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
        List.map (fun import -> Renderer.Import import)
        @@ Resolve.list_file_diagnostics
             (Lookups.make_names database recorder)
             file
             (fst (parse file text))
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
      | Error descriptions -> (Failed, descriptions))

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
      | descriptions, _ -> (Failed, descriptions))

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
          | descriptions -> (Failed, descriptions))
      | Failed | Blocked -> (Blocked, []))

let check_types check database recorder key : Infer.checked Tracker.outcome * _ =
  match check (Lookups.make_infer database recorder) key with
  | Ok checked -> (Value checked, [])
  | Error [] -> (Blocked, [])
  | Error descriptions -> (Failed, descriptions)

let run_check_contract database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Check_contract Facts.contract row ~id:row.id (fun recorder ->
      match check_types Infer.check_contract database recorder key with
      | Value checked, diagnostics -> (Value checked.form, diagnostics)
      | Failed, diagnostics -> (Failed, diagnostics)
      | Blocked, diagnostics -> (Blocked, diagnostics))

let is_checked_for_instantiation (row : Store.definition) =
  row.is_generic && row.ordinal = 0
  && match Declarations.decode_kind row.kind with Function | Method -> true | _ -> false

let run_check_body (database : Tracker.t) (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  let package = Ids.of_package key.module_.package in
  let outcome, diagnostics =
    Tracker.record database Check_body row.id (fun recorder ->
        block (fun () ->
            let outcome, diagnostics = check_types Infer.check_body database recorder key in
            (match outcome with
            | Value checked ->
                List.iter
                  (fun used ->
                    recorder.note References (Entity Package) package (Path.show_package used))
                  checked.used_packages;
                List.iter
                  (fun path -> recorder.note References (Entity Definition) (Ids.of_path path) "")
                  (Package_checks.list_uses checked.form
                  @ Inspect.References.list_named_members checked.tables
                      ((Lookups.make_names database recorder).read_definition key));
                if is_checked_for_instantiation row then
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
      | descriptions -> (Failed, descriptions))

let run_check_ownership database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  run_fact database Check_ownership Facts.ownership row ~id:row.id (fun recorder ->
      let result = Ownership.check (Lookups.make_ownership database recorder) key in
      let is_error diagnostic = (Catalog.describe diagnostic).severity = Error in
      if List.exists is_error result.diagnostics then (Failed, result.diagnostics)
      else (Value result.must_be_disjoint, result.diagnostics))

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
      let callees = Mir.Call_edges.list_path_edges lookups path in
      let note marker target = recorder.note marker (Entity Definition) (Ids.of_path target) "" in
      List.iter (note Calls) callees;
      List.iter (note Assumes) (Mir.Call_edges.list_assumed_paths lookups path);
      (Value callees, []))

module Integer_node = struct
  type t = int

  let equal = Int.equal
  let hash = Hashtbl.hash
  let compare = Int.compare
end

let group_recursion (database : Tracker.t) ~is_node (rows : Store.definition list) =
  let rank = Kind.rank_stage Group_recursion in
  List.iter
    (fun package ->
      let package_name = Path.show_package package in
      let seeds =
        List.filter_map
          (fun (row : Store.definition) ->
            if row.package = package_name then Some row.path else None)
          rows
      in
      if seeds <> [] then begin
        let nodes = Store.list_cycle_nodes database.store Tracker.proof_graph ~seeds in
        let edges = Store.list_proof_edges database.store Tracker.proof_graph ~nodes in
        let group ~follows =
          let successors = Hashtbl.create 64 in
          List.iter
            (fun (edge : Store.proof_edge) ->
              if follows edge.markers then Hashtbl.add successors edge.source edge.target)
            edges;
          let members_of = Hashtbl.create 64 in
          List.iter
            (fun component ->
              match component with
              | [ single ] ->
                  if List.mem single (Hashtbl.find_all successors single) then
                    Hashtbl.replace members_of single component
              | members ->
                  List.iter (fun member -> Hashtbl.replace members_of member members) members)
            (Strongly_connected.list_components
               (module Integer_node)
               ~list_successors:(Hashtbl.find_all successors) nodes);
          members_of
        in
        let recursion_groups = group ~follows:(fun markers -> Kind.has_marker markers Calls)
        and proof_groups = group ~follows:(fun _ -> true) in
        let paths = Hashtbl.create 64 in
        List.iter
          (fun (id, key) -> Hashtbl.replace paths id (Declarations.decode_key key).path)
          (Store.list_keys_of_paths database.store
             ~paths:
               (List.sort_uniq Int.compare
                  (Hashtbl.fold (fun _ members ids -> members @ ids) proof_groups [])));
        let targets =
          List.sort_uniq Int.compare
            (seeds @ List.filter (fun node -> is_node ~package:package_name node) nodes)
        in
        Tracker.report_computed Group_recursion targets;
        let write fact groups node =
          ignore
            (Tracker.write database fact ~id:node
               (Option.map
                  (fun members : Path.t list Tracker.outcome ->
                    Value
                      (List.sort Path.compare (List.filter_map (Hashtbl.find_opt paths) members)))
                  (Hashtbl.find_opt groups node)))
        in
        List.iter
          (fun node ->
            ignore (Store.unmark_stale database.store ~stage:rank ~id:node);
            write Facts.recursion_group recursion_groups node;
            write Facts.proof_group proof_groups node)
          targets
      end)
    (Store.list_project database.store)

let replace_placed (database : Tracker.t) stage ~package ~unit placed =
  Tracker.report stage unit
    ~is_changed:(Tracker.replace_placed_diagnostics database stage ~package ~unit placed)

let check_package_unit database stage ~package ~unit check =
  Tracker.record database stage unit (fun recorder ->
      match Package_checks.run (Lookups.make_package_checks database recorder) package check with
      | Placed placed ->
          List.map
            (fun ({ key; diagnostic } : Package_checks.placed) -> (Ids.of_key key, diagnostic))
            placed
      | Dependency_used _ ->
          Compiler_bug.raise_bug ~stage:"Database"
            "the check of a definition answered for a dependency"
      | exception Tracker.Reads_failed_fact -> [])

let run_definition_check stage make_check database (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  let package = key.module_.package in
  replace_placed database stage ~package ~unit:row.id
    (check_package_unit database stage ~package ~unit:row.id (make_check key))

let replace_classified (database : Tracker.t) stage classified =
  let placed_by_unit =
    List.map
      (fun ((key : Resolve.Names.key), unit, reported) ->
        let package = key.module_.package in
        (package, unit, Option.map (check_package_unit database stage ~package ~unit) reported))
      classified
  in
  List.iter
    (fun (package, unit, placed) ->
      match placed with
      | Some placed -> replace_placed database stage ~package ~unit placed
      | None ->
          if Store.has_diagnostic database.store ~stage:(Kind.rank_stage stage) ~unit then
            Tracker.forget database stage unit)
    placed_by_unit

let classify_together (database : Tracker.t) classify (rows : Store.definition list) =
  classify
    (Lookups.make_package_checks database Tracker.untracked)
    (List.map Declarations.decode_declaration rows)

let classify_uses database rows =
  replace_classified database Check_unexported
    (List.map
       (fun ((declaration : Resolve.Names.declaration), (use : Package_checks.use)) ->
         ( declaration.key,
           Ids.of_path declaration.key.path,
           match use with
           | Unused _ -> Some (Package_checks.Unexported (declaration.key, use))
           | Used -> None ))
       (classify_together database Package_checks.classify_uses rows))

let find_growing_cycles database rows =
  replace_classified database Check_instantiation
    (List.map
       (fun ((key : Resolve.Names.key), grows_on_a_cycle) ->
         ( key,
           Ids.of_key key,
           if grows_on_a_cycle then Some (Package_checks.Instantiation key) else None ))
       (classify_together database Package_checks.find_growing_cycles rows))

let item_kind = Kind.rank_target (Entity Item)

let item_stages : Kind.stage list =
  [ Lower; Key_tests; Evaluate; Run_test; Render Development; Render Release ]

let item_graph : Store.item_graph =
  {
    lower_kind = Kind.rank_stage Lower;
    evaluate_kind = Kind.rank_stage Evaluate;
    item_kind;
    references = Kind.encode_markers [ References ];
    claims = Kind.encode_markers [ Claims ];
    claim_kinds = [ Kind.rank_stage Claim_roots; Kind.rank_stage Prove ];
  }

let evaluation_graph = { item_graph with claim_kinds = [ Kind.rank_stage Prove ] }

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
  then List.iter (fun stage -> Tracker.mark_stale database stage id) item_stages

let list_item_targets (database : Tracker.t) stage id =
  List.filter_map
    (fun (edge : Store.edge) -> if edge.target.kind = item_kind then Some edge.target.id else None)
    (Store.list_edges database.store Main ~source:(Tracker.locate_unit stage id))

let rec collect_items (database : Tracker.t) candidates =
  List.iter
    (fun id ->
      if
        Option.is_some (Store.find_item_key database.store ~id)
        && not (Store.is_item_claimed database.store item_graph ~item:id ~over:Every_edge)
      then begin
        let referenced = list_item_targets database Lower id in
        List.iter (fun stage -> Tracker.forget database stage id) item_stages;
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

let read_host_system () =
  match Libc.host with
  | Ok system -> system
  | Error _ ->
      Compiler_bug.raise_bug ~stage:"Database"
        "code is lowered on a host that Stage0 does not build for"

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
                      { home = Ids.of_key home; location = Marshal.to_string location [] })
                    outcome.holes
              | Unsupported _ | Not_proven_here -> [] ))
        | exception Tracker.Reads_failed_fact -> (Blocked, [], []))
  in
  ignore (Tracker.write database Facts.proof ~id:row.id (Some outcome));
  Store.replace_holes database.store ~definition:row.id holes;
  follow_item_edges database ~items:roots changes

type posed_unit = { posed : Prover.posed; has_unfinished_run : bool }

let rec make_value : Lowered.static_value -> Prover.Obligation.value = function
  | Static_scalar (Bool holds) -> Boolean holds
  | Static_scalar (Integer (_, number)) -> Integer number
  | Static_scalar (Character scalar) -> Integer (Z.of_int scalar)
  | Static_scalar (Float32 bits) -> Float (Int32.float_of_bits bits)
  | Static_scalar (Float64 bits) -> Float (Int64.float_of_bits bits)
  | Static_scalar _ ->
      Compiler_bug.raise_bug ~stage:"Database" "an evaluation gave a scalar that is no value"
  | Static_record fields -> Constructed { variant = None; fields = make_fields fields }
  | Static_variant (variant, fields) ->
      Constructed { variant = Some variant; fields = make_fields fields }
  | Static_array elements | Static_storage { elements; _ } ->
      Elements (List.map make_value elements)

and make_fields fields = List.map (fun (name, value) -> (name, make_value value)) fields

let find_run (database : Tracker.t) (recorder : Tracker.recorder) (lookups : Prover.Lookups.t)
    evaluation : Prover.Obligation.run option =
  let id = Ids.of_item (make_evaluation_root evaluation) in
  let find_settled view =
    Tracker.find_settled database recorder view (Lookups.locate_items database) ~id
  in
  recorder.note Reads (Fact Test_key) id "";
  match (find_settled Facts.lowered.whole, find_settled Facts.evaluation.whole) with
  | Some (Value (Ok (Folded (data, _)))), _ -> Some (Evaluated (make_value data.value))
  | Some (Value (Ok (Evaluate (_, ty)))), Some (Value (Ran encoded)) ->
      let env = Lowering.make_env (read_host_system ()) lookups.interface in
      Some (Evaluated (make_value (Lowering.Encoding.decode env ty encoded)))
  | _, Some (Value (Unfinished report)) -> Some (Unfinished report)
  | _, Some (Value (Stopped report)) -> Some (Failed report)
  | _, (Some (Value (Ran _) | Failed | Blocked) | None) -> None

let list_runs database recorder lookups proof =
  List.filter_map
    (fun evaluation ->
      Option.map (fun run -> (evaluation, run)) (find_run database recorder lookups evaluation))
    (Prover.list_evaluations proof)

let pose_unit (database : Tracker.t) (recorder : Tracker.recorder) (row : Store.definition) =
  let key = Declarations.decode_key row.key in
  match Tracker.find database recorder Facts.proof.whole key.module_.package ~id:row.id with
  | Some (Value proof) ->
      let lookups = Lookups.make_proof database recorder in
      let runs = list_runs database recorder lookups proof in
      Some
        {
          posed = Prover.pose ~runs proof;
          has_unfinished_run =
            List.exists
              (function
                | _, (Prover.Obligation.Unfinished _ | Failed _) -> true | _, Evaluated _ -> false)
              runs;
        }
  | Some (Failed | Blocked) | None -> None

type note = Kind.marker * Kind.target * int * string

type answered_unit = {
  unit : posed_unit option;
  notes : note list;
  answers : Solver.answer list;
  refutations : Solver.answer list;
  solver_runs : Store.solver_run list;
}

let hash_solver_input = Blake3.derive_key ~context:"truss 2026-11-25 solver input"

let list_distinct_solver_runs (solved : Solver.solved list) =
  let listed = Hashtbl.create 16 in
  List.concat_map
    (fun (solved : Solver.solved) ->
      List.filter_map
        (fun (run : Solver.run) : Store.solver_run option ->
          let input_hash = hash_solver_input run.input in
          if Hashtbl.mem listed input_hash then None
          else begin
            Hashtbl.replace listed input_hash ();
            Some { input_hash; output = run.output }
          end)
        solved.runs)
    solved

let split_by_counts counts values =
  let remaining = ref values in
  List.map
    (fun count ->
      let own = List.take count !remaining in
      remaining := List.drop count !remaining;
      own)
    counts

let solve_units (database : Tracker.t) solver (rows : Store.definition list) =
  let posed =
    List.map
      (fun (row : Store.definition) ->
        let notes = ref [] in
        let recorder : Tracker.recorder =
          { note = (fun marker target id name -> notes := (marker, target, id, name) :: !notes) }
        in
        match pose_unit database recorder row with
        | unit -> (row.id, Ok (unit, List.rev !notes))
        | exception ((Compiler_bug.Bug _ | Interface.Properties.Recursion_limit _) as raised) ->
            (row.id, Error raised))
      rows
  in
  let list_of_posed list_requests =
    List.map
      (fun (_, unit) ->
        match unit with
        | Ok (Some { posed; _ }, _) -> list_requests posed
        | Ok (None, _) | Error _ -> [])
      posed
  in
  let outputs = Hashtbl.create 64 in
  List.iter
    (fun (row : Store.definition) ->
      List.iter
        (fun (run : Store.solver_run) -> Hashtbl.replace outputs run.input_hash run.output)
        (Store.list_solver_runs database.store ~definition:row.id))
    rows;
  let find_output input = Hashtbl.find_opt outputs (hash_solver_input input) in
  let solve_each requests =
    split_by_counts (List.map List.length requests)
      (Solver.solve_all ~find_output solver (List.concat requests))
  in
  let list_answers = List.map (fun (solved : Solver.solved) -> solved.answer) in
  let solved_requests = solve_each (list_of_posed Prover.list_requests) in
  let solved_refutations =
    solve_each
      (List.map2
         (fun (_, unit) solved ->
           match unit with
           | Ok (Some { posed; _ }, _) ->
               Prover.list_refutation_requests posed (list_answers solved)
           | Ok (None, _) | Error _ -> [])
         posed solved_requests)
  in
  let answered = Hashtbl.create (List.length rows) in
  List.iter2
    (fun (id, unit) (requests, refutations) ->
      Hashtbl.replace answered id
        (Result.map
           (fun (unit, notes) ->
             {
               unit;
               notes;
               answers = list_answers requests;
               refutations = list_answers refutations;
               solver_runs = list_distinct_solver_runs (requests @ refutations);
             })
           unit))
    posed
    (List.combine solved_requests solved_refutations);
  answered

let run_decide (database : Tracker.t) answered (row : Store.definition) =
  let states, has_unfinished_run, solver_runs =
    Tracker.record database Decide row.id (fun recorder ->
        match Hashtbl.find answered row.id with
        | Error raised -> raise raised
        | Ok { unit; notes; answers; refutations; solver_runs } -> (
            List.iter (fun (marker, target, id, name) -> recorder.note marker target id name) notes;
            match unit with
            | Some { posed; has_unfinished_run } ->
                (Prover.list_states posed ~answers ~refutations, has_unfinished_run, solver_runs)
            | None -> ([], false, [])))
  in
  Store.replace_solver_runs database.store ~definition:row.id solver_runs;
  Tracker.report Decide row.id
    ~is_changed:
      (Store.replace_verdicts database.store ~definition:row.id
         (List.map
            (fun ({ site; is_proven; trusts_compiled_code; failure } : Prover.state) : Store.verdict
               ->
              {
                code = Diagnostic.Code.name (Catalog.describe (Prover site)).code;
                site = Marshal.to_string site [];
                is_proven;
                trusts_compiled_code;
                failure = Option.map (fun failure -> Marshal.to_string failure []) failure;
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

let read_item (database : Tracker.t) id : Lowered.Item.t =
  match Store.find_item_key database.store ~id with
  | Some key -> Marshal.from_string key 0
  | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale item has no row"

let find_call_edges (database : Tracker.t) (recorder : Tracker.recorder) path =
  let node = Ids.of_path path in
  match
    Tracker.find database recorder Facts.call_node.whole (Path.locate_package path) ~id:node
  with
  | Some (Value callees) -> Some callees
  | Some (Failed | Blocked) -> Some []
  | None -> None

let run_find_aborts database (row : Store.definition) =
  let path = (Declarations.decode_key row.key).path in
  run_fact database Find_aborts Facts.aborts_outside_group row ~id:row.path (fun recorder ->
      let lookups = Lookups.make_call_edges database recorder in
      let list_callee_aborts () =
        let members =
          Option.value ~default:[]
            (Tracker.find_value database recorder Facts.recursion_group.whole
               (Path.locate_package path) ~id:row.path)
        in
        List.filter_map
          (fun callee ->
            if List.exists (Path.equal callee) members || Path.equal callee path then None
            else Some (Lookups.find_abort database recorder callee))
          (Mir.Call_edges.list_callees_that_run lookups path)
      in
      ( Value
          (if Mir.Call_edges.is_specification_only lookups path then
             { Facts.aborts = false; bound_methods_run = [] }
           else
             let callees = list_callee_aborts () in
             {
               aborts =
                 Mir.Call_edges.has_abort_site lookups path
                 || List.exists (fun (callee : Facts.abort) -> callee.aborts) callees;
               bound_methods_run =
                 List.sort_uniq Path.compare
                   (Mir.Call_edges.list_bound_methods_run lookups path
                   @ List.concat_map
                       (fun (callee : Facts.abort) -> callee.bound_methods_run)
                       callees);
             }),
        [] ))

let write_lowered (database : Tracker.t) ~id outcome =
  if snd (Tracker.write_observed database Facts.lowered ~id (Some outcome)) then
    Tracker.mark_stale database Key_tests id

let supply_lowered (database : Tracker.t) item lowered =
  let id = Ids.of_item item and references = Lowering.list_references lowered in
  ensure_item database item;
  ignore (Store.unmark_stale database.store ~stage:(Kind.rank_stage Lower) ~id);
  let (), changes =
    Tracker.record_observed database Lower id (fun recorder ->
        List.iter
          (fun referenced -> recorder.note References (Entity Item) (Ids.of_item referenced) "")
          references)
  in
  write_lowered database ~id (Value (Ok lowered));
  follow_item_edges database ~items:references changes

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
        | exception Lowering.Infinite_size _ -> (Failed, []))
  in
  write_lowered database ~id outcome;
  follow_item_edges database ~items:references changes;
  references

let run_key_tests (database : Tracker.t) ids =
  let items = List.map (fun id -> (id, read_item database id)) ids in
  let project = Lookups.locate_items database in
  let read view item =
    Tracker.read_value database Tracker.untracked view project ~id:(Ids.of_item item)
  in
  let outcome : _ Tracker.outcome =
    match
      Lowering.derive_test_keys ~read_lowered:(read Facts.lowered.whole)
        ~read_known_key:(read Facts.test_key.whole) (List.map snd items)
    with
    | keys -> Value keys
    | exception Tracker.Reads_failed_fact -> Blocked
  in
  Tracker.report_computed Key_tests ids;
  let rank = Kind.rank_stage Key_tests in
  let changed =
    List.filter
      (fun (id, item) ->
        let key : _ Tracker.outcome =
          match outcome with
          | Value (Ok keys) -> Value (Ok (List.assoc item keys))
          | Value (Error unbuildable) -> Value (Error unbuildable)
          | Failed | Blocked -> Blocked
        in
        snd (Tracker.write_observed database Facts.test_key ~id (Some key)))
      items
  in
  List.iter
    (fun (id, _) ->
      Store.mark_stage_of_sources_stale database.store
        ~target:(Tracker.locate (Entity Item) id "")
        ~source_kind:(Kind.rank_stage Lower) ~markers:references ~stage:rank)
    changed;
  if changed <> [] then
    List.iter (fun id -> ignore (Store.unmark_stale database.store ~stage:rank ~id)) ids

let render_unit (database : Tracker.t) recorder profile item =
  let project = Lookups.locate_items database in
  let find_lowered read =
    match Tracker.find database recorder Facts.lowered.whole project ~id:(Ids.of_item read) with
    | Some (Value (Ok lowered)) -> Some lowered
    | Some (Value (Error _) | Failed | Blocked) | None -> None
  in
  let interface = Lookups.make_interface database recorder ~is_checked:true in
  Option.map
    (Lowering.render_unit (read_host_system ()) interface
       ~source:(Lookups.make_source database recorder)
       profile
       ~read_source:(Lookups.read_source database recorder)
       ~is_worked_on:(Lookups.is_worked_on database) ~find_lowered)
    (match find_lowered item with
    | Some (Compiled fragment | Folded (_, fragment)) -> Some fragment
    | Some (Evaluate (_, ty)) -> (
        match
          Tracker.find database recorder Facts.evaluation.whole project ~id:(Ids.of_item item)
        with
        | Some (Value (Ran encoded)) ->
            Some
              (Lowering.make_data
                 (Lowering.make_env (read_host_system ()) interface)
                 item ty encoded)
        | Some (Value (Unfinished _ | Stopped _) | Failed | Blocked) | None -> None)
    | None -> None)

let record_evaluation (database : Tracker.t) item (result : Lowering.evaluation) =
  let id = Ids.of_item item in
  Tracker.record database Evaluate id (fun recorder ->
      match
        ( Tracker.read database recorder Facts.lowered.whole (Lookups.locate_items database) ~id,
          result )
      with
      | Value (Ok (Evaluate (evaluator, ty))), Ran encoded ->
          recorder.note Reads (Fact Test_key) (Ids.of_item evaluator) "";
          let env =
            Lowering.make_env (read_host_system ())
              (Lookups.make_interface database recorder ~is_checked:true)
          in
          List.iter
            (fun referenced -> recorder.note References (Entity Item) (Ids.of_item referenced) "")
            (Lowering.list_references (Compiled (Lowering.make_data env item ty encoded)))
      | Value (Ok (Evaluate (evaluator, _))), (Unfinished _ | Stopped _) ->
          recorder.note Reads (Fact Test_key) (Ids.of_item evaluator) ""
      | (Value (Ok (Compiled _ | Folded _) | Error _) | Failed | Blocked), _ -> ());
  ignore (Tracker.write database Facts.evaluation ~id (Some (Value result)));
  ignore (Store.unmark_stale database.store ~stage:(Kind.rank_stage Evaluate) ~id)

let record_test_run (database : Tracker.t) item (pass : Lowering.test_pass option) =
  let id = Ids.of_item item in
  match pass with
  | None -> Tracker.forget database Run_test id
  | Some pass ->
      Tracker.record database Run_test id (fun recorder ->
          recorder.note Reads (Fact Test_key) id "");
      ignore (Tracker.write database Facts.test_run ~id (Some (Value pass)));
      ignore (Store.unmark_stale database.store ~stage:(Kind.rank_stage Run_test) ~id)

let run_render profile (database : Tracker.t) id =
  let item = read_item database id in
  let outcome =
    Tracker.record database (Render profile) id (fun recorder ->
        match render_unit database recorder profile item with
        | text -> Option.map (fun text -> Tracker.Value (C_compiler.hash_text text)) text
        | exception Tracker.Reads_failed_fact -> Some Blocked)
  in
  ignore (Tracker.write database (Facts.unit profile) ~id outcome)

let list_linked (database : Tracker.t) profile ~roots =
  Store.list_linked database.store item_graph ~profile:(Facts.rank_profile profile)
    ~unit_kind:(Kind.rank_stage (Render profile))
    ~roots:(List.map Ids.of_item roots)

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
    { stage = Claim_roots; unit_id = Of_definition; applies = is_root; run = run_claim_roots };
    { stage = Resolve; unit_id = Of_definition; applies = is_written; run = run_resolve };
    {
      stage = Read_trait_header;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && decode_kind row = Trait);
      run = run_trait_header;
    };
    {
      stage = Evaluate_constant;
      unit_id = Of_path;
      applies =
        (fun row ->
          is_written row && is_first row
          && match decode_kind row with Constant | Member_constant -> true | _ -> false);
      run = run_constant_value;
    };
    {
      stage = Elaborate_header;
      unit_id = Of_definition;
      applies =
        (fun row ->
          is_written row
          && match decode_kind row with Trait | Impl | Capability -> true | _ -> false);
      run = run_header;
    };
    { stage = Elaborate; unit_id = Of_definition; applies = is_written; run = run_elaborate };
    {
      stage = Derive_interface;
      unit_id = Of_path;
      applies = (fun row -> row.origin = Declarations.derived_impl_origin);
      run = run_derive_interface;
    };
    {
      stage = Compute_type_facts;
      unit_id = Of_path;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Type);
      run = (fun database row -> run_type_facts database [ (Declarations.decode_key row.key).path ]);
    };
    {
      stage = Check_signature;
      unit_id = Of_definition;
      applies = is_written;
      run = run_check_signature;
    };
    {
      stage = Check_contract;
      unit_id = Of_definition;
      applies = is_written;
      run = run_check_contract;
    };
    { stage = Check_body; unit_id = Of_definition; applies = is_written; run = run_check_body };
    {
      stage = Build_body_mir;
      unit_id = Of_definition;
      applies = is_written;
      run = run_build_body_mir;
    };
    {
      stage = Build_contract_mir;
      unit_id = Of_definition;
      applies = is_written;
      run = run_build_contract_mir;
    };
    {
      stage = Generate_mir;
      unit_id = Of_path;
      applies = (fun row -> row.origin = Declarations.derived_method_origin);
      run = run_generate_mir;
    };
    { stage = List_calls; unit_id = Of_path; applies = has_call_node; run = run_list_calls };
    {
      stage = Group_recursion;
      unit_id = Of_path;
      applies = has_call_node;
      run =
        (fun database row -> group_recursion database ~is_node:(fun ~package:_ _ -> false) [ row ]);
    };
    { stage = Find_aborts; unit_id = Of_path; applies = has_call_node; run = run_find_aborts };
    { stage = Check_usage; unit_id = Of_definition; applies = is_written; run = run_check_usage };
    {
      stage = Check_ownership;
      unit_id = Of_definition;
      applies = is_written;
      run = run_check_ownership;
    };
    {
      stage = Check_sealed;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Impl);
      run = run_definition_check Check_sealed (fun key -> Sealed key);
    };
    {
      stage = Check_impl;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Impl);
      run = run_definition_check Check_impl (fun key -> Impl key);
    };
    {
      stage = Check_type;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Type);
      run = run_definition_check Check_type (fun key -> Type key);
    };
    {
      stage = Check_instantiation;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && is_checked_for_instantiation row);
      run = (fun database row -> find_growing_cycles database [ row ]);
    };
    {
      stage = Check_test;
      unit_id = Of_definition;
      applies = (fun row -> is_written row && is_first row && decode_kind row = Test);
      run = run_definition_check Check_test (fun key -> Test key);
    };
    {
      stage = Check_unexported;
      unit_id = Of_path;
      applies =
        (fun row ->
          is_written row && is_first row
          &&
          match decode_kind row with
          | Function | Method | Constant | Member_constant -> true
          | _ -> false);
      run = (fun database row -> classify_uses database [ row ]);
    };
    { stage = Prove; unit_id = Of_definition; applies = is_proven_definition; run = run_prove };
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
      if recipe.applies row then Tracker.forget database recipe.stage (identify_unit recipe row))
    definition_stages;
  if is_proven_definition row then begin
    Tracker.forget database Decide row.id;
    Store.replace_holes database.store ~definition:row.id [];
    ignore (Store.replace_verdicts database.store ~definition:row.id []);
    Store.replace_solver_runs database.store ~definition:row.id []
  end;
  collect_items database claimed;
  if is_impl row then begin
    List.iter
      (fun (supplied : Store.definition) ->
        Store.remove_definition database.store ~id:supplied.id;
        forget_definition database supplied)
      (list_supplied_methods database row);
    Tracker.forget database Supply row.id
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
  let is_added id = List.exists (fun (row : Store.definition) -> row.id = id) written.added in
  List.iter
    (fun ({ lookup; scope; name; is_spans_only } : Declarations.change) ->
      if is_spans_only then Tracker.mark_position_holders database (Lookup lookup) scope name
      else begin
        Tracker.mark_readers database (Lookup lookup) scope name;
        match lookup with
        | (Declaration | Container) when not (is_added scope) ->
            Option.iter
              (fun (row : Store.definition) ->
                Tracker.mark_stale database Check_unexported row.path)
              (Store.find_definition database.store Main ~id:scope)
        | _ -> ()
      end)
    written.changes;
  List.iter (forget_definition database) written.removed;
  List.iter (create_units database) written.added;
  Tracker.report Declare id
    ~is_changed:(written.changes <> [] || written.added <> [] || written.removed <> []);
  if files = [] then begin
    Store.remove_module database.store ~id;
    Tracker.forget database Declare id
  end

let read_dependency (database : Tracker.t) id =
  let dependency =
    match Store.find_dependency database.store ~id with
    | Some dependency -> dependency
    | None -> Compiler_bug.raise_bug ~stage:"Database" "a stale dependency has no row"
  in
  let parse name =
    match Path.parse_package name with
    | Some package -> package
    | None -> Compiler_bug.raise_bug ~stage:"Database" "a dependency names no package"
  in
  (dependency, parse dependency.package, parse dependency.dependency)

let run_grant (database : Tracker.t) id =
  let dependency, package, _ = read_dependency database id in
  let grant =
    Tracker.record database Resolve_grant id (fun recorder ->
        recorder.note Reads (Lookup Dependencies) (Ids.of_package package) "";
        Interface.Grants.resolve_grant
          (Lookups.make_names database recorder)
          ~package
          (Marshal.from_string dependency.capabilities 0))
  in
  ignore (Tracker.write database Facts.grant ~id (Some (Value grant)))

let run_check_dependency (database : Tracker.t) id =
  let _, package, dependency = read_dependency database id in
  let is_used =
    Tracker.record database Check_dependency id (fun recorder ->
        match
          Package_checks.run
            (Lookups.make_package_checks database recorder)
            package (Dependency dependency)
        with
        | Dependency_used is_used -> is_used
        | Placed _ ->
            Compiler_bug.raise_bug ~stage:"Database" "the check of a dependency placed a diagnostic")
  in
  ignore (Tracker.write database Facts.dependency_use ~id (Some (Value is_used)))

let dependency_stages : Kind.stage list = [ Resolve_grant; Check_dependency ]

let forget_dependency database id =
  List.iter (fun stage -> Tracker.forget database stage id) dependency_stages

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

let list_definition_facts () =
  List.concat_map
    (fun recipe -> List.map Tracker.describe (Tracker.list_facts recipe.stage))
    definition_stages

let locate_entity (stage : Kind.stage) : Store.unit_entity =
  match stage with
  | Lower | Key_tests | Evaluate | Run_test | Render _ -> Item_unit
  | Parse | Check_imports -> File_unit
  | Declare -> Module_unit
  | Resolve_grant | Check_dependency -> Dependency_unit
  | Supply | Decide -> Definition_unit
  | Claim_roots | Resolve | Read_trait_header | Evaluate_constant | Elaborate_header | Elaborate
  | Derive_interface | Compute_type_facts | Check_signature | Check_contract | Check_body
  | Build_body_mir | Build_contract_mir | Generate_mir | List_calls | Group_recursion | Find_aborts
  | Check_usage | Check_ownership | Check_sealed | Check_impl | Check_type | Check_instantiation
  | Check_test | Check_unexported | Prove -> (
      match (find_recipe stage).unit_id with
      | Of_definition -> Definition_unit
      | Of_path -> Path_unit)

let list_stale_units (database : Tracker.t) (stage : Kind.stage) ~scope =
  List.filter
    (fun id -> not (Tracker.is_broken database stage id))
    (Store.list_stale database.store ~stage:(Kind.rank_stage stage) ~entity:(locate_entity stage)
       ~scope)

let guard_units (database : Tracker.t) ?on_bug (stage : Kind.stage) ids run =
  let mark_stale () = List.iter (Tracker.mark_stale database stage) ids in
  let fail bug =
    mark_stale ();
    Tracker.record_bug database stage ids bug;
    match on_bug with Some on_bug -> on_bug bug | None -> raise (Compiler_bug.Bug bug)
  in
  match
    Tracker.fail_for_test stage ids;
    run ()
  with
  | () -> ()
  | exception Compiler_bug.Bug bug -> fail bug
  | exception Interface.Properties.Recursion_limit _ ->
      fail
        {
          stage = "Database";
          message = "a stage after the checks reached a recursion limit";
          doing = [];
        }
  | exception raised ->
      let backtrace = Printexc.get_raw_backtrace () in
      mark_stale ();
      Printexc.raise_with_backtrace raised backtrace

let run_units (database : Tracker.t) ?on_bug (stage : Kind.stage) ids run =
  List.iter
    (fun id ->
      if
        (not (Tracker.is_broken database stage id))
        && Store.unmark_stale database.store ~stage:(Kind.rank_stage stage) ~id
      then guard_units database ?on_bug stage [ id ] (fun () -> run database id))
    ids

let drain_decide (database : Tracker.t) ?on_bug ~scope solver =
  match
    List.filter_map
      (fun id -> Store.find_definition database.store Main ~id)
      (list_stale_units database Decide ~scope)
  with
  | [] -> ()
  | rows ->
      let answered = solve_units database (Lazy.force solver) rows in
      List.iter
        (fun (row : Store.definition) ->
          if Store.unmark_stale database.store ~stage:(Kind.rank_stage Decide) ~id:row.id then
            guard_units database ?on_bug Decide [ row.id ] (fun () ->
                run_decide database answered row))
        rows

let drain_stage (database : Tracker.t) ?on_bug (stage : Kind.stage) ~scope =
  let rank = Kind.rank_stage stage in
  let stale = list_stale_units database stage ~scope in
  let guard = guard_units database ?on_bug stage in
  let run_each = run_units database ?on_bug stage stale in
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
  | Check_dependency -> run_each run_check_dependency
  | Check_instantiation | Check_unexported ->
      let recipe = find_recipe stage in
      let find_unit id =
        match recipe.unit_id with
        | Of_definition ->
            Option.bind (Store.find_definition database.store Main ~id) (fun row ->
                if recipe.applies row then Some row else None)
        | Of_path ->
            List.find_opt recipe.applies (Store.list_definitions database.store Main (Of_path id))
      in
      let rows =
        List.filter_map
          (fun id ->
            if Store.unmark_stale database.store ~stage:rank ~id then begin
              let row = find_unit id in
              if Option.is_none row then Tracker.forget database stage id;
              row
            end
            else None)
          stale
      in
      if rows <> [] then
        guard
          (List.map (identify_unit recipe) rows)
          (fun () ->
            if stage = Check_unexported then classify_uses database rows
            else find_growing_cycles database rows)
  | Lower | Key_tests ->
      Compiler_bug.raise_bug ~stage:"Database"
        "an item is lowered and keyed from the claims that reach it"
  | Render _ ->
      Compiler_bug.raise_bug ~stage:"Database" "a unit is rendered when its item is linked"
  | Evaluate ->
      Compiler_bug.raise_bug ~stage:"Database"
        "an evaluation is recorded by the command that runs it"
  | Run_test ->
      Compiler_bug.raise_bug ~stage:"Database" "a test run is recorded by the command that runs it"
  | Decide -> Compiler_bug.raise_bug ~stage:"Database" "Decide is drained with a solver"
  | Find_aborts ->
      let recipe = find_recipe stage in
      let waiting = Hashtbl.create 64 in
      List.iter (fun id -> Hashtbl.replace waiting id ()) stale;
      let read_untracked (fact : Path.t list Tracker.fact) path =
        match
          Tracker.find database Tracker.untracked fact.whole (Path.locate_package path)
            ~id:(Ids.of_path path)
        with
        | Some (Value paths) -> paths
        | Some (Failed | Blocked) | None -> []
      in
      let rec run_after_callees id =
        if Hashtbl.mem waiting id then begin
          let path =
            (Declarations.decode_key (read_first_definition database recipe id).key).path
          in
          let members =
            match read_untracked Facts.recursion_group path with
            | [] -> [ path ]
            | members -> members
          in
          List.iter (fun member -> Hashtbl.remove waiting (Ids.of_path member)) members;
          List.iter
            (fun member ->
              List.iter
                (fun callee -> run_after_callees (Ids.of_path callee))
                (read_untracked Facts.call_node member))
            members;
          run_units database ?on_bug stage (List.map Ids.of_path members) (fun database id ->
              recipe.run database (read_first_definition database recipe id));
          let outside : Facts.abort list =
            List.map
              (fun member : Facts.abort ->
                match
                  Tracker.find database Tracker.untracked Facts.aborts_outside_group.whole
                    (Path.locate_package member) ~id:(Ids.of_path member)
                with
                | Some (Value abort) -> abort
                | Some (Failed | Blocked) -> { aborts = true; bound_methods_run = [] }
                | None -> { aborts = false; bound_methods_run = [] })
              members
          in
          let may_abort : Facts.abort Tracker.outcome =
            Value
              {
                aborts = List.exists (fun (member : Facts.abort) -> member.aborts) outside;
                bound_methods_run =
                  List.sort_uniq Path.compare
                    (List.concat_map
                       (fun (member : Facts.abort) -> member.bound_methods_run)
                       outside);
              }
          in
          List.iter
            (fun member ->
              ignore
                (Tracker.write database Facts.may_abort ~id:(Ids.of_path member) (Some may_abort)))
            members
        end
      in
      List.iter run_after_callees stale
  | Resolve | Read_trait_header | Evaluate_constant | Elaborate_header | Elaborate
  | Derive_interface | Check_signature | Check_body | Build_body_mir | Build_contract_mir
  | Generate_mir | List_calls | Check_usage | Check_ownership | Check_sealed | Check_impl
  | Check_type | Check_test | Prove | Claim_roots ->
      let recipe = find_recipe stage in
      run_each (fun database id -> recipe.run database (read_first_definition database recipe id)));
  stale <> []

let drain_test_keys (database : Tracker.t) ?on_bug ~graph packages =
  let rank = Kind.rank_stage Key_tests in
  let candidates = Hashtbl.create 64 in
  let lower_rank = Kind.rank_stage Lower in
  let rec add_referrers id =
    if not (Hashtbl.mem candidates id) then begin
      Hashtbl.replace candidates id ();
      List.iter
        (fun (referrer : Store.endpoint) ->
          if referrer.kind = lower_rank then add_referrers referrer.id)
        (Store.list_sources database.store
           ~target:(Tracker.locate (Entity Item) id "")
           ~markers:references)
    end
  in
  List.iter add_referrers (list_stale_units database Key_tests ~scope:Everything);
  let list_sorted_ids table =
    List.sort Int.compare (Hashtbl.fold (fun id _ ids -> id :: ids) table [])
  in
  if Hashtbl.length candidates > 0 then begin
    let targets = Hashtbl.create 64 in
    let list_candidate_targets id =
      match Hashtbl.find_opt targets id with
      | Some candidate_targets -> candidate_targets
      | None ->
          let candidate_targets =
            List.filter (Hashtbl.mem candidates) (list_item_targets database Lower id)
          in
          Hashtbl.replace targets id candidate_targets;
          candidate_targets
    in
    let unsettled = Hashtbl.create 16 in
    List.iter
      (fun id -> Hashtbl.replace unsettled id ())
      (Store.list_stale database.store ~stage:(Kind.rank_stage Lower) ~entity:Item_unit
         ~scope:Everything);
    let reached = Hashtbl.create 64 in
    let rec reach id =
      if not (Hashtbl.mem reached id || Hashtbl.mem unsettled id) then begin
        Hashtbl.replace reached id ();
        List.iter reach (list_candidate_targets id)
      end
    in
    List.iter reach
      (Store.list_claimed_among database.store graph ~items:(list_sorted_ids candidates) ~packages);
    List.iter
      (fun component ->
        let was_stale =
          List.map (fun id -> Store.unmark_stale database.store ~stage:rank ~id) component
        in
        if List.exists Fun.id was_stale then
          guard_units database ?on_bug Key_tests component (fun () ->
              run_key_tests database component))
      (Strongly_connected.list_components
         (module Integer_node)
         ~list_successors:(fun id -> List.filter (Hashtbl.mem reached) (list_candidate_targets id))
         (list_sorted_ids reached))
  end

let drain_items_claimed_in (database : Tracker.t) ?on_bug ~graph packages =
  let rec lower_each = function
    | [] -> ()
    | id :: pending ->
        let referenced = ref [] in
        run_units database ?on_bug Lower [ id ] (fun database id ->
            referenced := List.map Ids.of_item (run_lower database id));
        lower_each (!referenced @ pending)
  in
  let rec lower_claimed () =
    match
      List.filter
        (fun item ->
          Store.is_item_claimed database.store graph ~item ~over:(Settled_edges { packages }))
        (list_stale_units database Lower ~scope:Everything)
    with
    | [] -> ()
    | claimed ->
        lower_each claimed;
        lower_claimed ()
  in
  lower_claimed ();
  drain_test_keys database ?on_bug ~graph packages

let drain_claimed_items database ?on_bug packages =
  drain_items_claimed_in database ?on_bug ~graph:item_graph packages

let drain_evaluated_items database ?on_bug packages =
  drain_items_claimed_in database ?on_bug ~graph:evaluation_graph packages

let render_units (database : Tracker.t) ?on_bug profile items =
  run_units database ?on_bug (Render profile) items (run_render profile)
