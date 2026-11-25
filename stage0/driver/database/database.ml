type t = Tracker.t
type 'value outcome = 'value Tracker.outcome = Value of 'value | Failed | Blocked

exception Unusable = Sql.Failed

let make_name_lookups database = Lookups.make_names database Tracker.untracked

let add_package_rows (database : t) (package : Project.package) =
  let name = Path.show_package package.name in
  let dependencies =
    List.map
      (fun (dependency : Manifest.dependency) : Store.dependency ->
        {
          id = Ids.of_dependency package.name dependency.package;
          package = name;
          dependency = Path.show_package dependency.package;
          capabilities = Marshal.to_string dependency.capabilities [];
        })
      package.dependencies
  in
  let dependencies_before = Store.list_dependencies database.store Main ~package:name in
  Store.replace_package database.store ~name ~id:(Ids.of_package package.name) ~dependencies;
  if dependencies_before <> dependencies then begin
    Tracker.mark_readers database (Lookup Dependencies) (Ids.of_package package.name) "";
    List.iter
      (fun (before : Store.dependency) ->
        if not (List.exists (fun (after : Store.dependency) -> after.id = before.id) dependencies)
        then Recipes.forget_dependency database before.id)
      dependencies_before;
    List.iter
      (fun (dependency : Store.dependency) ->
        List.iter
          (fun stage -> Tracker.mark_stale database stage dependency.id)
          Recipes.dependency_stages)
      dependencies
  end;
  if package.name = Well_known.intrinsic_module.package then
    Recipes.replace_builtin_entries database

let add_package (database : t) (package : Project.package) =
  add_package_rows database package;
  List.iter
    (fun (file, text) ->
      Recipes.write_file database ~package:(Path.show_package package.name) file text)
    package.files

let run_past_bugs (database : t) ?on_bug drain =
  Tracker.reset_broken database;
  let bugs = ref [] in
  drain ~on_bug:(fun bug -> bugs := bug :: !bugs);
  match (on_bug, List.rev !bugs) with
  | Some on_bug, bugs -> List.iter on_bug bugs
  | None, bug :: _ -> raise (Compiler_bug.Bug bug)
  | None, [] -> ()

let drain_stages (database : t) ?on_bug stages ~scope =
  run_past_bugs database ?on_bug (fun ~on_bug ->
      List.iter
        (fun stage ->
          while Recipes.drain_stage database ~on_bug stage ~scope do
            ()
          done)
        stages)

let drain (database : t) ?on_bug ~(through : Kind.stage) ~scope () =
  drain_stages database ?on_bug
    (List.filter (fun stage -> Kind.rank_stage stage <= Kind.rank_stage through) Kind.stages)
    ~scope

let scope_packages (database : t) packages : Store.scope =
  Packages (List.map Path.show_package (Lookups.sort_in_dependency_order database packages))

let drain_packages (database : t) ?on_bug ~through packages =
  drain database ?on_bug ~through ~scope:(scope_packages database packages) ()

let last_checking_stage : Kind.stage = Check_dependency
let loaded_meta = "loaded"
let compiler_meta = "compiler"

let attach_loaded (database : t) loaded =
  Store.replace_routes database.store
    (List.concat_map
       (fun path ->
         let schema = Store.attach database.store path in
         List.filter_map
           (fun name -> Option.map (fun package -> (package, schema)) (Path.parse_package name))
           (Store.list_packages database.store schema))
       loaded);
  Store.write_meta database.store loaded_meta (Marshal.to_string loaded [])

let create_in_memory ?on_bug ~loaded ~records_reads (packages : Project.package list) : t =
  let database = Tracker.create (Store.create_memory ()) ~records_reads in
  attach_loaded database loaded;
  Store.replace_project database.store
    (List.map (fun (package : Project.package) -> package.name) packages);
  List.iter (add_package database) packages;
  drain database ?on_bug ~through:last_checking_stage ~scope:Everything ();
  database

let create ?on_bug ?(loaded = []) packages =
  create_in_memory ?on_bug ~loaded ~records_reads:true packages

let update ?on_bug (database : t) changes =
  List.iter
    (fun ((file : Path.file), text) ->
      let package = file.module_.package in
      if not (List.mem package (Store.list_project database.store)) then
        Compiler_bug.raise_bug ~stage:"Database" "%s is not a package of the build"
          (Path.show_package package);
      match text with
      | Some text -> (
          match Store.find_file database.store Main ~id:(Ids.of_file file) with
          | Some previous when String.equal previous.text text -> ()
          | Some _ | None ->
              Recipes.write_file database ~package:(Path.show_package package) file text)
      | None -> Recipes.remove_file database file)
    changes;
  drain database ?on_bug ~through:last_checking_stage ~scope:Everything ()

let list_routes (database : t) =
  List.filter_map
    (fun path ->
      match Store.locate_attached database.store path with
      | Some schema -> Some (path, List.sort compare (Store.list_packages database.store schema))
      | None -> None)
    (Store.list_attached database.store)

let retire (database : t) (package : Path.package) =
  let name = Path.show_package package in
  List.iter
    (fun (file : Store.file) -> Recipes.remove_file database (Declarations.decode_file file.key))
    (Store.list_files database.store Main (Of_package name));
  List.iter
    (fun (dependency : Store.dependency) -> Recipes.forget_dependency database dependency.id)
    (Store.list_dependencies database.store Main ~package:name);
  Store.remove_package database.store ~name

let list_differing_ids (database : t) ~table ~id_column ~before ~after =
  List.map
    (function
      | [| Store.Integer id |] -> id
      | _ ->
          Compiler_bug.raise_bug ~stage:"Database" "a row of %s is identified by no integer" table)
    (Store.list_differing_rows database.store ~table ~columns:[ id_column ] ~before ~after)

let mark_readers_of_replaced_packages (database : t) ~routes_before ~routes_after =
  let locate routes package =
    List.find_map
      (fun (path, packages) -> if List.mem package packages then Some path else None)
      routes
  in
  List.iter
    (fun (before, after) ->
      let before = Option.bind before (Store.locate_attached database.store)
      and after = Option.bind after (Store.locate_attached database.store) in
      Tracker.mark_readers_of_all database
        (List.map
           (fun (lookup, scope, name) -> (Kind.Lookup lookup, scope, name))
           (Declarations.list_replaced_lookups database.store ~before ~after)
        @ List.concat_map
            (fun ({ table; id_column; read_targets; _ } : Tracker.description) ->
              List.concat_map
                (fun id -> List.map (fun fact -> (Kind.Fact fact, id, "")) read_targets)
                (list_differing_ids database ~table ~id_column ~before ~after))
            (Tracker.describe (Any Facts.grant) :: Recipes.list_definition_facts ())))
    (List.sort_uniq compare
       (List.filter_map
          (fun package ->
            let before = locate routes_before package and after = locate routes_after package in
            if before = after then None else Some (before, after))
          (List.concat_map snd (routes_before @ routes_after))))

let record_layout (database : t) ~loaded (packages : Project.package list) =
  let project = List.map (fun (package : Project.package) -> package.name) packages in
  let project_before = Store.list_project database.store in
  let routes_before = list_routes database in
  let list_visible routes = List.sort_uniq compare (List.concat_map snd routes) in
  List.iter
    (fun package -> if not (List.mem package project) then retire database package)
    project_before;
  List.iter (fun path -> ignore (Store.attach database.store path)) loaded;
  let routes_after = List.filter (fun (path, _) -> List.mem path loaded) (list_routes database) in
  mark_readers_of_replaced_packages database ~routes_before ~routes_after;
  List.iter
    (fun path -> if not (List.mem path loaded) then Store.detach database.store path)
    (Store.list_attached database.store);
  attach_loaded database loaded;
  Store.replace_project database.store project;
  if project <> project_before then
    Store.mark_items_stale database.store ~stage:(Kind.rank_stage (Render Development));
  List.iter
    (fun (package : Project.package) ->
      if List.mem package.name project_before then begin
        add_package_rows database package;
        List.iter
          (fun (file : Store.file) ->
            let path = Declarations.decode_file file.key in
            if not (List.mem_assoc path package.files) then Recipes.remove_file database path)
          (Store.list_files database.store Main (Of_package (Path.show_package package.name)));
        List.iter
          (fun ((file : Path.file), text) ->
            match Store.find_file database.store Main ~id:(Ids.of_file file) with
            | Some previous when String.equal previous.text text -> ()
            | Some _ | None ->
                Recipes.write_file database ~package:(Path.show_package package.name) file text)
          package.files
      end
      else add_package database package)
    packages;
  if
    list_visible routes_before <> list_visible routes_after
    || List.sort compare project <> List.sort compare project_before
  then Tracker.mark_readers database (Lookup Packages) 0 ""

let relayout ?on_bug (database : t) ~loaded packages =
  record_layout database ~loaded packages;
  drain database ?on_bug ~through:last_checking_stage ~scope:Everything ()

let remove_database_file path =
  List.iter
    (fun suffix -> try Sys.remove (path ^ suffix) with Sys_error _ -> ())
    [ ""; "-wal"; "-shm" ]

let open_saved path ~compiler =
  if not (Sys.file_exists path) then None
  else
    match Store.open_file path with
    | exception Sql.Failed _ -> None
    | store -> (
        match
          ( Store.find_meta store compiler_meta,
            Option.map
              (fun paths : string list -> Marshal.from_string paths 0)
              (Store.find_meta store loaded_meta) )
        with
        | Some saved_compiler, Some paths
          when saved_compiler = compiler && List.for_all Sys.file_exists paths ->
            let database = Tracker.create store ~records_reads:true in
            attach_loaded database paths;
            Store.replace_project store
              (List.filter_map Path.parse_package (Store.list_packages store Main));
            Some database
        | _ ->
            Store.close store;
            None
        | exception Sql.Failed _ ->
            Store.close store;
            None)

let open_file ?on_bug path ~compiler ~loaded packages =
  let restored =
    Option.bind (open_saved path ~compiler) (fun database ->
        match record_layout database ~loaded packages with
        | () -> Some database
        | exception (Sql.Failed _ | Failure _ | Invalid_argument _ | End_of_file) ->
            Store.close database.store;
            None)
  in
  let database =
    match restored with
    | Some database -> database
    | None ->
        remove_database_file path;
        let database = Tracker.create (Store.open_file path) ~records_reads:true in
        Store.write_meta database.store compiler_meta compiler;
        attach_loaded database loaded;
        Store.replace_project database.store
          (List.map (fun (package : Project.package) -> package.name) packages);
        List.iter (add_package database) packages;
        database
  in
  drain database ?on_bug ~through:last_checking_stage ~scope:Everything ();
  database

let commit (database : t) = Store.commit database.store
let close (database : t) = Store.close database.store
let close_uncommitted (database : t) = Store.close_uncommitted database.store

let copy (database : t) : t =
  {
    database with
    store = Store.copy database.store;
    bugs = Hashtbl.copy database.bugs;
    broken = Hashtbl.copy database.broken;
  }

let merge_packages paths ~into = Store.merge paths ~into

type checker =
  | Parse
  | Resolve
  | Interface
  | Infer
  | Usage
  | Ownership
  | Package_checks
  | Unexported

let find_checker (stage : Kind.stage) : checker option =
  match stage with
  | Parse -> Some Parse
  | Resolve | Check_imports -> Some Resolve
  | Elaborate_header | Elaborate | Check_signature -> Some Interface
  | Check_contract | Check_body -> Some Infer
  | Check_usage -> Some Usage
  | Check_ownership -> Some Ownership
  | Check_sealed | Check_impl | Check_type | Check_instantiation | Check_test -> Some Package_checks
  | Check_unexported -> Some Unexported
  | Declare | Supply | Claim_roots | Resolve_grant | Read_trait_header | Evaluate_constant
  | Derive_interface | Compute_type_facts | Build_body_mir | Build_contract_mir | Generate_mir
  | List_calls | Group_recursion | Check_dependency | Prove | Lower | Key_tests | Evaluate
  | Render _ | Decide ->
      None

let has_unchecked_body (database : t) (package : Path.package) =
  Store.locate_schema database.store package = Main
  && Store.has_unchecked_body database.store ~package:(Path.show_package package) ~skipped_kind:None

let decode_placed (placed : Store.placed) : Renderer.placed =
  {
    file = Declarations.decode_file placed.file;
    base = placed.base;
    stop = placed.stop;
    spans = Marshal.from_string placed.spans 0;
  }

let make_render_lookups (database : t) placed_by_key : Renderer.lookups =
  let texts = Hashtbl.create 4 in
  {
    read_placed =
      (fun key ->
        match Hashtbl.find_opt placed_by_key key with
        | Some placed -> placed
        | None -> (
            match
              Store.find_placed database.store
                (Store.locate_schema database.store key.module_.package)
                ~definition:(Ids.of_key key)
            with
            | Some placed -> decode_placed placed
            | None ->
                Compiler_bug.raise_bug ~stage:"Database" "%s has no place in a file"
                  (Resolve.Names.show_key key)));
    read_file_text =
      (fun file ->
        match Hashtbl.find_opt texts file with
        | Some text -> text
        | None ->
            let text = Source.text (Lookups.read_source database Tracker.untracked file) in
            Hashtbl.replace texts file text;
            text);
  }

let decode_rows rows find_placed =
  let placed_by_key = Hashtbl.create 16 in
  let decoded =
    List.map
      (fun row ->
        ( row,
          Option.map
            (fun (key, placed) ->
              let key = Declarations.decode_key key in
              Hashtbl.replace placed_by_key key (decode_placed placed);
              key)
            (find_placed row) ))
      rows
  in
  (decoded, placed_by_key)

let list_located (database : t) (file : Path.file) ~is_selected : Diagnostic.t list =
  let hides_unused = lazy (has_unchecked_body database file.module_.package) in
  let is_shown (stage : Kind.stage) = stage <> Check_unexported || not (Lazy.force hides_unused) in
  let rows, placed_by_key =
    decode_rows
      (Store.list_file_diagnostics database.store
         (Store.locate_schema database.store file.module_.package)
         ~file:(Ids.of_file file) ~test_kind:(Declarations.rank_kind Test))
      (fun (located : Store.located) -> located.definition)
  in
  let lookups = make_render_lookups database placed_by_key in
  let render (located : Store.located) = function
    | Some key ->
        Renderer.render lookups key (Marshal.from_string located.detail 0 : Catalog.diagnostic)
    | None ->
        Renderer.render_file_diagnostic ~text:(lookups.read_file_text file)
          (Marshal.from_string located.detail 0 : Renderer.file_diagnostic)
  in
  List.sort_uniq
    (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    (List.filter_map
       (fun ((located : Store.located), key) ->
         let stage = List.nth Kind.stages located.stage in
         match find_checker stage with
         | Some checker when is_shown stage && is_selected checker located ->
             Some (render located key)
         | Some _ | None -> None)
       rows)

let list_diagnostics checkers database file =
  list_located database file ~is_selected:(fun checker _ -> List.mem checker checkers)

let list_file_diagnostics database file = list_located database file ~is_selected:(fun _ _ -> true)

let list_blocking_diagnostics database file =
  List.filter Diagnostic.is_error
    (list_located database file ~is_selected:(fun checker located ->
         match checker with
         | Parse -> true
         | Resolve | Interface | Infer | Usage | Ownership ->
             Option.is_some located.definition && not located.is_in_test
         | Package_checks | Unexported -> false))

let read_source (database : t) = Lookups.read_source database Tracker.untracked

let require_package (database : t) package =
  if
    not
      (List.mem package (Store.list_project database.store)
      || Store.locate_schema database.store package <> Main)
  then
    Compiler_bug.raise_bug ~stage:"Database" "%s is not a package of the build"
      (Path.show_package package)

let list_dependency_diagnostics (database : t) package =
  require_package database package;
  List.filter_map
    (fun (row : Store.file) ->
      let file = Declarations.decode_file row.key in
      match list_blocking_diagnostics database file with
      | [] -> None
      | diagnostics -> Some (read_source database file, diagnostics))
    (Store.list_files database.store
       (Store.locate_schema database.store package)
       (Of_package (Path.show_package package)))

let last_stage_before_lowering : Kind.stage = List_calls

let drain_claimed_items (database : t) ?on_bug packages =
  run_past_bugs database ?on_bug (fun ~on_bug ->
      Recipes.drain_claimed_items database ~on_bug
        (Option.map (List.map Path.show_package) packages))

let drain_lowering (database : t) ?on_bug packages =
  drain_packages database ?on_bug ~through:last_stage_before_lowering packages;
  drain_claimed_items database ?on_bug (Some (Lookups.sort_in_dependency_order database packages))

let make_interface_lookups database =
  Lookups.make_interface database Tracker.untracked ~is_checked:true

let make_proof_lookups database = Lookups.make_proof database Tracker.untracked

let find_value database fact (key : Resolve.Names.key) =
  match
    Tracker.find database Tracker.untracked fact.Tracker.whole key.module_.package
      ~id:(Ids.of_key key)
  with
  | Some (Tracker.Value value) -> Some value
  | Some (Failed | Blocked) | None -> None

let read_resolved database key =
  match
    List.filter_map
      (fun section -> find_value database (Facts.resolved section) key)
      Resolve.sections
  with
  | [] -> None
  | sections -> Some (Resolve.merge sections)

let read_checked_body database key = find_value database Facts.body key
let read_parsed database (file : Path.file) = fst (Parser.parse_source (read_source database file))

let find_main database package =
  List.find_map
    (fun (declaration : Resolve.Names.declaration) ->
      if
        Path.is_entry_point declaration.key.path
        && declaration.kind = Function && declaration.key.ordinal = 0
      then Some declaration.key.path
      else None)
    ((make_name_lookups database).list_declarations { package; modules = [] })

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; capability : Grant.capability }
  | Unused_dependency of Path.package

let list_manifest_problems (database : t) package =
  let read fact ~id =
    match Tracker.find database Tracker.untracked fact.Tracker.whole package ~id with
    | Some (Tracker.Value value) -> Some value
    | Some (Failed | Blocked) | None -> None
  in
  let dependencies = (make_name_lookups database).list_dependency_names package in
  List.concat_map
    (fun dependency ->
      match read Facts.grant ~id:(Ids.of_dependency package dependency) with
      | Some (grant : Interface.Environment.grant) ->
          List.map (fun capability -> Not_a_capability { dependency; capability }) grant.unknown
      | None -> [])
    dependencies
  @
  if has_unchecked_body database package then []
  else
    List.filter_map
      (fun dependency ->
        match read Facts.dependency_use ~id:(Ids.of_dependency package dependency) with
        | Some false -> Some (Unused_dependency dependency)
        | Some true | None -> None)
      dependencies

let find_code_packages (database : t) package =
  Option.map
    (List.filter_map Path.parse_package)
    (Store.list_code_packages database.store ~package:(Path.show_package package)
       ~unit_kind:(Kind.rank_stage Check_body)
       ~target_kind:(Kind.rank_target (Entity Package))
       ~test_kind:(Declarations.rank_kind Test))

let has_errors (database : t) package =
  if List.mem package (Store.list_project database.store) then
    Store.has_error database.store ~package:(Path.show_package package)
      ~last_stage:(Kind.rank_stage last_checking_stage)
      ~hidden_stage:
        (if has_unchecked_body database package then Some (Kind.rank_stage Check_unexported)
         else None)
  else if Store.locate_schema database.store package <> Main then
    list_dependency_diagnostics database package <> []
  else true

type proof_scope = In_packages of Path.package list | In_files of Path.file list
type proofs = { database : t; scope : proof_scope }

let find_proof (database : t) (key : Resolve.Names.key) =
  Tracker.find database Tracker.untracked Facts.proof.whole key.module_.package ~id:(Ids.of_key key)

let list_proof_packages proofs =
  List.sort_uniq Path.compare_package
    (match proofs.scope with
    | In_packages packages -> packages
    | In_files files -> List.map (fun (file : Path.file) -> file.module_.package) files)

let scope_proofs proofs : Store.scope =
  match proofs.scope with
  | In_packages packages -> Packages (List.map Path.show_package packages)
  | In_files files -> Files (List.map Ids.of_file files)

let prove ?on_bug (database : t) scope =
  let proofs = { database; scope } in
  let packages = list_proof_packages proofs in
  drain_packages database ?on_bug ~through:last_checking_stage packages;
  drain_stages database ?on_bug [ Prove ] ~scope:(scope_proofs proofs);
  (match
     Store.find_unproven_definition database.store ~scope:(scope_proofs proofs)
       ~origin:Declarations.written_origin
   with
  | Some key
    when not
           (List.exists (has_errors database) (Lookups.sort_in_dependency_order database packages))
    ->
      Compiler_bug.raise_bug ~stage:"Database"
        "the proof of %s is blocked, and no code of its package or of a package it depends on has \
         a diagnostic"
        (Resolve.Names.show_key (Declarations.decode_key key))
  | Some _ | None -> ());
  proofs

let list_proof_keys proofs =
  let names = make_name_lookups proofs.database in
  List.map
    (fun (declaration : Resolve.Names.declaration) -> declaration.key)
    (match proofs.scope with
    | In_packages packages -> List.concat_map names.list_package_declarations packages
    | In_files files -> List.concat_map names.list_declarations_in files)

let find_item_outcome (database : t) fact item =
  Tracker.find database Tracker.untracked fact.Tracker.whole (Lookups.locate_items database)
    ~id:(Ids.of_item item)

let list_evaluations proofs =
  let database = proofs.database in
  match
    List.sort_uniq compare
      (List.concat_map
         (fun id ->
           match
             Option.bind (Store.find_definition database.store Main ~id)
               (fun (row : Store.definition) ->
                 find_proof database (Declarations.decode_key row.key))
           with
           | Some (Value proof) -> Prover.list_evaluations proof
           | Some (Failed | Blocked) | None -> [])
         (Recipes.list_stale_units database Decide ~scope:(scope_proofs proofs)))
  with
  | [] -> []
  | evaluations ->
      drain_lowering database (list_proof_packages proofs);
      List.filter
        (fun root ->
          match find_item_outcome proofs.database Facts.test_key root with
          | Some (Blocked | Value (Error (Todo_types _))) -> false
          | Some (Value (Ok _ | Error (Unsupported _)) | Failed) | None -> true)
        (List.map Recipes.make_evaluation_root evaluations)

let decide ?on_bug proofs solver =
  run_past_bugs proofs.database ?on_bug (fun ~on_bug ->
      Recipes.drain_decide proofs.database ~on_bug ~scope:(scope_proofs proofs) solver)

type proof_site = { code : string; span : Source.span; shows : string }
type proof_state = { site : proof_site; is_proven : bool; trusts_compiled_code : bool }

let list_verdicts (database : t) (file : Path.file) =
  let rows, placed_by_key =
    decode_rows
      (Store.list_file_verdicts database.store ~file:(Ids.of_file file))
      (fun (key, placed, _) -> Some (key, placed))
  in
  ( List.map (fun ((_, _, verdict), key) -> (Option.get key, verdict)) rows,
    make_render_lookups database placed_by_key )

let render_site lookups key ({ code; site; _ } : Store.verdict) =
  let shown =
    Renderer.render lookups key (Prover (Marshal.from_string site 0 : Catalog.Prover.t))
  in
  { code; span = shown.span; shows = shown.message }

let list_proof_states (database : t) (file : Path.file) =
  let verdicts, lookups = list_verdicts database file in
  List.stable_sort
    (fun left right -> compare (left.site.span, left.site.code) (right.site.span, right.site.code))
    (List.map
       (fun (key, ({ is_proven; trusts_compiled_code; _ } as verdict : Store.verdict)) ->
         { site = render_site lookups key verdict; is_proven; trusts_compiled_code })
       verdicts)

let describe_proof_failure (database : t) (lookups : Renderer.lookups) (file : Path.file) failure =
  match Catalog.Prover_description.find_cited failure with
  | None -> Catalog.Prover_description.describe failure
  | Some { key = cited; origin } ->
      let placed = lookups.read_placed cited in
      if placed.file = file then Catalog.Prover_description.describe_cited failure Cited_here
      else
        let source = Lookups.read_source database Tracker.untracked placed.file in
        let clause = Renderer.locate lookups cited origin in
        Catalog.Prover_description.describe_cited failure
          (Cited_at
             { path = Source.path source; line = fst (Source.compute_position source clause.start) })

let list_proof_diagnostics (database : t) (file : Path.file) =
  let verdicts, lookups = list_verdicts database file in
  let _, failures =
    List.fold_left
      (fun (shown_failures, failures) (key, (verdict : Store.verdict)) ->
        match verdict.failure with
        | None -> (shown_failures, failures)
        | Some failure ->
            let site = render_site lookups key verdict in
            let shown = (key, site.code, site.shows) in
            if List.mem shown shown_failures then (shown_failures, failures)
            else
              ( shown :: shown_failures,
                Renderer.render_description lookups key
                  (describe_proof_failure database lookups file
                     (Marshal.from_string failure 0 : Catalog.Prover.t))
                :: failures ))
      ([], []) verdicts
  in
  List.sort
    (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    failures

let list_unit_targets (database : t) stage id =
  List.map
    (fun (edge : Store.edge) -> edge.target)
    (Store.list_edges database.store Main ~source:(Tracker.locate_unit stage id))

let list_holes proofs ~reached =
  let database = proofs.database in
  let names = make_name_lookups database in
  let proven_by_path = Hashtbl.create 64 and proven_by_id = Hashtbl.create 64 in
  List.iter
    (fun (key : Resolve.Names.key) ->
      Hashtbl.replace proven_by_path (Ids.of_path key.path) key;
      Hashtbl.replace proven_by_id (Ids.of_key key) key)
    (list_proof_keys proofs);
  let contract_kind = Kind.rank_target (Fact Contract_mir)
  and definition_kind = Kind.rank_target (Entity Definition) in
  let list_next (key : Resolve.Names.key) =
    List.filter_map
      (fun (target : Store.endpoint) ->
        if target.kind = contract_kind then
          Option.map
            (fun (contract : Resolve.Names.key) -> Ids.of_path contract.path)
            (Hashtbl.find_opt proven_by_id target.id)
        else None)
      (list_unit_targets database Prove (Ids.of_key key))
    @ List.filter_map
        (fun (_, callee) ->
          match (Declarations.decode_key callee).path with
          | Method { owner = Impl _ as impl; _ } -> Some (Ids.of_path impl)
          | _ -> None)
        (Store.list_keys_of_paths database.store
           ~paths:
             (List.filter_map
                (fun (target : Store.endpoint) ->
                  if target.kind = definition_kind then Some target.id else None)
                (list_unit_targets database List_calls (Ids.of_path key.path))))
  in
  let locate ({ home; start; _ } : Store.hole) =
    match Store.find_definition_key_anywhere database.store ~id:home with
    | Some key ->
        let ({ file; base } : Resolve.Names.place) =
          names.read_place (Declarations.decode_key key)
        in
        let line, column = Source.compute_position (read_source database file) (base + start) in
        (file, line, column)
    | None -> Compiler_bug.raise_bug ~stage:"Database" "a hole is in a definition with no row"
  in
  let visited = Hashtbl.create 64 and pending = Queue.create () in
  let visit way path =
    match Hashtbl.find_opt proven_by_path path with
    | Some (key : Resolve.Names.key) when not (Hashtbl.mem visited path) ->
        Hashtbl.replace visited path ();
        Queue.add (key, way @ [ key.path ]) pending
    | Some _ | None -> ()
  in
  List.iter (fun path -> visit [] (Ids.of_path path)) reached;
  let rec collect holes =
    match Queue.take_opt pending with
    | None -> List.rev holes
    | Some (key, way) ->
        List.iter (visit way) (list_next key);
        collect
          (List.rev_append
             (List.map
                (fun hole ->
                  let file, line, column = locate hole in
                  (file, line, column, way))
                (Store.list_holes database.store
                   (Store.locate_schema database.store key.module_.package)
                   ~definition:(Ids.of_key key)))
             holes)
  in
  collect []

let read_reached database fact item =
  match find_item_outcome database fact item with
  | Some (Tracker.Value value) -> value
  | Some (Failed | Blocked) ->
      Compiler_bug.raise_bug ~stage:"Database" "%s is read from code with errors"
        (Lowered.Item.to_string item)
  | None ->
      Compiler_bug.raise_bug ~stage:"Database" "%s is read, and no root of lowering reaches it"
        (Lowered.Item.to_string item)

let list_linked (database : t) profile roots : Lowering.linked list =
  let rows = Recipes.list_linked database profile ~roots in
  let is_rendered_by_listing (row : Store.linked) = row.is_unit_stale && not row.is_unevaluated in
  run_past_bugs database (fun ~on_bug ->
      Recipes.render_units database ~on_bug profile
        (List.filter_map
           (fun (row : Store.linked) ->
             if is_rendered_by_listing row then Some row.linked_id else None)
           rows));
  List.iter
    (fun root ->
      let id = Ids.of_item root in
      if not (List.exists (fun (row : Store.linked) -> row.linked_id = id) rows) then
        Compiler_bug.raise_bug ~stage:"Database" "%s is linked, and no root of lowering reaches it"
          (Lowered.Item.to_string root))
    roots;
  List.map
    (fun (row : Store.linked) : Lowering.linked ->
      let item : Lowered.Item.t = Marshal.from_string row.linked_key 0 in
      let text_hash =
        if is_rendered_by_listing row then
          match find_item_outcome database (Facts.unit profile) item with
          | Some (Value text_hash) -> Some text_hash
          | Some (Failed | Blocked) | None -> None
        else Option.map (fun text_hash : string -> Marshal.from_string text_hash 0) row.text_hash
      in
      match (text_hash, row.sites) with
      | Some text_hash, Some sites -> Unit { item; text_hash; sites = Marshal.from_string sites 0 }
      | _ -> (
          match find_item_outcome database Facts.lowered item with
          | Some (Value (Ok (Evaluate (evaluator, _)))) -> Evaluated { item; evaluator }
          | Some (Value (Error unbuildable)) -> Unbuildable unbuildable
          | Some (Value (Ok (Compiled _ | Folded _)) | Failed | Blocked) | None ->
              Compiler_bug.raise_bug ~stage:"Database" "%s is linked from code with errors"
                (Lowered.Item.to_string item)))
    rows

let render_unit (database : t) profile item =
  match Recipes.render_unit database Tracker.untracked profile item with
  | Some text -> text
  | None ->
      Compiler_bug.raise_bug ~stage:"Database" "%s is rendered, and has no code"
        (Lowered.Item.to_string item)

let find_lowered_lookups (database : t) packages : (Lowering.lowered_lookups, string) result =
  match Libc.host with
  | Error message -> Error message
  | Ok system ->
      drain_lowering database packages;
      Ok
        {
          system;
          read_source = read_source database;
          interface = make_interface_lookups database;
          find_evaluation =
            (fun item ->
              match
                Tracker.find_settled database Tracker.untracked Facts.evaluation.whole
                  (Lookups.locate_items database) ~id:(Ids.of_item item)
              with
              | Some (Value evaluation) -> Some evaluation
              | Some (Failed | Blocked) | None -> None);
          record_evaluation = Recipes.record_evaluation database;
          find_lowered =
            (fun item ->
              match find_item_outcome database Facts.lowered item with
              | Some (Value lowered) -> Some lowered
              | Some (Failed | Blocked) -> None
              | None ->
                  Compiler_bug.raise_bug ~stage:"Database"
                    "%s is read, and no root of lowering reaches it" (Lowered.Item.to_string item));
          read_test_key = read_reached database Facts.test_key;
          list_linked = list_linked database;
          render_unit = render_unit database;
        }

type read = {
  reader : Path.t;
  reader_kind : string;
  read : Path.t;
  read_kind : string;
  is_signature : bool;
}

let describe_target rank =
  match Kind.find_target rank with
  | Some (Fact fact) -> Some (Kind.show_fact fact, Kind.is_signature fact)
  | Some (Lookup lookup) when List.mem lookup Kind.lookups_of_definition ->
      Some (Kind.show_lookup lookup, false)
  | Some (Lookup _ | Entity _ | Selection _) | None -> None

let list_reads (database : t) paths ~is_source =
  let reads = Kind.encode_markers [ Reads ] in
  let lowering = List.map Kind.rank_stage Recipes.item_stages in
  let stages_of_definitions =
    List.filter (fun stage -> not (List.mem stage lowering)) (List.map Kind.rank_stage Kind.stages)
  in
  List.concat_map
    (fun path ->
      let path_id = Ids.of_path path in
      let own =
        path_id
        :: List.map
             (fun (id, _, _) -> id)
             (Store.list_definitions_identified database.store ~ids:[ path_id ])
      in
      let edges =
        List.filter
          (fun (edge : Store.read_edge) -> not (List.mem edge.source_kind lowering))
          (if is_source then
             Store.list_edges_from database.store Main ~source_kinds:stages_of_definitions
               ~sources:own ~markers:reads
           else
             Store.list_edges_into database.store
               ~target_kinds:
                 (List.map (fun fact -> Kind.rank_target (Fact fact)) Kind.facts_of_definition
                 @ List.map
                     (fun lookup -> Kind.rank_target (Lookup lookup))
                     Kind.lookups_of_definition)
               ~targets:own ~markers:reads)
      in
      let other_ids =
        List.sort_uniq Int.compare
          (List.map
             (fun (edge : Store.read_edge) -> if is_source then edge.target else edge.source)
             edges)
      in
      let paths_by_id = Hashtbl.create 64 in
      List.iter
        (fun (id, other_path_id, key) ->
          let other = (Declarations.decode_key key).path in
          Hashtbl.replace paths_by_id id other;
          Hashtbl.replace paths_by_id other_path_id other)
        (Store.list_definitions_identified database.store ~ids:other_ids);
      List.filter_map
        (fun (edge : Store.read_edge) ->
          match
            ( Hashtbl.find_opt paths_by_id (if is_source then edge.target else edge.source),
              describe_target edge.target_kind )
          with
          | Some other, Some (read_kind, is_signature) when not (Path.equal other path) ->
              let reader_kind = Kind.show_stage (List.nth Kind.stages edge.source_kind) in
              Some
                (if is_source then
                   { reader = path; reader_kind; read = other; read_kind; is_signature }
                 else { reader = other; reader_kind; read = path; read_kind; is_signature })
          | _ -> None)
        edges)
    (List.sort_uniq Path.compare paths)

let list_dependencies database paths = list_reads database paths ~is_source:true
let list_dependents database paths = list_reads database paths ~is_source:false

type counts = {
  kind : string;
  computed : int;
  unchanged : int;
  writes : int;
  reads : int;
  distinct_reads : int;
}

let count run =
  let counts_by_kind = Hashtbl.create 32 in
  let add stage increment =
    let kind = Kind.show_stage stage in
    let rank, counts =
      Option.value
        (Hashtbl.find_opt counts_by_kind kind)
        ~default:
          ( Kind.rank_stage stage,
            { kind; computed = 0; unchanged = 0; writes = 0; reads = 0; distinct_reads = 0 } )
    in
    Hashtbl.replace counts_by_kind kind (rank, increment counts)
  in
  let result =
    Tracker.with_observer
      (function
        | Computed { stage; ids; reads; distinct_reads } ->
            add stage (fun counts ->
                {
                  counts with
                  computed = counts.computed + List.length ids;
                  reads = counts.reads + reads;
                  distinct_reads = counts.distinct_reads + distinct_reads;
                })
        | Unchanged { stage; _ } ->
            add stage (fun counts -> { counts with unchanged = counts.unchanged + 1 })
        | Written { stage; _ } ->
            add stage (fun counts -> { counts with writes = counts.writes + 1 }))
      run
  in
  ( result,
    List.map snd
      (List.sort
         (fun (rank, _) (other_rank, _) -> Int.compare rank other_rank)
         (List.of_seq (Hashtbl.to_seq_values counts_by_kind))) )

type statement_count = { statement : string; runs : int; steps : int; seconds : float }

let count_statements run =
  let counts = Hashtbl.create 64 in
  let result =
    Sql.with_observer
      (fun statement ~seconds ~steps ->
        let count =
          Option.value
            (Hashtbl.find_opt counts statement)
            ~default:{ statement; runs = 0; steps = 0; seconds = 0.0 }
        in
        Hashtbl.replace counts statement
          {
            count with
            runs = count.runs + 1;
            steps = count.steps + steps;
            seconds = count.seconds +. seconds;
          })
      run
  in
  ( result,
    List.sort
      (fun count other ->
        match Float.compare other.seconds count.seconds with
        | 0 -> String.compare count.statement other.statement
        | order -> order)
      (List.of_seq (Hashtbl.to_seq_values counts)) )

type change = { changed : Path.t; kind : string; is_signature : bool }

let list_changes (database : t) (other : t) =
  let locate_files (database : t) =
    List.concat_map
      (fun (path, packages) -> List.map (fun package -> (package, path)) packages)
      (list_routes database)
  in
  let files_after = locate_files other in
  let replaced =
    List.sort_uniq compare
      (List.filter_map
         (fun (package, before) ->
           match List.assoc_opt package files_after with
           | Some after when after <> before -> Some (before, after)
           | Some _ | None -> None)
         (locate_files database))
  in
  List.sort_uniq compare
    (List.concat_map
       (fun (before, after) ->
         match Store.locate_attached database.store before with
         | None -> []
         | Some left ->
             let right = Store.attach database.store after in
             Fun.protect
               ~finally:(fun () -> Store.detach database.store after)
               (fun () ->
                 List.concat_map
                   (fun ({ table; id_column; read_targets; _ } : Tracker.description) ->
                     let ids =
                       list_differing_ids database ~table ~id_column ~before:(Some left)
                         ~after:(Some right)
                     in
                     List.concat_map
                       (fun (_, _, key) ->
                         List.map
                           (fun fact ->
                             {
                               changed = (Declarations.decode_key key).path;
                               kind = Kind.show_fact fact;
                               is_signature = Kind.is_signature fact;
                             })
                           read_targets)
                       (Store.list_definitions_identified database.store ~ids))
                   (Recipes.list_definition_facts ())))
       replaced)

let build_package ~loaded (package : Project.package) ~into =
  let database = create_in_memory ~loaded ~records_reads:false [ package ] in
  Fun.protect
    ~finally:(fun () -> Store.close database.store)
    (fun () ->
      Store.keep_for_dependents database.store ~markers:(Kind.encode_markers [ Calls ]);
      Store.save database.store ~into)

let list_package_diagnostics path package =
  let database = create ~loaded:[ path ] [] in
  Fun.protect
    ~finally:(fun () -> close database)
    (fun () -> list_dependency_diagnostics database package)

let list_differences (database : t) (other : t) =
  let path = Filename.temp_file "truss-database" ".sqlite" in
  Fun.protect
    ~finally:(fun () -> Sys.remove path)
    (fun () ->
      Store.save other.store ~into:path;
      let schema = Store.attach database.store path in
      Fun.protect
        ~finally:(fun () -> Store.detach database.store path)
        (fun () -> Store.count_differing_rows database.store ~other:schema))

let list_definitions_naming (database : t) (path : Path.t) =
  let paths =
    match path with
    | Method { owner; name; _ } | Member_constant { owner; name } ->
        List.sort_uniq Path.compare
          (path
          :: List.map
               (fun (key : Resolve.Names.key) -> key.path)
               ((make_name_lookups database).list_members owner name))
    | Top _ | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _ -> [ path ]
  in
  List.sort_uniq compare
    (List.concat_map
       (fun path ->
         let id = Ids.of_path path in
         List.map Declarations.decode_key
           (List.map
              (fun (row : Store.definition) -> row.key)
              (Store.list_definitions database.store Main (Of_path id))
           @ Store.list_definitions_naming database.store
               ~target:(Tracker.locate (Entity Definition) id "")
               ~markers:(Kind.encode_markers [ References ])))
       paths)

let list_readers_of_module (database : t) (module_ : Path.module_) =
  let edges =
    Store.list_edges_into database.store
      ~target_kinds:[ Kind.rank_target (Lookup Module) ]
      ~targets:[ Ids.of_module module_ ]
      ~markers:(Kind.encode_markers [ Reads ])
  in
  let list_units stage =
    List.filter_map
      (fun (edge : Store.read_edge) ->
        if edge.source_kind = Kind.rank_stage stage then Some edge.source else None)
      edges
  in
  ( List.sort_uniq compare
      (List.map
         (fun (_, _, key) -> Declarations.decode_key key)
         (Store.list_definitions_identified database.store ~ids:(list_units Resolve))),
    List.sort_uniq compare
      (List.filter_map
         (fun id ->
           Option.map
             (fun (row : Store.file) -> Declarations.decode_file row.key)
             (Store.find_file database.store Main ~id))
         (list_units Check_imports)) )

module Kind = Kind

module For_testing = struct
  type nonrec checker = checker =
    | Parse
    | Resolve
    | Interface
    | Infer
    | Usage
    | Ownership
    | Package_checks
    | Unexported

  let list_diagnostics = list_diagnostics

  let fragment_checkers : checker list =
    [ Parse; Resolve; Interface; Infer; Usage; Ownership; Package_checks ]

  let make_unchecked_interface_lookups database =
    Lookups.make_interface database Tracker.untracked ~is_checked:false

  let make_mir_lookups database = Lookups.make_mir database Tracker.untracked

  let read_derived_form database path =
    try Infer.derive_form (Lookups.make_infer database Tracker.untracked) path
    with Tracker.Reads_failed_fact -> None

  let read_core database path =
    Option.bind ((make_mir_lookups database).find_form_origin path)
      (fun ((origin : Interface.form_origin), substitution) ->
        Option.map
          (fun form -> (form, substitution))
          (match origin with
          | Written key | Inherited key ->
              Option.map
                (fun (checked : Infer.checked) -> checked.form)
                (read_checked_body database key)
          | Derived _ -> read_derived_form database path))

  let read_ownership (database : t) (key : Resolve.Names.key) =
    Tracker.read database Tracker.untracked Facts.ownership.whole key.module_.package
      ~id:(Ids.of_key key)

  let list_unread (database : t) =
    let list_of ?section fact =
      let ({ table; id_column; targets; read_targets } : Tracker.description) =
        Tracker.describe fact
      in
      List.map
        (fun name -> Printf.sprintf "the %s of %s" (Kind.show_fact (List.hd targets)) name)
        (Store.list_unread database.store ~table ~id_column ~section
           ~target_kinds:(List.map (fun fact -> Kind.rank_target (Fact fact)) read_targets))
    in
    List.concat
      (List.mapi
         (fun rank section -> list_of ~section:rank (Any (Facts.resolved section)))
         Resolve.sections)
    @ List.concat_map list_of
        [
          Any Facts.trait_header;
          Any Facts.elaborated;
          Any Facts.signature_check;
          Any Facts.contract;
          Any Facts.body;
          Any Facts.body_mir;
        ]

  let make_proof_lookups = make_proof_lookups

  let list_queries proofs =
    let database = proofs.database in
    let lookups = make_proof_lookups database in
    List.sort
      (fun (left, _) (right, _) -> compare (left.span, left.code) (right.span, right.code))
      (List.concat_map
         (fun (key : Resolve.Names.key) ->
           match find_proof database key with
           | Some (Value proof) ->
               List.map
                 (fun (site, input) ->
                   let shown =
                     Renderer.render
                       (make_render_lookups database (Hashtbl.create 1))
                       key (Prover site)
                   in
                   ( {
                       code = Diagnostic.Code.name shown.code;
                       span = shown.span;
                       shows = shown.message;
                     },
                     input ))
                 (Prover.For_testing.list_queries
                    (Prover.pose
                       ~runs:(Recipes.list_runs database Tracker.untracked lookups proof)
                       proof))
           | Some (Failed | Blocked) | None -> [])
         (list_proof_keys proofs))

  let find_proof proofs key = find_proof proofs.database key

  let block_proof (database : t) (key : Resolve.Names.key) =
    ignore (Tracker.write database Facts.proof ~id:(Ids.of_key key) (Some Blocked))

  let lower_roots ?on_bug (database : t) = drain_claimed_items database ?on_bug None

  let propagate ?on_bug (database : t) =
    drain database ?on_bug ~through:Prove ~scope:Everything ();
    lower_roots database ?on_bug

  type computed = { stage : Kind.stage; id : int }
  type observed = { recomputed : computed list; collected : int list }

  let observe run =
    let recomputed = ref [] and collected = ref [] in
    let result =
      Tracker.with_observer
        (function
          | Computed { stage; ids; _ } ->
              recomputed := List.map (fun id -> { stage; id }) ids @ !recomputed
          | Written { stage = Lower | Key_tests; id; is_removal = true } ->
              collected := id :: !collected
          | Written _ | Unchanged _ -> ())
        run
    in
    ( result,
      {
        recomputed = List.sort_uniq compare !recomputed;
        collected = List.sort_uniq compare !collected;
      } )

  let identify_key = Ids.of_key
  let identify_path = Ids.of_path
  let identify_file = Ids.of_file
  let identify_module = Ids.of_module
  let identify_package = Ids.of_package
  let identify_item = Ids.of_item

  let list_reads (database : t) stage id =
    List.filter_map
      (fun (edge : Store.edge) ->
        if Kind.has_marker edge.markers Reads then
          Option.map
            (fun target -> (target, edge.target.id, edge.target.name))
            (Kind.find_target edge.target.kind)
        else None)
      (Store.list_edges database.store Main ~source:(Tracker.locate_unit stage id))

  let with_failing_unit = Tracker.with_failing_unit

  let add_root (database : t) item =
    let root = Tracker.locate (Entity Item) (Ids.of_item item) "" in
    let source = Tracker.locate_unit Claim_roots 0 in
    let claimed = Store.list_edges database.store Main ~source in
    if not (List.exists (fun (edge : Store.edge) -> edge.target = root) claimed) then begin
      ignore
        (Store.replace_edges database.store ~source
           ({ Store.target = root; markers = Kind.encode_markers [ Claims ] } :: claimed));
      Recipes.ensure_item database item
    end

  let supply_lowered (database : t) item lowered =
    add_root database item;
    Recipes.supply_lowered database item lowered

  let list_differences = list_differences

  let list_items (database : t) : Lowered.Item.t list =
    List.map (fun key -> Marshal.from_string key 0) (Store.list_item_keys database.store)

  let extend_package ~loaded files =
    let database = Tracker.create (Store.copy_file loaded) ~records_reads:true in
    Store.replace_project database.store
      (List.filter_map Path.parse_package (Store.list_packages database.store Main));
    List.iter
      (fun ((file : Path.file), text) ->
        Recipes.write_file database ~package:(Path.show_package file.module_.package) file text)
      files;
    drain database ~through:last_checking_stage ~scope:Everything ();
    database
end
