module Part = Part
module Call_graph = Graph.Make (Path)

type 'a part = Value of 'a | Failed of Diagnostic.in_definition list | Blocked
type 'a slot = { stored : 'a option; replace : 'a -> unit; remove : unit -> unit }

exception Reads_failed_part

module Make_table (Key : sig
  type t
end) =
struct
  include Hashtbl.Make (Structural_key.Make (Key))

  let make_slot table key =
    {
      stored = find_opt table key;
      replace = replace table key;
      remove = (fun () -> remove table key);
    }

  let make_access select key owner = make_slot (select owner) key
  let list_keys table make_part = fold (fun key _ parts -> make_part key :: parts) table []

  let list_failures table key =
    match find_opt table key with
    | Some (Failed diagnostics) -> diagnostics
    | Some (Value _ | Blocked) | None -> []
end

module Path_table = Make_table (Path)

module Key_table = Make_table (struct
  type t = Resolve.Names.key
end)

module Key_section_table = Make_table (struct
  type t = Resolve.Names.key * Resolve.section
end)

module File_table = Make_table (struct
  type t = Path.file
end)

module Package_table = Make_table (struct
  type t = Path.package
end)

module Package_stage_table = Make_table (struct
  type t = Path.package * Stage.t
end)

module Check_table = Make_table (struct
  type t = Package_checks.check
end)

module Type_trait_table = Make_table (struct
  type t = Path.t * Path.t
end)

module Part_table = Make_table (Part)

module Computed_table = Make_table (struct
  type t = Part.computed
end)

module Stored_table = Make_table (struct
  type t = Part.stored
end)

module Instance_table = Make_table (Instance)
module References = Graph.Make (Instance)

module Entry = struct
  type t =
    | Value of Part.stored
    | Reads of Part.computed
    | Stale of Part.computed
    | Package of Path.package
    | File of Path.file
    | Owned of Part.t
end

module Entry_table = Make_table (Entry)

type parsed = { tree : Syntax.file; diagnostics : Diagnostic.t list; text : string }

type package_database = {
  name : Path.package;
  mutable dependencies : Manifest.dependency list;
  mutable modules : Path.module_ list;
  mutable files : Path.file list;
  sources : Source.t File_table.t;
  parsed : parsed File_table.t;
  mutable namespace : Resolve.Names.namespace option;
  resolved_names : Resolve.resolved part Key_section_table.t;
  grants : Interface.Environment.grant Package_table.t;
  import_checks : Diagnostic.t list File_table.t;
  trait_headers : Resolve.trait_header part Key_table.t;
  constant_values : Z.t option part Path_table.t;
  headers : Interface.Environment.header part Key_table.t;
  interfaces : Interface.Environment.elaborated_interface part Key_table.t;
  derived_interfaces : Types.impl_interface part Type_trait_table.t;
  type_facts : Interface.Environment.type_facts part Path_table.t;
  signature_checks : unit part Key_table.t;
  contracts : Core.t part Key_table.t;
  checked_bodies : Infer.checked part Key_table.t;
  body_parts : Mir.body_part part Key_table.t;
  contract_parts : Mir.contract_part part Key_table.t;
  generated_parts : (Mir.body_part * Mir.contract_part) part Path_table.t;
  mir_call_edges : Path.t list part Path_table.t;
  patterns : unit part Key_table.t;
  usage : unit part Key_table.t;
  ownership : (Core.origin * Core.origin) list part Key_table.t;
  package_checks : Package_checks.outcome part Check_table.t;
  recursion_groups : Path.t list part Path_table.t;
  proofs : Prover.proof part Key_table.t;
}

type t = {
  package_databases : package_database Package_table.t;
  mutable project : Path.package list;
  absent : package_database Package_table.t;
  reads : Part.t list Computed_table.t;
  readers : unit Computed_table.t Part_table.t;
  stale : unit Computed_table.t Package_stage_table.t;
  implied : Part.computed list Package_table.t;
  graphs : Call_graph.t Package_table.t;
  lowering : Compile.Lookups.settings option;
  lowered : (Compile.lowered, Compile.unsupported) result part Instance_table.t;
  test_keys : (string, Compile.unsupported) result part Instance_table.t;
  references : References.t;
  owners : Part.t list Instance_table.t;
  owned : Instance.key list Part_table.t;
  unsaved : unit Entry_table.t;
}

type observation =
  | Computation of { parts : Part.stored list; reads : int; distinct_reads : int }
  | Unchanged of Part.stored
  | Write of { part : Part.stored; is_removal : bool }

let observer : (observation -> unit) ref = ref ignore

let make_empty_package_database name ~dependencies =
  {
    name;
    dependencies;
    modules = [];
    files = [];
    sources = File_table.create 64;
    parsed = File_table.create 64;
    namespace = None;
    resolved_names = Key_section_table.create 1024;
    grants = Package_table.create 4;
    import_checks = File_table.create 64;
    trait_headers = Key_table.create 64;
    constant_values = Path_table.create 64;
    headers = Key_table.create 64;
    interfaces = Key_table.create 256;
    derived_interfaces = Type_trait_table.create 16;
    type_facts = Path_table.create 64;
    signature_checks = Key_table.create 256;
    contracts = Key_table.create 256;
    checked_bodies = Key_table.create 256;
    body_parts = Key_table.create 256;
    contract_parts = Key_table.create 256;
    generated_parts = Path_table.create 16;
    mir_call_edges = Path_table.create 256;
    patterns = Key_table.create 64;
    usage = Key_table.create 64;
    ownership = Key_table.create 64;
    package_checks = Check_table.create 64;
    recursion_groups = Path_table.create 64;
    proofs = Key_table.create 64;
  }

let set_files (package_database : package_database) files =
  package_database.files <- List.sort compare files;
  package_database.modules <-
    List.sort_uniq compare
      (List.map (fun (file : Path.file) -> file.module_) package_database.files)

let make_source (file : Path.file) text = Source.create ~path:(Path.show_file file) text

let make_package_database name ~dependencies (texts : (Path.file * string) list) =
  let package_database = make_empty_package_database name ~dependencies in
  List.iter
    (fun (file, text) -> File_table.replace package_database.sources file (make_source file text))
    texts;
  set_files package_database (List.map fst texts);
  package_database

let mark_unsaved database entry = Entry_table.replace database.unsaved entry ()

let is_saved_part database (part : Part.stored) =
  match part with
  | Computed (Namespace _) -> false
  | Computed (Lowering _) -> true
  | Computed part -> List.mem (Part.locate_package part) database.project
  | Recursion_group path -> List.mem (Path.locate_package path) database.project

let mark_package_database_unsaved database (package_database : package_database) =
  mark_unsaved database (Package package_database.name);
  List.iter (fun file -> mark_unsaved database (File file)) package_database.files

let mark_stale database part =
  let slot = (Part.locate_package part, Stage.of_part part) in
  let parts =
    match Package_stage_table.find_opt database.stale slot with
    | Some parts -> parts
    | None ->
        let parts = Computed_table.create 64 in
        Package_stage_table.replace database.stale slot parts;
        parts
  in
  if not (Computed_table.mem parts part) then begin
    Computed_table.replace parts part ();
    mark_unsaved database (Stale part)
  end

let is_stale database part =
  match
    Package_stage_table.find_opt database.stale (Part.locate_package part, Stage.of_part part)
  with
  | Some parts -> Computed_table.mem parts part
  | None -> false

let unmark database part =
  Option.iter
    (fun parts ->
      if Computed_table.mem parts part then begin
        Computed_table.remove parts part;
        mark_unsaved database (Stale part)
      end)
    (Package_stage_table.find_opt database.stale (Part.locate_package part, Stage.of_part part))

let list_stale_parts database package stage =
  match Package_stage_table.find_opt database.stale (package, stage) with
  | Some parts -> Computed_table.fold (fun part () parts -> part :: parts) parts []
  | None -> []

let create ?(loaded = []) ?(checks = true) (packages : Project.package list) =
  let package_databases = Package_table.create 8 in
  List.iter
    (fun package_database ->
      Package_table.replace package_databases package_database.name package_database)
    loaded;
  let database =
    {
      package_databases;
      project = List.map (fun (package : Project.package) -> package.name) packages;
      absent = Package_table.create 4;
      reads = Computed_table.create 4096;
      readers = Part_table.create 4096;
      stale = Package_stage_table.create 64;
      implied = Package_table.create 8;
      graphs = Package_table.create 8;
      lowering = Option.map (fun system -> { Compile.Lookups.checks; system }) Libc.host;
      lowered = Instance_table.create 1024;
      test_keys = Instance_table.create 1024;
      references = References.create ~tracks_blocked:false;
      owners = Instance_table.create 64;
      owned = Part_table.create 64;
      unsaved = Entry_table.create 4096;
    }
  in
  List.iter
    (fun (package : Project.package) ->
      let package_database =
        make_package_database package.name ~dependencies:package.dependencies package.files
      in
      Package_table.replace package_databases package.name package_database;
      mark_package_database_unsaved database package_database;
      List.iter (fun file -> mark_stale database (Parsed file)) package_database.files;
      mark_stale database (Namespace package.name))
    packages;
  database

let copy_package_database (package_database : package_database) =
  {
    name = package_database.name;
    dependencies = package_database.dependencies;
    modules = package_database.modules;
    files = package_database.files;
    sources = File_table.copy package_database.sources;
    parsed = File_table.copy package_database.parsed;
    namespace = package_database.namespace;
    resolved_names = Key_section_table.copy package_database.resolved_names;
    grants = Package_table.copy package_database.grants;
    import_checks = File_table.copy package_database.import_checks;
    trait_headers = Key_table.copy package_database.trait_headers;
    constant_values = Path_table.copy package_database.constant_values;
    headers = Key_table.copy package_database.headers;
    interfaces = Key_table.copy package_database.interfaces;
    derived_interfaces = Type_trait_table.copy package_database.derived_interfaces;
    type_facts = Path_table.copy package_database.type_facts;
    signature_checks = Key_table.copy package_database.signature_checks;
    contracts = Key_table.copy package_database.contracts;
    checked_bodies = Key_table.copy package_database.checked_bodies;
    body_parts = Key_table.copy package_database.body_parts;
    contract_parts = Key_table.copy package_database.contract_parts;
    generated_parts = Path_table.copy package_database.generated_parts;
    mir_call_edges = Path_table.copy package_database.mir_call_edges;
    patterns = Key_table.copy package_database.patterns;
    usage = Key_table.copy package_database.usage;
    ownership = Key_table.copy package_database.ownership;
    package_checks = Check_table.copy package_database.package_checks;
    recursion_groups = Path_table.copy package_database.recursion_groups;
    proofs = Key_table.copy package_database.proofs;
  }

let copy database =
  let package_databases = Package_table.copy database.package_databases in
  Package_table.filter_map_inplace
    (fun name package_database ->
      Some
        (if List.mem name database.project then copy_package_database package_database
         else package_database))
    package_databases;
  let readers = Part_table.copy database.readers in
  Part_table.filter_map_inplace (fun _ parts -> Some (Computed_table.copy parts)) readers;
  let stale = Package_stage_table.copy database.stale in
  Package_stage_table.filter_map_inplace (fun _ parts -> Some (Computed_table.copy parts)) stale;
  let graphs = Package_table.copy database.graphs in
  Package_table.filter_map_inplace (fun _ graph -> Some (Call_graph.copy graph)) graphs;
  {
    package_databases;
    project = database.project;
    absent = Package_table.copy database.absent;
    reads = Computed_table.copy database.reads;
    readers;
    stale;
    implied = Package_table.copy database.implied;
    graphs;
    lowering = database.lowering;
    lowered = Instance_table.copy database.lowered;
    test_keys = Instance_table.copy database.test_keys;
    references = References.copy database.references;
    owners = Instance_table.copy database.owners;
    owned = Part_table.copy database.owned;
    unsaved = Entry_table.create 64;
  }

let add_reads database part read_parts =
  Computed_table.replace database.reads part read_parts;
  List.iter
    (fun read ->
      let readers =
        match Part_table.find_opt database.readers read with
        | Some readers -> readers
        | None ->
            let readers = Computed_table.create 4 in
            Part_table.replace database.readers read readers;
            readers
      in
      Computed_table.replace readers part ())
    read_parts

let record database parts reads =
  let read_parts =
    Part_table.fold
      (fun (read : Part.t) () read_parts ->
        match read with
        | Stored (Computed read) when List.mem read parts -> read_parts
        | _ -> read :: read_parts)
      reads []
  in
  List.iter
    (fun part ->
      let before = Computed_table.find_opt database.reads part in
      let is_unchanged =
        match before with
        | Some before ->
            List.length before = List.length read_parts
            && List.for_all (Part_table.mem reads) before
        | None -> false
      in
      if not is_unchanged then mark_unsaved database (Reads part);
      Option.iter
        (List.iter (fun read ->
             Option.iter
               (fun readers -> Computed_table.remove readers part)
               (Part_table.find_opt database.readers read)))
        before;
      add_reads database part read_parts)
    parts

let compute_and_record database parts compute =
  let reads = Part_table.create 16 in
  let read_count = ref 0 in
  let result =
    compute (fun part ->
        incr read_count;
        Part_table.replace reads part ())
  in
  record database parts reads;
  !observer
    (Computation
       {
         parts = List.map (fun part -> Part.Computed part) parts;
         reads = !read_count;
         distinct_reads = Part_table.length reads;
       });
  result

let mark_readers ?(is_selected = fun _ -> true) database part =
  Option.iter
    (Computed_table.iter (fun reader () -> if is_selected reader then mark_stale database reader))
    (Part_table.find_opt database.readers part)

let mark_written database (part : Part.stored) ~is_removal =
  !observer (Write { part; is_removal });
  if is_saved_part database part then mark_unsaved database (Value part);
  mark_readers database (Stored part)

let store database part slot value =
  if slot.stored = value then !observer (Unchanged part)
  else begin
    (match value with Some value -> slot.replace value | None -> slot.remove ());
    mark_written database part ~is_removal:(Option.is_none value)
  end

let compute_into database part slot compute =
  store database (Computed part) slot (compute_and_record database [ part ] compute)

let obtain_owner database package =
  match Package_table.find_opt database.package_databases package with
  | Some package_database -> package_database
  | None -> (
      match Package_table.find_opt database.absent package with
      | Some package_database -> package_database
      | None ->
          let package_database = make_empty_package_database package ~dependencies:[] in
          package_database.namespace <- Some Resolve.Names.empty_namespace;
          Package_table.replace database.absent package package_database;
          package_database)

let obtain_call_graph database package =
  match Package_table.find_opt database.graphs package with
  | Some graph -> graph
  | None ->
      let graph = Call_graph.create ~tracks_blocked:true in
      Package_table.replace database.graphs package graph;
      graph

let report_uncomputed part =
  Compiler_bug.raise_bug ~stage:"Database" "%s is not computed" (Part.show_computed part)

let read database note part =
  note (Part.Stored (Computed part));
  if is_stale database part then
    Compiler_bug.raise_bug ~stage:"Database" "%s is read while it is stale"
      (Part.show_computed part)

let read_part database note part_of select (key : Resolve.Names.key) =
  let part = part_of key in
  read database note part;
  match Key_table.find_opt (select (obtain_owner database key.module_.package)) key with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> report_uncomputed part

let make_part compute argument =
  match compute argument with value -> Value value | exception Reads_failed_part -> Blocked

let make_checked_part check key =
  match check key with
  | [], value -> Value value
  | diagnostics, _ -> Failed diagnostics
  | exception Reads_failed_part -> Blocked

let require_value = function Value value -> value | Failed _ | Blocked -> raise Reads_failed_part
let find_package database name = Package_table.find_opt database.package_databases name

let list_dependency_names database name =
  match find_package database name with
  | Some package ->
      List.map (fun (dependency : Manifest.dependency) -> dependency.package) package.dependencies
  | None -> []

let list_modules database name =
  match find_package database name with Some package -> package.modules | None -> []

let read_source database (file : Path.file) =
  match File_table.find_opt (obtain_owner database file.module_.package).sources file with
  | Some source -> source
  | None ->
      Compiler_bug.raise_bug ~stage:"Database" "%s is not a file of the build" (Path.show_file file)

let sort_in_dependency_order database packages =
  let seen = Package_table.create 8 in
  let order = ref [] in
  let rec visit package =
    if not (Package_table.mem seen package) then begin
      Package_table.replace seen package ();
      List.iter visit (List.sort Path.compare_package (list_dependency_names database package));
      order := package :: !order
    end
  in
  visit Path.standard_package;
  List.iter visit packages;
  List.rev !order

let read_namespace database package =
  match (obtain_owner database package).namespace with
  | Some namespace -> namespace
  | None -> report_uncomputed (Namespace package)

let make_name_lookups_over database ~read_namespace =
  Resolve.Names.of_namespaces ~read_namespace
    ~module_exists:(fun (module_ : Path.module_) ->
      module_ = Intrinsic.module_ || List.mem module_ (list_modules database module_.package))
    ~split_module:
      (Path.split_module ~is_package:(fun name -> Option.is_some (find_package database name)))
    ~list_dependency_names:(list_dependency_names database)

let make_stored_name_lookups database =
  make_name_lookups_over database ~read_namespace:(read_namespace database)

let add_recording (names : Resolve.Names.lookups) (note : Part.t -> unit) : Resolve.Names.lookups =
  let note_name_read (part : Part.name) read =
    note (Name part);
    read
  in
  let note_input_read (part : Part.input) read =
    note (Input part);
    read
  in
  {
    find = (fun module_ name -> note_name_read (Entry (module_, name)) (names.find module_ name));
    list_entries = (fun module_ -> note_name_read (Entries module_) (names.list_entries module_));
    list_imports = (fun key -> note_name_read (Imports key) (names.list_imports key));
    module_exists =
      (fun module_ -> note_input_read (Modules module_.package) (names.module_exists module_));
    split_module = (fun parts -> note_input_read Packages (names.split_module parts));
    list_dependency_names =
      (fun package -> note_input_read (Dependencies package) (names.list_dependency_names package));
    find_key =
      (fun path ->
        (match path with
        | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ }
          ->
            note (Name (Declaration { module_; path; ordinal = 0 }))
        | Method { owner; name; _ } | Member_constant { owner; name } ->
            note (Name (Members (owner, name)))
        | Derived _ | Unresolved _ -> ());
        names.find_key path);
    read_declaration = (fun key -> note_name_read (Declaration key) (names.read_declaration key));
    list_declarations =
      (fun module_ ->
        note_name_read (Module_declarations module_) (names.list_declarations module_));
    list_declarations_in =
      (fun file -> note_name_read (File_declarations file) (names.list_declarations_in file));
    list_package_declarations =
      (fun package ->
        note_name_read (Package_declarations package) (names.list_package_declarations package));
    read_definition = (fun key -> note_name_read (Tree key) (names.read_definition key));
    read_text = (fun key -> note_name_read (Text key) (names.read_text key));
    read_spans = (fun key -> note_name_read (Tree key) (names.read_spans key));
    list_recovered = (fun key -> note_name_read (Tree key) (names.list_recovered key));
    read_place = (fun key -> note_name_read (Place key) (names.read_place key));
    find_container = (fun key -> note_name_read (Container key) (names.find_container key));
    list_contained = (fun key -> note_name_read (Contained key) (names.list_contained key));
    list_members =
      (fun owner name -> note_name_read (Members (owner, name)) (names.list_members owner name));
    list_traits_declaring =
      (fun package name ->
        note_name_read (Traits_declaring (package, name)) (names.list_traits_declaring package name));
    list_impls = (fun package -> note_name_read (Impl_index package) (names.list_impls package));
    list_impls_of_type =
      (fun package type_ ->
        note_name_read (Impls_of_type (package, type_)) (names.list_impls_of_type package type_));
    list_impls_of_trait =
      (fun package trait ->
        note_name_read (Impls_of_trait (package, trait)) (names.list_impls_of_trait package trait));
    list_law_proofs =
      (fun package name ->
        note_name_read (Law_proofs (package, name)) (names.list_law_proofs package name));
  }

let make_recording_name_lookups database note =
  add_recording (make_stored_name_lookups database) note

let read_parsed_file database (file : Path.file) =
  match File_table.find_opt (obtain_owner database file.module_.package).parsed file with
  | Some parsed -> parsed
  | None -> report_uncomputed (Parsed file)

let make_namespace database note (package_database : package_database) =
  note (Part.Input (Modules package_database.name));
  Resolve.Names.build_namespace
    (make_recording_name_lookups database note)
    package_database.name
    (List.map
       (fun module_ ->
         ( module_,
           List.filter_map
             (fun (file : Path.file) ->
               if file.module_ = module_ then begin
                 read database note (Parsed file);
                 let parsed = read_parsed_file database file in
                 Some (file, parsed.tree, parsed.text)
               end
               else None)
             package_database.files ))
       package_database.modules)

let list_file_keys database file =
  List.map Resolve.Names.make_key ((make_stored_name_lookups database).list_declarations_in file)

let read_resolution_part database note section (key : Resolve.Names.key) =
  read database note (Resolved (key, section));
  match
    Key_section_table.find_opt (obtain_owner database key.module_.package).resolved_names
      (key, section)
  with
  | Some part -> part
  | None -> report_uncomputed (Resolved (key, section))

let read_resolution database note section key =
  require_value (read_resolution_part database note section key)

let read_whole_resolution database note key =
  Resolve.merge
    (List.map (fun section -> read_resolution database note section key) Resolve.sections)

let read_elaborated_interface database note ~is_checked (key : Resolve.Names.key) =
  let owner = obtain_owner database key.module_.package in
  read database note (Interface key);
  if is_checked then begin
    read database note (Signature_check key);
    match Key_table.find_opt owner.signature_checks key with
    | Some (Failed _ | Blocked) -> raise Reads_failed_part
    | Some (Value ()) -> ()
    | None -> report_uncomputed (Signature_check key)
  end;
  match Key_table.find_opt owner.interfaces key with
  | Some part -> require_value part
  | None -> report_uncomputed (Interface key)

let make_recording_interface_lookups database note ~is_checked : Interface.Lookups.t =
  let names = make_recording_name_lookups database note in
  let read_elaborated_interface = read_elaborated_interface database note ~is_checked in
  {
    names;
    read_resolved = read_resolution database note;
    find_trait_header =
      (fun path ->
        Option.bind (names.find_key path) (fun key ->
            read database note (Trait_header key);
            Option.map require_value
              (Key_table.find_opt (obtain_owner database key.module_.package).trait_headers key)));
    find_constant_value =
      (fun path ->
        read database note (Constant_value path);
        Option.bind
          (Path_table.find_opt (obtain_owner database (Path.locate_package path)).constant_values
             path)
          require_value);
    find_header =
      (fun key ->
        read database note (Header key);
        Option.map require_value
          (Key_table.find_opt (obtain_owner database key.module_.package).headers key));
    read_elaborated_interface;
    find_derived_interface =
      (fun ~type_ ~trait ->
        Option.iter (fun key -> ignore (read_elaborated_interface key)) (names.find_key type_);
        read database note (Derived_interface { type_; trait });
        Option.map require_value
          (Type_trait_table.find_opt
             (obtain_owner database (Path.locate_package type_)).derived_interfaces (type_, trait)));
    find_type_facts =
      (fun path ->
        read database note (Type_facts path);
        Option.map require_value
          (Path_table.find_opt (obtain_owner database (Path.locate_package path)).type_facts path));
    find_grant =
      (fun package dependency ->
        read database note (Grant (package, dependency));
        Package_table.find_opt (obtain_owner database package).grants dependency);
  }

let make_interface_part (elaborated : Interface.Environment.elaborated_interface) =
  match (elaborated.diagnostics, elaborated.interface) with
  | [], Error_interface _ -> Blocked
  | [], _ -> Value elaborated
  | diagnostics, _ -> Failed diagnostics

let find_type_interface lookups path =
  match make_part (Interface.Definition.read_type_interface lookups) path with
  | Value interface -> interface
  | Failed _ | Blocked -> None

let list_derived_methods (names : Resolve.Names.lookups) package =
  List.concat_map
    (fun (((trait : Path.t), _), (impl : Path.t)) ->
      match (impl, names.find_key trait) with
      | Derived _, Some trait_key ->
          List.filter_map
            (fun (member : Resolve.Names.key) ->
              match member.path with
              | Method { name; receiver; _ } -> Some (Path.Method { owner = impl; name; receiver })
              | _ -> None)
            (names.list_contained trait_key)
      | _ -> [])
    (names.list_impls package)

let list_package_parts database (names : Resolve.Names.lookups) package : Part.computed list =
  let package_database = obtain_owner database package in
  let declarations = names.list_package_declarations package in
  let paths =
    List.map (fun (declaration : Resolve.Names.declaration) -> declaration.path) declarations
  in
  let of_declaration (declaration : Resolve.Names.declaration) : Part.computed list =
    let key = Resolve.Names.make_key declaration in
    List.map (fun section -> Part.Resolved (key, section)) Resolve.sections
    @ [
        Part.Interface key;
        Signature_check key;
        Contract key;
        Checked_body key;
        Body_mir key;
        Contract_mir key;
        Patterns key;
        Usage key;
        Ownership key;
        Proof key;
      ]
    @ (match declaration.kind with
      | Trait -> [ Part.Trait_header key; Header key ]
      | Impl | Capability -> [ Part.Header key ]
      | _ -> [])
    @
    match declaration.kind with
    | (Constant | Member_constant) when declaration.ordinal = 0 -> [ Part.Constant_value key.path ]
    | Type when declaration.ordinal = 0 -> [ Part.Type_facts key.path ]
    | _ -> []
  in
  List.concat_map of_declaration declarations
  @ List.filter_map
      (function
        | _, Path.Derived { type_; trait } -> Some (Part.Derived_interface { type_; trait })
        | _ -> None)
      (names.list_impls package)
  @ List.map (fun path -> Part.Generated_mir path) (list_derived_methods names package)
  @ List.concat_map
      (fun path -> [ Part.Mir_call_edges path; Call_edges (path, package) ])
      (List.sort_uniq Path.compare paths)
  @ List.map
      (fun dependency -> Part.Grant (package, dependency))
      (List.sort_uniq Path.compare_package (names.list_dependency_names package))
  @ List.map (fun file -> Part.Import_check file) package_database.files
  @ List.map
      (fun check -> Part.Package_check (package, check))
      (Package_checks.list_checks declarations)

let read_checked database note key =
  read_part database note (fun key -> Part.Checked_body key) (fun owner -> owner.checked_bodies) key

let read_checked_form database note key = (read_checked database note key).form

let make_recording_infer_lookups database note : Infer.Lookups.t =
  {
    interface = make_recording_interface_lookups database note ~is_checked:true;
    read_contract =
      read_part database note (fun key -> Part.Contract key) (fun owner -> owner.contracts);
  }

let type_check run lookups key =
  match run lookups key with
  | Ok checked -> Value checked
  | Error [] -> Blocked
  | Error diagnostics -> Failed diagnostics
  | exception Reads_failed_part -> Blocked

let make_form_origin database note =
  Infer.find_form_origin (make_recording_interface_lookups database note ~is_checked:true)
    ~is_derived:(fun path ->
      read database note (Generated_mir path);
      Path_table.mem (obtain_owner database (Path.locate_package path)).generated_parts path)

let read_body_mir database note =
  read_part database note (fun key -> Part.Body_mir key) (fun owner -> owner.body_parts)

let make_recording_mir_lookups database note : Mir.lookups =
  {
    find_form_origin = make_form_origin database note;
    read_body_part = read_body_mir database note;
    read_contract_part =
      read_part database note (fun key -> Part.Contract_mir key) (fun owner -> owner.contract_parts);
    read_generated_parts =
      (fun path ->
        read database note (Generated_mir path);
        match
          Path_table.find_opt (obtain_owner database (Path.locate_package path)).generated_parts
            path
        with
        | Some (Value parts) -> parts
        | Some (Failed _ | Blocked) -> raise Reads_failed_part
        | None -> report_uncomputed (Generated_mir path));
  }

let make_recording_call_edge_lookups database note : Mir.Call_edges.lookups =
  {
    interface = make_recording_interface_lookups database note ~is_checked:true;
    mir = make_recording_mir_lookups database note;
  }

let read_mir_call_edges database note path =
  read database note (Mir_call_edges path);
  match
    Path_table.find_opt (obtain_owner database (Path.locate_package path)).mir_call_edges path
  with
  | Some part -> part
  | None -> Blocked

let make_recording_patterns_lookups database note : Patterns.Lookups.t =
  {
    read_core = read_checked_form database note;
    interface = make_recording_interface_lookups database note ~is_checked:true;
  }

let make_recording_usage_lookups database note : Usage.Lookups.t =
  {
    names = make_recording_name_lookups database note;
    read_resolved = read_whole_resolution database note;
    read_tables = (fun key -> (read_checked database note key).tables);
  }

let make_recording_ownership_lookups database note : Ownership.Lookups.t =
  {
    find_graph = (fun key -> Mir.find_graph (read_body_mir database note key));
    interface = make_recording_interface_lookups database note ~is_checked:true;
  }

let make_recording_package_checks_lookups database note : Package_checks.Lookups.t =
  {
    interface = make_recording_interface_lookups database note ~is_checked:true;
    read_core = read_checked_form database note;
    list_used_packages = (fun key -> (read_checked database note key).used_packages);
  }

let find_used_imports database note file =
  note (Part.Name (File_declarations file));
  let used =
    List.concat_map
      (fun key ->
        List.map
          (fun section ->
            match read_resolution_part database note section key with
            | Value resolved -> Some resolved.used_imports
            | Failed _ | Blocked -> None)
          Resolve.sections)
      (list_file_keys database file)
  in
  if List.for_all Option.is_some used then Some (List.concat_map Option.get used) else None

let list_import_diagnostics database note (file : Path.file) =
  read database note (Parsed file);
  note (Part.Input (Source file));
  Resolve.list_file_diagnostics
    (make_recording_name_lookups database note)
    file (read_parsed_file database file).tree
    ~text:(Source.text (read_source database file))
    ~used:(find_used_imports database note file)

let find_call_edges database note ~viewer path =
  match read_mir_call_edges database note path with
  | Failed _ | Blocked -> None
  | Value mir_call_edges -> (
      match
        Mir.Call_edges.list_implementations
          (make_recording_call_edge_lookups database note)
          ~viewer path
      with
      | implementations -> Some (List.sort_uniq Path.compare (mir_call_edges @ implementations))
      | exception Reads_failed_part -> None)

let read_recursion_group database note path =
  note (Part.Stored (Recursion_group path));
  match
    Path_table.find_opt (obtain_owner database (Path.locate_package path)).recursion_groups path
  with
  | Some (Value members) -> members
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> []

let make_recording_proof_lookups database note : Prover.Lookups.t =
  {
    read_source =
      (fun file ->
        note (Part.Input (Source file));
        read_source database file);
    interface = make_recording_interface_lookups database note ~is_checked:true;
    mir = make_recording_mir_lookups database note;
    read_patterns =
      read_part database note (fun key -> Part.Patterns key) (fun owner -> owner.patterns);
    list_must_be_disjoint =
      read_part database note (fun key -> Part.Ownership key) (fun owner -> owner.ownership);
    list_recursion_group = read_recursion_group database note;
  }

let make_recording_lowering_lookups database note : Compile.Lookups.t =
  {
    interface = make_recording_interface_lookups database note ~is_checked:true;
    mir = make_recording_mir_lookups database note;
  }

let read_instance_part database note table part instance =
  read database note (Lowering part);
  match Instance_table.find_opt table instance with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> report_uncomputed (Lowering part)

let read_lowered database note key =
  read_instance_part database note database.lowered (Lowered key) key

let read_test_key database note key =
  read_instance_part database note database.test_keys (Test_key key) key

exception Reaches_unsupported of Compile.unsupported

let compute_test_keys database keys =
  let outcome =
    compute_and_record database
      (List.map (fun key -> Part.Lowering (Test_key key)) keys)
      (fun note ->
        let require_supported = function
          | Ok value -> value
          | Error unsupported -> raise (Reaches_unsupported unsupported)
        in
        match
          Compile.derive_test_keys
            ~read_lowered:(fun key -> require_supported (read_lowered database note key))
            ~read_known_key:(fun key -> require_supported (read_test_key database note key))
            keys
        with
        | test_keys -> Value (Ok test_keys)
        | exception Reaches_unsupported unsupported -> Value (Error unsupported)
        | exception Reads_failed_part -> Blocked)
  in
  List.iter
    (fun key ->
      let part = Part.Lowering (Test_key key) in
      store database (Computed part)
        (Instance_table.make_slot database.test_keys key)
        (Some
           (match outcome with
           | Value (Ok test_keys) -> Value (Ok (List.assoc key test_keys))
           | Value (Error unsupported) -> Value (Error unsupported)
           | Failed _ | Blocked -> Blocked)))
    keys

type stored = {
  has_value : bool;
  is_failed : bool;
  remove : unit -> unit;
  is_equal_in : t -> bool;
  marshal : unit -> string option;
  restore : string -> unit;
}

let marshal value = Marshal.to_string value []

let make_stored database (part : Part.stored) =
  let package =
    match part with
    | Computed part -> Part.locate_package part
    | Recursion_group path -> Path.locate_package path
  in
  let package_database = obtain_owner database package in
  let is_failed = function Failed _ -> true | Value _ | Blocked -> false in
  let is_never _ = false in
  let make_stored_in_owner ~is_failed ~select_owner access =
    let current = select_owner database in
    {
      has_value = Option.is_some (access current).stored;
      is_failed = Option.fold ~none:false ~some:is_failed (access current).stored;
      remove = (fun () -> (access current).remove ());
      is_equal_in =
        (fun other -> compare (access (select_owner other)).stored (access current).stored = 0);
      marshal = (fun () -> Option.map marshal (access current).stored);
      restore = (fun bytes -> (access current).replace (Marshal.from_string bytes 0));
    }
  in
  let make_keyed_stored ~is_failed access =
    make_stored_in_owner ~is_failed
      ~select_owner:(fun database -> obtain_owner database package)
      access
  in
  let of_database access = make_stored_in_owner ~is_failed ~select_owner:Fun.id access in
  match part with
  | Recursion_group path ->
      make_keyed_stored ~is_failed
        (Path_table.make_access (fun package_database -> package_database.recursion_groups) path)
  | Computed part -> (
      match part with
      | Parsed file ->
          make_keyed_stored ~is_failed:is_never
            (File_table.make_access (fun package_database -> package_database.parsed) file)
      | Namespace _ ->
          {
            has_value = Option.is_some package_database.namespace;
            is_failed = false;
            remove = (fun () -> package_database.namespace <- None);
            is_equal_in =
              (fun other ->
                compare (obtain_owner other package).namespace package_database.namespace = 0);
            marshal = (fun () -> None);
            restore = ignore;
          }
      | Resolved (key, section) ->
          make_keyed_stored ~is_failed
            (Key_section_table.make_access
               (fun package_database -> package_database.resolved_names)
               (key, section))
      | Grant (_, dependency) ->
          make_keyed_stored ~is_failed:is_never
            (Package_table.make_access (fun package_database -> package_database.grants) dependency)
      | Import_check file ->
          make_keyed_stored ~is_failed:is_never
            (File_table.make_access (fun package_database -> package_database.import_checks) file)
      | Trait_header key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.trait_headers) key)
      | Constant_value path ->
          make_keyed_stored ~is_failed
            (Path_table.make_access (fun package_database -> package_database.constant_values) path)
      | Header key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.headers) key)
      | Interface key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.interfaces) key)
      | Derived_interface { type_; trait } ->
          make_keyed_stored ~is_failed
            (Type_trait_table.make_access
               (fun package_database -> package_database.derived_interfaces)
               (type_, trait))
      | Type_facts path ->
          make_keyed_stored ~is_failed
            (Path_table.make_access (fun package_database -> package_database.type_facts) path)
      | Signature_check key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.signature_checks) key)
      | Contract key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.contracts) key)
      | Checked_body key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.checked_bodies) key)
      | Body_mir key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.body_parts) key)
      | Contract_mir key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.contract_parts) key)
      | Generated_mir path ->
          make_keyed_stored ~is_failed
            (Path_table.make_access (fun package_database -> package_database.generated_parts) path)
      | Mir_call_edges path ->
          make_keyed_stored ~is_failed
            (Path_table.make_access (fun package_database -> package_database.mir_call_edges) path)
      | Patterns key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.patterns) key)
      | Usage key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.usage) key)
      | Ownership key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.ownership) key)
      | Package_check (_, check) ->
          make_keyed_stored ~is_failed
            (Check_table.make_access
               (fun package_database -> package_database.package_checks)
               check)
      | Call_edges (path, viewer) ->
          let find_viewer_successors database =
            Option.bind (Package_table.find_opt database.graphs viewer) (fun graph ->
                Call_graph.find_successors graph path)
          in
          {
            has_value = Option.is_some (find_viewer_successors database);
            is_failed = false;
            remove =
              (fun () -> Call_graph.remove_successors (obtain_call_graph database viewer) path);
            is_equal_in =
              (fun other -> find_viewer_successors other = find_viewer_successors database);
            marshal = (fun () -> Option.map marshal (find_viewer_successors database));
            restore =
              (fun bytes ->
                ignore
                  (Call_graph.set_successors
                     (obtain_call_graph database viewer)
                     path (Marshal.from_string bytes 0)));
          }
      | Proof key ->
          make_keyed_stored ~is_failed
            (Key_table.make_access (fun package_database -> package_database.proofs) key)
      | Lowering (Lowered key) ->
          of_database (Instance_table.make_access (fun database -> database.lowered) key)
      | Lowering (Test_key key) ->
          of_database (Instance_table.make_access (fun database -> database.test_keys) key))

let discard database part =
  unmark database part;
  record database [ part ] (Part_table.create 0);
  Computed_table.remove database.reads part;
  mark_unsaved database (Reads part)

let list_instance_parts key : Part.lowering list = [ Lowered key; Test_key key ]

let is_stored database (part : Part.lowering) =
  match part with
  | Lowered key -> Instance_table.mem database.lowered key
  | Test_key key -> Instance_table.mem database.test_keys key

let is_created database part = is_stale database (Lowering part) || is_stored database part
let is_current database part = (not (is_stale database (Lowering part))) && is_stored database part

let create_instance database key =
  List.iter
    (fun part -> if not (is_created database part) then mark_stale database (Lowering part))
    (list_instance_parts key)

let rec subtract_sorted compare left right =
  match (left, right) with
  | [], _ -> []
  | left, [] -> left
  | item :: rest, other :: others ->
      let order = compare item other in
      if order = 0 then subtract_sorted compare rest others
      else if order < 0 then item :: subtract_sorted compare rest right
      else subtract_sorted compare left others

let rec forget database parts =
  List.iter
    (fun part ->
      let stored = make_stored database (Computed part) in
      if stored.has_value then begin
        stored.remove ();
        mark_written database (Computed part) ~is_removal:true
      end)
    parts;
  List.iter (discard database) parts;
  List.iter
    (function
      | Part.Proof _ as owner -> own_roots database (Part.Stored (Computed owner)) [] | _ -> ())
    parts

and own_roots database owner roots =
  let before = Option.value (Part_table.find_opt database.owned owner) ~default:[] in
  let roots = List.sort_uniq Instance.compare roots in
  if roots <> before then begin
    if roots = [] then Part_table.remove database.owned owner
    else Part_table.replace database.owned owner roots;
    mark_unsaved database (Owned owner);
    let list_owners root =
      Option.value (Instance_table.find_opt database.owners root) ~default:[]
    in
    List.iter
      (fun root ->
        match List.filter (fun other -> other <> owner) (list_owners root) with
        | [] ->
            Instance_table.remove database.owners root;
            References.remove_root database.references root
        | others -> Instance_table.replace database.owners root others)
      (subtract_sorted Instance.compare before roots);
    List.iter
      (fun root ->
        Instance_table.replace database.owners root (owner :: list_owners root);
        if References.add_root database.references root then create_instance database root)
      (subtract_sorted Instance.compare roots before);
    settle_references database
  end

and settle_references database =
  if References.has_changes database.references then
    collect database (References.update database.references).removed

and collect database keys =
  forget database
    (List.map (fun part -> Part.Lowering part) (List.concat_map list_instance_parts keys))

let list_lowered_references database key =
  match Instance_table.find_opt database.lowered key with
  | Some (Value (Ok lowered)) -> Compile.list_references lowered
  | Some (Value (Error _) | Failed _ | Blocked) | None -> []

let list_instance_edges database key =
  List.sort_uniq Instance.compare (list_lowered_references database key)

let update_references database key =
  let edges = list_instance_edges database key in
  if References.find_successors database.references key <> Some (Some edges) then begin
    List.iter (create_instance database)
      (References.set_successors database.references key (Some edges));
    settle_references database
  end

let list_current_edges database key =
  if is_stale database (Lowering (Lowered key)) then [] else list_lowered_references database key

let collect_ready_instances database =
  let ready = Instance_table.create 1024 in
  let pending = Queue.create () in
  let reach key =
    if not (Instance_table.mem ready key) then begin
      Instance_table.replace ready key ();
      Queue.add key pending
    end
  in
  let is_current_owner (owner : Part.t) =
    match owner with
    | Stored (Computed owner) -> not (is_stale database owner)
    | Input _ | Name _ | Stored (Recursion_group _) -> true
  in
  Instance_table.iter
    (fun root owners -> if List.exists is_current_owner owners then reach root)
    database.owners;
  while not (Queue.is_empty pending) do
    List.iter reach (list_current_edges database (Queue.pop pending))
  done;
  ready

let is_drained ~ready (part : Part.computed) =
  match part with
  | Lowering (Lowered key | Test_key key) -> Instance_table.mem (Lazy.force ready) key
  | _ -> true

let read_lowering_settings database =
  match database.lowering with
  | Some settings -> settings
  | None -> Compiler_bug.raise_bug ~stage:"Database" "this host has no lowering settings"

let list_proof_template_checks database (key : Resolve.Names.key) =
  match Key_table.find_opt (obtain_owner database key.module_.package).proofs key with
  | Some (Value (Obligations { obligations; _ })) ->
      List.filter_map
        (fun (obligation : Prover.State.obligation) ->
          Option.map
            (fun (template_clause : Prover.State.template_clause) -> template_clause.check)
            obligation.template_clause)
        obligations
  | Some (Value (Unsupported _ | Not_proven_here) | Failed _ | Blocked) -> []
  | None -> report_uncomputed (Proof key)

let make_template_check_root ({ from_template; literals; clauses } : Prover.State.template_check) =
  Instance.Template_check { from_template; literals; clauses }

let own_template_checks database (key : Resolve.Names.key) =
  if Option.is_some database.lowering then
    own_roots database (Stored (Computed (Proof key)))
      (List.map make_template_check_root (list_proof_template_checks database key))

let find_entry_point (names : Resolve.Names.lookups) package =
  List.find_map
    (fun (declaration : Resolve.Names.declaration) ->
      match declaration.path with
      | Top { name = "main"; _ } when declaration.kind = Function && declaration.ordinal = 0 ->
          Some declaration.path
      | _ -> None)
    (names.list_declarations { package; modules = [] })

let own_lowering_roots database (names : Resolve.Names.lookups) package =
  if Option.is_some database.lowering then
    own_roots database (Stored (Computed (Namespace package)))
      (Compile.list_roots
         ~tests:
           (List.filter_map
              (fun (declaration : Resolve.Names.declaration) ->
                match declaration.path with Test _ -> Some declaration.path | _ -> None)
              (names.list_package_declarations package))
         ~mains:(Option.to_list (find_entry_point names package)))

let holds_position database (part : Part.computed) =
  match part with
  | Proof _ | Package_check _ | Lowering (Lowered _) -> true
  | _ -> (make_stored database (Computed part)).is_failed

let mark_change database package (change : Resolve.Names.change) =
  let part : Part.name =
    match change with
    | Entry (module_, name) -> Entry (module_, name)
    | Entries module_ -> Entries module_
    | Imports key -> Imports key
    | Declaration key -> Declaration key
    | Tree key | Positions key -> Tree key
    | Text key -> Text key
    | Place key -> Place key
    | Container key -> Container key
    | Contained key -> Contained key
    | Module_declarations module_ -> Module_declarations module_
    | File_declarations file -> File_declarations file
    | Package_declarations -> Package_declarations package
    | Members (owner, name) -> Members (owner, name)
    | Traits_declaring name -> Traits_declaring (package, name)
    | Impl_index -> Impl_index package
    | Impls_of_type type_ -> Impls_of_type (package, type_)
    | Impls_of_trait trait -> Impls_of_trait (package, trait)
    | Law_proofs name -> Law_proofs (package, name)
  in
  match change with
  | Positions _ -> mark_readers ~is_selected:(holds_position database) database (Name part)
  | _ -> mark_readers database (Name part)

let write_namespace_changes database package = function
  | [] -> !observer (Unchanged (Computed (Namespace package)))
  | changes ->
      mark_written database (Computed (Namespace package)) ~is_removal:false;
      List.iter (mark_change database package) changes

let is_own_namespace_part package (part : Part.t) =
  match part with
  | Name part -> Part.locate_name_package part = package
  | Stored (Computed (Namespace namespace_package)) -> namespace_package = package
  | Input _ | Stored _ -> false

let compute_namespace_and_implied database (package_database : package_database) =
  let package = package_database.name in
  let namespace, implied =
    compute_and_record database [ Part.Namespace package ] (fun note ->
        let note part = if not (is_own_namespace_part package part) then note part in
        let own_namespace = make_namespace database note package_database in
        let names =
          make_name_lookups_over database ~read_namespace:(fun name ->
              if name = package then own_namespace else read_namespace database name)
        in
        (own_namespace, list_package_parts database (add_recording names note) package))
  in
  Package_table.replace database.implied package implied;
  (namespace, implied)

let compute_namespace database (package_database : package_database) =
  let package = package_database.name in
  let before = Option.value package_database.namespace ~default:Resolve.Names.empty_namespace in
  let implied_before = Option.value ~default:[] (Package_table.find_opt database.implied package) in
  let after, implied = compute_namespace_and_implied database package_database in
  package_database.namespace <- Some after;
  let make_membership_test parts =
    let members = Computed_table.create 256 in
    List.iter (fun part -> Computed_table.replace members part ()) parts;
    Computed_table.mem members
  in
  let was_implied = make_membership_test implied_before
  and is_implied = make_membership_test implied in
  let graph = obtain_call_graph database package in
  List.iter
    (function
      | Part.Call_edges (root, _) as part when not (is_implied part) ->
          Call_graph.remove_root graph root
      | _ -> ())
    implied_before;
  List.iter
    (function
      | Part.Call_edges (root, _) as part when not (was_implied part) ->
          ignore (Call_graph.add_root graph root)
      | _ -> ())
    implied;
  write_namespace_changes database package (Resolve.Names.list_changes before after);
  List.iter (fun part -> if not (was_implied part) then mark_stale database part) implied;
  forget database (List.filter (fun part -> not (is_implied part)) implied_before);
  own_lowering_roots database (make_stored_name_lookups database) package

let compute_type_facts database paths =
  let facts =
    compute_and_record database
      (List.map (fun path -> Part.Type_facts path) paths)
      (fun note ->
        let lookups = make_recording_interface_lookups database note ~is_checked:false in
        let interfaces = List.map (fun path -> (path, find_type_interface lookups path)) paths in
        if List.for_all (fun (_, interface) -> Option.is_some interface) interfaces then
          make_part
            (Interface.Properties.compute_component_facts lookups)
            (List.filter_map
               (fun (path, interface) -> Option.map (fun interface -> (path, interface)) interface)
               interfaces)
        else Blocked)
  in
  List.iter
    (fun path ->
      store database (Computed (Type_facts path))
        (Path_table.make_slot (obtain_owner database (Path.locate_package path)).type_facts path)
        (Some
           (match facts with
           | Value facts -> (
               match List.assoc_opt path facts with
               | Some facts -> Value facts
               | None ->
                   Compiler_bug.raise_bug ~stage:"Database" "the type facts of a component omit %s"
                     (Path.show path))
           | Failed _ | Blocked -> Blocked)))
    paths

let compute_part database (part : Part.computed) =
  let package_database = obtain_owner database (Part.locate_package part) in
  let compute_into_slot slot compute = compute_into database part slot compute in
  match part with
  | Parsed file ->
      compute_into_slot (File_table.make_slot package_database.parsed file) (fun note ->
          note (Input (Source file));
          let source = read_source database file in
          let tokens, lexer_diagnostics = Lexer.lex source in
          let tree, parser_diagnostics = Parser.parse tokens ~lexer_diagnostics in
          Some
            {
              tree;
              diagnostics = lexer_diagnostics @ parser_diagnostics;
              text = Source.text source;
            })
  | Namespace _ -> compute_namespace database package_database
  | Resolved (key, section) ->
      compute_into_slot
        (Key_section_table.make_slot package_database.resolved_names (key, section))
        (fun note ->
          Some
            (match Resolve.resolve (make_recording_name_lookups database note) key section with
            | Some (Ok resolved) -> Value resolved
            | Some (Error diagnostics) -> Failed diagnostics
            | None -> Blocked))
  | Grant (package, dependency) ->
      let entry =
        List.find
          (fun (entry : Manifest.dependency) -> entry.package = dependency)
          package_database.dependencies
      in
      compute_into_slot (Package_table.make_slot package_database.grants dependency) (fun note ->
          note (Input (Dependencies package));
          Some
            (Interface.Grants.resolve_grant
               (make_recording_name_lookups database note)
               ~package entry.capabilities))
  | Import_check file ->
      compute_into_slot (File_table.make_slot package_database.import_checks file) (fun note ->
          Some (list_import_diagnostics database note file))
  | Trait_header key ->
      compute_into_slot (Key_table.make_slot package_database.trait_headers key) (fun note ->
          Some
            (match
               ( (make_recording_name_lookups database note).read_definition key,
                 read_resolution_part database note Interface key )
             with
            | definition, Value resolved -> (
                match Resolve.make_trait_header definition resolved with
                | Some header -> Value header
                | None -> Blocked)
            | _, (Failed _ | Blocked) -> Blocked))
  | Constant_value path ->
      compute_into_slot (Path_table.make_slot package_database.constant_values path) (fun note ->
          Some
            (make_part
               (Interface.Constants.evaluate_constant
                  (make_recording_interface_lookups database note ~is_checked:false))
               path))
  | Header key ->
      compute_into_slot (Key_table.make_slot package_database.headers key) (fun note ->
          Some
            (match
               make_part
                 (Interface.Elaborator.elaborate_header
                    (make_recording_interface_lookups database note ~is_checked:false))
                 key
             with
            | Value (Ok header) -> Value header
            | Value (Error (_ :: _ as diagnostics)) -> Failed diagnostics
            | Value (Error []) | Failed _ | Blocked -> Blocked))
  | Interface key ->
      compute_into_slot (Key_table.make_slot package_database.interfaces key) (fun note ->
          Some
            (match
               make_part
                 (Interface.Elaborator.elaborate_definition
                    (make_recording_interface_lookups database note ~is_checked:false))
                 key
             with
            | Value elaborated -> make_interface_part elaborated
            | Failed _ | Blocked -> Blocked))
  | Derived_interface { type_; trait } ->
      compute_into_slot
        (Type_trait_table.make_slot package_database.derived_interfaces (type_, trait))
        (fun note ->
          Some
            (match
               make_part
                 (fun trait ->
                   Interface.Impls.derive_interface
                     (make_recording_interface_lookups database note ~is_checked:false)
                     ~type_ ~trait)
                 trait
             with
            | Value (Some interface) -> Value interface
            | Value None | Failed _ | Blocked -> Blocked))
  | Type_facts path -> compute_type_facts database [ path ]
  | Signature_check key ->
      compute_into_slot (Key_table.make_slot package_database.signature_checks key) (fun note ->
          read database note (Interface key);
          Some
            (match Key_table.find_opt package_database.interfaces key with
            | Some (Value _) ->
                make_checked_part
                  (fun key ->
                    ( Interface.Check.list_diagnostics
                        (make_recording_interface_lookups database note ~is_checked:false)
                        key,
                      () ))
                  key
            | Some (Failed _ | Blocked) -> Blocked
            | None -> report_uncomputed (Interface key)))
  | Contract key ->
      compute_into_slot (Key_table.make_slot package_database.contracts key) (fun note ->
          Some
            (match
               type_check Infer.check_contract (make_recording_infer_lookups database note) key
             with
            | Value (checked : Infer.checked) -> Value checked.form
            | Failed diagnostics -> Failed diagnostics
            | Blocked -> Blocked))
  | Checked_body key ->
      compute_into_slot (Key_table.make_slot package_database.checked_bodies key) (fun note ->
          Some (type_check Infer.check_body (make_recording_infer_lookups database note) key))
  | Body_mir key ->
      compute_into_slot (Key_table.make_slot package_database.body_parts key) (fun note ->
          read database note (Checked_body key);
          Some
            (match Key_table.find_opt package_database.checked_bodies key with
            | Some (Value checked) -> (
                match read_elaborated_interface database note ~is_checked:true key with
                | elaborated ->
                    Value (Mir.make_body_part ~interface:elaborated.interface checked.form)
                | exception Reads_failed_part -> Blocked)
            | Some (Failed _ | Blocked) -> Blocked
            | None -> report_uncomputed (Checked_body key)))
  | Contract_mir key ->
      compute_into_slot (Key_table.make_slot package_database.contract_parts key) (fun note ->
          read database note (Contract key);
          Some
            (match Key_table.find_opt package_database.contracts key with
            | Some (Value form) ->
                Value
                  (Mir.make_contract_part
                     ~find_type_interface:
                       (Interface.Definition.read_type_interface
                          (make_recording_interface_lookups database note ~is_checked:true))
                     key.path form)
            | Some (Failed _ | Blocked) -> Blocked
            | None -> report_uncomputed (Contract key)))
  | Generated_mir path ->
      compute_into_slot (Path_table.make_slot package_database.generated_parts path) (fun note ->
          match Infer.derive_form (make_recording_infer_lookups database note) path with
          | None -> None
          | Some form ->
              Some
                (make_part
                   (fun form ->
                     ( Mir.make_body_part form,
                       Mir.make_contract_part
                         ~find_type_interface:
                           (Interface.Definition.read_type_interface
                              (make_recording_interface_lookups database note ~is_checked:true))
                         path form ))
                   form)
          | exception Reads_failed_part -> Some Blocked)
  | Mir_call_edges path ->
      compute_into_slot (Path_table.make_slot package_database.mir_call_edges path) (fun note ->
          Some
            (make_part
               (Mir.Call_edges.list_path_edges (make_recording_call_edge_lookups database note))
               path))
  | Patterns key ->
      compute_into_slot (Key_table.make_slot package_database.patterns key) (fun note ->
          Some
            (make_checked_part
               (fun key -> (Patterns.check (make_recording_patterns_lookups database note) key, ()))
               key))
  | Usage key ->
      compute_into_slot (Key_table.make_slot package_database.usage key) (fun note ->
          Some
            (make_checked_part
               (fun key -> (Usage.check (make_recording_usage_lookups database note) key, ()))
               key))
  | Ownership key ->
      compute_into_slot (Key_table.make_slot package_database.ownership key) (fun note ->
          Some
            (make_checked_part
               (fun key ->
                 let result =
                   Ownership.check (make_recording_ownership_lookups database note) key
                 in
                 (result.diagnostics, result.must_be_disjoint))
               key))
  | Package_check (package, check) ->
      compute_into_slot (Check_table.make_slot package_database.package_checks check) (fun note ->
          Some
            (make_part
               (Package_checks.run (make_recording_package_checks_lookups database note) package)
               check))
  | Call_edges (path, viewer) ->
      let graph = obtain_call_graph database viewer in
      compute_into_slot
        {
          stored = Call_graph.find_successors graph path;
          replace =
            (fun call_edges ->
              List.iter
                (fun node -> mark_stale database (Call_edges (node, viewer)))
                (Call_graph.set_successors graph path call_edges));
          remove = (fun () -> Call_graph.remove_successors graph path);
        }
        (fun note -> Some (find_call_edges database note ~viewer path))
  | Proof key ->
      compute_into_slot (Key_table.make_slot package_database.proofs key) (fun note ->
          Some (make_part (Prover.prove (make_recording_proof_lookups database note)) key));
      own_template_checks database key
  | Lowering (Lowered key) ->
      compute_into_slot (Instance_table.make_slot database.lowered key) (fun note ->
          Some
            (match
               Compile.lower (read_lowering_settings database)
                 (make_recording_lowering_lookups database note)
                 key
             with
            | lowered -> Value lowered
            | exception Reads_failed_part -> Blocked
            | exception (Compile.Todo_type _ | Compile.Infinite_size _) -> Failed []));
      update_references database key
  | Lowering (Test_key key) -> compute_test_keys database [ key ]

type component =
  | Single of Part.computed
  | Type_fact_component of Path.t list
  | Test_key_component of Instance.key list

let list_component_parts = function
  | Single part -> [ part ]
  | Type_fact_component paths -> List.map (fun path -> Part.Type_facts path) paths
  | Test_key_component keys -> List.map (fun key -> Part.Lowering (Test_key key)) keys

let compute database unit =
  try
    match unit with
    | Single part -> compute_part database part
    | Type_fact_component paths -> compute_type_facts database paths
    | Test_key_component keys -> compute_test_keys database keys
  with Interface.Properties.Recursion_limit message ->
    Compiler_bug.raise_bug ~stage:"Database"
      "a stage after the checks reached a recursion limit: %s" message

let list_components database (stage : Stage.t) package parts =
  match stage with
  | Type_facts ->
      let paths =
        List.filter_map (function Part.Type_facts path -> Some path | _ -> None) parts
      in
      let in_closure = Path_table.create 64 in
      List.iter (fun path -> Path_table.replace in_closure path ()) paths;
      let lookups = make_recording_interface_lookups database ignore ~is_checked:false in
      List.map
        (fun paths -> Type_fact_component paths)
        (Strongly_connected.list_components
           (module Path)
           ~list_successors:(fun path ->
             match find_type_interface lookups path with
             | Some interface ->
                 List.filter (Path_table.mem in_closure)
                   (Interface.Properties.list_field_type_paths ~package interface)
             | None -> [])
           paths)
  | _ -> List.map (fun part -> Single part) parts

let list_test_key_components database parts =
  let keys =
    List.filter_map (function Part.Lowering (Test_key key) -> Some key | _ -> None) parts
  in
  let in_closure = Instance_table.of_seq (Seq.map (fun key -> (key, ())) (List.to_seq keys)) in
  List.map
    (fun keys -> Test_key_component keys)
    (Strongly_connected.list_components
       (module Instance)
       ~list_successors:(fun key ->
         match Instance_table.find_opt database.lowered key with
         | Some (Value (Ok lowered)) ->
             List.filter (Instance_table.mem in_closure) (Compile.list_references lowered)
         | Some (Value (Error _) | Failed _ | Blocked) | None -> [])
       keys)

let update_groups database package =
  match Package_table.find_opt database.graphs package with
  | Some graph when Call_graph.has_changes graph ->
      let { Call_graph.touched; removed } = Call_graph.update graph in
      List.iter
        (fun node ->
          let part = Part.Call_edges (node, package) in
          if Computed_table.mem database.reads part then
            mark_written database (Computed part) ~is_removal:true;
          discard database part)
        removed;
      let make_group_slot = Path_table.make_slot (obtain_owner database package).recursion_groups in
      let is_own node = Path.locate_package node = package in
      List.iter
        (fun node ->
          if is_own node then begin
            !observer
              (Computation { parts = [ Recursion_group node ]; reads = 0; distinct_reads = 0 });
            store database (Recursion_group node) (make_group_slot node)
              (match Call_graph.group graph node with
              | Blocked -> Some Blocked
              | Members [] -> None
              | Members members -> Some (Value members))
          end)
        touched;
      List.iter
        (fun node ->
          if is_own node then
            let slot = make_group_slot node in
            if Option.is_some slot.stored then store database (Recursion_group node) slot None)
        removed
  | Some _ | None -> ()

let has_work database package (stage : Stage.t) =
  match stage with
  | Recursion_groups -> (
      match Package_table.find_opt database.graphs package with
      | Some graph -> Call_graph.has_changes graph
      | None -> false)
  | stage -> (
      match Package_stage_table.find_opt database.stale (package, stage) with
      | Some parts -> Computed_table.length parts > 0
      | None -> false)

let drain_stage database ~is_drained ~on_raise (stage : Stage.t) packages =
  match stage with
  | Recursion_groups -> List.iter (update_groups database) packages
  | stage -> (
      let closure = Computed_table.create 64 in
      let rec close part =
        if not (Computed_table.mem closure part) then begin
          Computed_table.replace closure part ();
          Option.iter
            (Computed_table.iter (fun reader () ->
                 if
                   Stage.of_part reader = stage
                   && List.mem (Part.locate_package reader) packages
                   && is_drained reader
                 then close reader))
            (Part_table.find_opt database.readers (Stored (Computed part)))
        end
      in
      List.iter
        (fun package ->
          List.iter close (List.filter is_drained (list_stale_parts database package stage)))
        packages;
      let compute_components =
        List.iter (fun component ->
            let parts = list_component_parts component in
            if List.exists (is_stale database) parts then begin
              List.iter (unmark database) parts;
              match compute database component with
              | () -> ()
              | exception raised ->
                  List.iter (mark_stale database) parts;
                  on_raise parts raised
            end)
      in
      let list_parts_where is_kept =
        Computed_table.fold
          (fun part () parts -> if is_kept part then part :: parts else parts)
          closure []
      in
      let list_all_parts () = list_parts_where (fun _ -> true) in
      match stage with
      | Lowered_code -> compute_components (List.map (fun part -> Single part) (list_all_parts ()))
      | Test_keys -> compute_components (list_test_key_components database (list_all_parts ()))
      | stage ->
          List.iter
            (fun package ->
              compute_components
                (list_components database stage package
                   (list_parts_where (fun part -> Part.locate_package part = package))))
            packages)

let drain_where ?on_bug database ~drains requested =
  let packages = sort_in_dependency_order database requested in
  let broken = Computed_table.create 0 in
  let on_raise parts raised =
    match (on_bug, raised) with
    | Some on_bug, Compiler_bug.Bug bug ->
        List.iter (fun part -> Computed_table.replace broken part ()) parts;
        on_bug bug
    | _ -> raise raised
  in
  let rec drain_next () =
    let ready = lazy (collect_ready_instances database) in
    let is_drained part = is_drained ~ready part && not (Computed_table.mem broken part) in
    let has_drained_work stage =
      List.exists
        (fun package ->
          has_work database package stage
          && ((Computed_table.length broken = 0 && not (Stage.is_lowering stage))
             || List.exists is_drained (list_stale_parts database package stage)))
        packages
    in
    match List.find_opt (fun stage -> drains stage && has_drained_work stage) Stage.all with
    | Some stage ->
        drain_stage database ~is_drained ~on_raise stage packages;
        drain_next ()
    | None -> ()
  in
  drain_next ()

let drain database ~through requested =
  drain_where database ~drains:(Stage.drains ~through) requested

let propagate ?on_bug database =
  drain_where ?on_bug database ~drains:(fun _ -> true) database.project

type read = { dependent : Part.t; dependency : Part.t }

let make_definition_set paths =
  let set = Path_table.create 8 in
  List.iter (fun path -> Path_table.replace set path ()) paths;
  set

let is_of_other definition part =
  match Part.find_definition part with
  | Some other -> not (Path.equal other definition)
  | None -> false

let drain_checks database = drain database ~through:Proofs database.project
let is_checked part = not (Stage.is_lowering (Stage.of_part part))

let list_dependencies database paths =
  drain_checks database;
  let wanted = make_definition_set paths in
  Computed_table.fold
    (fun dependent dependencies found ->
      let dependent_part = Part.Stored (Computed dependent) in
      match Part.find_definition dependent_part with
      | Some definition when is_checked dependent && Path_table.mem wanted definition ->
          List.fold_left
            (fun found dependency ->
              if is_of_other definition dependency then
                { dependent = dependent_part; dependency } :: found
              else found)
            found dependencies
      | Some _ | None -> found)
    database.reads []

let list_dependents database paths =
  drain_checks database;
  let wanted = make_definition_set paths in
  Part_table.fold
    (fun dependency readers found ->
      match Part.find_definition dependency with
      | Some definition when Path_table.mem wanted definition ->
          Computed_table.fold
            (fun dependent () found ->
              let dependent_part = Part.Stored (Computed dependent) in
              if is_checked dependent && is_of_other definition dependent_part then
                { dependent = dependent_part; dependency } :: found
              else found)
            readers found
      | Some _ | None -> found)
    database.readers []

let list_changes database other =
  drain_checks database;
  drain_checks other;
  let parts = Stored_table.create 1024 in
  let add (part : Part.stored) =
    match part with
    | Computed (Namespace _ | Lowering _) -> ()
    | Computed _ | Recursion_group _ ->
        if Option.is_some (Part.find_definition (Stored part)) then
          Stored_table.replace parts part ()
  in
  List.iter
    (fun database ->
      Computed_table.iter (fun part _ -> add (Computed part)) database.reads;
      Part_table.iter
        (fun (part : Part.t) _ ->
          match part with Stored part -> add part | Input _ | Name _ -> ())
        database.readers;
      List.iter
        (fun package ->
          Path_table.iter
            (fun path _ -> add (Recursion_group path))
            (obtain_owner database package).recursion_groups)
        database.project)
    [ database; other ];
  Stored_table.fold
    (fun part () changed ->
      if (make_stored database part).is_equal_in other then changed else Part.Stored part :: changed)
    parts []

let update database changes =
  List.iter
    (fun ((file : Path.file), text) ->
      let package = file.module_.package in
      let package_database =
        match Package_table.find_opt database.package_databases package with
        | Some package_database -> package_database
        | None ->
            Compiler_bug.raise_bug ~stage:"Database" "%s is not a package of the build"
              (Path.show_package package)
      in
      let previous = File_table.find_opt package_database.sources file in
      let is_unchanged =
        match (previous, text) with
        | Some source, Some text -> String.equal (Source.text source) text
        | None, None -> not (List.mem file package_database.files)
        | Some _, None | None, Some _ -> false
      in
      if not is_unchanged then begin
        mark_unsaved database (File file);
        (match text with
        | Some text ->
            File_table.replace package_database.sources file (make_source file text);
            mark_stale database (Parsed file)
        | None ->
            File_table.remove package_database.sources file;
            forget database [ Parsed file ]);
        mark_readers database (Input (Source file));
        if Option.is_none previous || Option.is_none text then begin
          let modules = package_database.modules in
          set_files package_database
            (List.filter (( <> ) file) package_database.files
            @ if Option.is_some text then [ file ] else []);
          if modules <> package_database.modules then
            mark_readers database (Input (Modules package));
          mark_stale database (Namespace package)
        end
      end)
    changes

let list_stored_parts (package_database : package_database) : Part.stored list =
  Path_table.list_keys package_database.recursion_groups (fun path -> Part.Recursion_group path)
  @ List.map
      (fun part -> Part.Computed part)
      (List.concat
         [
           File_table.list_keys package_database.parsed (fun file -> Part.Parsed file);
           Key_section_table.list_keys package_database.resolved_names (fun (key, section) ->
               Part.Resolved (key, section));
           Package_table.list_keys package_database.grants (fun dependency ->
               Part.Grant (package_database.name, dependency));
           File_table.list_keys package_database.import_checks (fun file -> Part.Import_check file);
           Key_table.list_keys package_database.trait_headers (fun key -> Part.Trait_header key);
           Path_table.list_keys package_database.constant_values (fun path ->
               Part.Constant_value path);
           Key_table.list_keys package_database.headers (fun key -> Part.Header key);
           Key_table.list_keys package_database.interfaces (fun key -> Part.Interface key);
           Type_trait_table.list_keys package_database.derived_interfaces (fun (type_, trait) ->
               Part.Derived_interface { type_; trait });
           Path_table.list_keys package_database.type_facts (fun path -> Part.Type_facts path);
           Key_table.list_keys package_database.signature_checks (fun key ->
               Part.Signature_check key);
           Key_table.list_keys package_database.contracts (fun key -> Part.Contract key);
           Key_table.list_keys package_database.checked_bodies (fun key -> Part.Checked_body key);
           Key_table.list_keys package_database.body_parts (fun key -> Part.Body_mir key);
           Key_table.list_keys package_database.contract_parts (fun key -> Part.Contract_mir key);
           Path_table.list_keys package_database.generated_parts (fun path ->
               Part.Generated_mir path);
           Path_table.list_keys package_database.mir_call_edges (fun path ->
               Part.Mir_call_edges path);
           Key_table.list_keys package_database.patterns (fun key -> Part.Patterns key);
           Key_table.list_keys package_database.usage (fun key -> Part.Usage key);
           Key_table.list_keys package_database.ownership (fun key -> Part.Ownership key);
           Check_table.list_keys package_database.package_checks (fun check ->
               Part.Package_check (package_database.name, check));
           Key_table.list_keys package_database.proofs (fun key -> Part.Proof key);
         ])

let mark_differences database name ~(before : package_database option)
    ~(after : package_database option) =
  let make_empty () =
    let package_database = make_empty_package_database name ~dependencies:[] in
    package_database.namespace <- Some Resolve.Names.empty_namespace;
    package_database
  in
  let before =
    match before with Some package_database -> package_database | None -> make_empty ()
  in
  let after =
    match after with Some package_database -> package_database | None -> make_empty ()
  in
  let read_package_namespace (package_database : package_database) =
    Option.value package_database.namespace ~default:Resolve.Names.empty_namespace
  in
  write_namespace_changes database name
    (Resolve.Names.list_changes (read_package_namespace before) (read_package_namespace after));
  let find_text (package_database : package_database) file =
    Option.map Source.text (File_table.find_opt package_database.sources file)
  in
  List.iter
    (fun file ->
      if find_text before file <> find_text after file then
        mark_readers database (Input (Source file)))
    (List.sort_uniq compare (before.files @ after.files));
  if before.modules <> after.modules then mark_readers database (Input (Modules name));
  if before.dependencies <> after.dependencies then
    mark_readers database (Input (Dependencies name));
  let make_view (package_database : package_database) =
    let package_databases = Package_table.create 1 in
    Package_table.replace package_databases name package_database;
    { database with package_databases }
  in
  let parts = Stored_table.create 1024 in
  List.iter
    (fun part -> Stored_table.replace parts part ())
    (list_stored_parts before @ list_stored_parts after);
  Stored_table.iter
    (fun part () ->
      if not ((make_stored (make_view before) part).is_equal_in (make_view after)) then
        mark_written database part ~is_removal:(not (make_stored (make_view after) part).has_value))
    parts

let retire database (package_database : package_database) =
  let package = package_database.name in
  own_roots database (Stored (Computed (Namespace package))) [];
  Key_table.iter
    (fun key _ -> own_roots database (Stored (Computed (Proof key))) [])
    package_database.proofs;
  let is_own part =
    (not (Stage.is_lowering (Stage.of_part part))) && Part.locate_package part = package
  in
  mark_package_database_unsaved database package_database;
  List.iter (fun part -> mark_unsaved database (Value part)) (list_stored_parts package_database);
  List.iter
    (fun part ->
      mark_unsaved database (Value (Computed part));
      discard database part)
    (Computed_table.fold
       (fun part _ parts -> if is_own part then part :: parts else parts)
       database.reads []);
  Package_stage_table.filter_map_inplace
    (fun (owner, stage) parts ->
      if owner = package && not (Stage.is_lowering stage) then begin
        Computed_table.iter (fun part () -> mark_unsaved database (Stale part)) parts;
        None
      end
      else Some parts)
    database.stale;
  Package_table.remove database.graphs package;
  Package_table.remove database.implied package;
  Package_table.remove database.package_databases package

let relayout database ~(loaded : package_database list) (packages : Project.package list) =
  let project = List.map (fun (package : Project.package) -> package.name) packages in
  let find_loaded name =
    List.find_opt (fun (package_database : package_database) -> package_database.name = name) loaded
  in
  let names_before =
    Package_table.fold (fun name _ names -> name :: names) database.package_databases []
  in
  List.iter
    (fun name ->
      let before = Package_table.find database.package_databases name in
      let is_kept =
        if List.mem name database.project then List.mem name project
        else
          match find_loaded name with
          | Some package_database -> package_database == before
          | None -> false
      in
      if not is_kept then begin
        let after = if List.mem name project then None else find_loaded name in
        mark_differences database name ~before:(Some before) ~after;
        retire database before;
        Option.iter (Package_table.replace database.package_databases name) after
      end)
    names_before;
  List.iter
    (fun (package_database : package_database) ->
      if not (Package_table.mem database.package_databases package_database.name) then begin
        mark_differences database package_database.name ~before:None ~after:(Some package_database);
        Package_table.remove database.absent package_database.name;
        Package_table.replace database.package_databases package_database.name package_database
      end)
    loaded;
  List.iter
    (fun (package : Project.package) ->
      match Package_table.find_opt database.package_databases package.name with
      | Some package_database ->
          if package_database.dependencies <> package.dependencies then begin
            package_database.dependencies <- package.dependencies;
            mark_unsaved database (Package package.name);
            mark_readers database (Input (Dependencies package.name));
            mark_stale database (Namespace package.name)
          end;
          update database
            (List.map (fun (file, text) -> (file, Some text)) package.files
            @ List.filter_map
                (fun file -> if List.mem_assoc file package.files then None else Some (file, None))
                package_database.files)
      | None ->
          let package_database =
            make_package_database package.name ~dependencies:package.dependencies package.files
          in
          Package_table.remove database.absent package.name;
          Package_table.replace database.package_databases package.name package_database;
          mark_package_database_unsaved database package_database;
          mark_readers database (Input (Modules package.name));
          mark_readers database (Input (Dependencies package.name));
          List.iter (fun file -> mark_stale database (Parsed file)) package_database.files;
          mark_stale database (Namespace package.name))
    packages;
  let names_after =
    Package_table.fold (fun name _ names -> name :: names) database.package_databases []
  in
  if List.sort compare names_before <> List.sort compare names_after then
    mark_readers database (Input Packages);
  database.project <- project

let fingerprint text = Digest.BLAKE128.to_hex (Digest.BLAKE128.string text)

let find_saved_value database (entry : Entry.t) =
  match entry with
  | Value part ->
      if is_saved_part database part then (make_stored database part).marshal () else None
  | Reads part ->
      if is_saved_part database (Computed part) then
        Option.map marshal (Computed_table.find_opt database.reads part)
      else None
  | Stale part ->
      if is_saved_part database (Computed part) && is_stale database part then Some "" else None
  | Package name ->
      if List.mem name database.project then
        Option.map
          (fun (package_database : package_database) -> marshal package_database.dependencies)
          (find_package database name)
      else None
  | File file ->
      let name = file.module_.package in
      if List.mem name database.project then
        Option.bind (find_package database name) (fun (package_database : package_database) ->
            Option.map
              (fun source -> fingerprint (Source.text source))
              (File_table.find_opt package_database.sources file))
      else None
  | Owned owner -> Option.map marshal (Part_table.find_opt database.owned owner)

let list_unsaved database =
  drain database ~through:Namespaces database.project;
  List.iter (update_groups database) database.project;
  Entry_table.fold
    (fun entry () entries ->
      (Marshal.to_string entry [ No_sharing ], find_saved_value database entry) :: entries)
    database.unsaved []

let mark_saved database = Entry_table.reset database.unsaved

let restore_packages database ~find_text entries =
  let files = Package_table.create 64 in
  List.iter
    (function
      | Entry.File (file : Path.file), saved ->
          let name = file.module_.package in
          Package_table.replace files name
            ((file, saved) :: Option.value ~default:[] (Package_table.find_opt files name))
      | _ -> ())
    entries;
  List.iter
    (function
      | Entry.Package name, dependencies ->
          let package_database =
            make_empty_package_database name ~dependencies:(Marshal.from_string dependencies 0)
          in
          let listed = Option.value ~default:[] (Package_table.find_opt files name) in
          List.iter
            (fun (file, saved) ->
              match find_text file with
              | Some text when String.equal (fingerprint text) saved ->
                  File_table.replace package_database.sources file (make_source file text)
              | Some _ | None -> ())
            listed;
          set_files package_database (List.map fst listed);
          Package_table.replace database.package_databases name package_database;
          database.project <- name :: database.project
      | _ -> ())
    entries;
  database.project <- List.sort Path.compare_package database.project

let restore_parts database entries =
  List.iter
    (fun ((entry : Entry.t), bytes) ->
      match entry with
      | Value part when is_saved_part database part -> (make_stored database part).restore bytes
      | Reads part when is_saved_part database (Computed part) ->
          add_reads database part (Marshal.from_string bytes 0)
      | Stale part when is_saved_part database (Computed part) -> mark_stale database part
      | Owned owner -> Part_table.replace database.owned owner (Marshal.from_string bytes 0)
      | Value _ | Reads _ | Stale _ | Package _ | File _ -> ())
    entries

let restore_namespaces database =
  List.iter
    (fun name ->
      if List.mem name database.project then begin
        let package_database = Package_table.find database.package_databases name in
        let namespace, implied = compute_namespace_and_implied database package_database in
        package_database.namespace <- Some namespace;
        let graph = obtain_call_graph database name in
        List.iter
          (function
            | Part.Call_edges (root, _) -> ignore (Call_graph.add_root graph root) | _ -> ())
          implied
      end)
    (sort_in_dependency_order database database.project)

let restore_references database =
  Part_table.iter
    (fun owner roots ->
      List.iter
        (fun root ->
          Instance_table.replace database.owners root
            (owner :: Option.value (Instance_table.find_opt database.owners root) ~default:[]);
          ignore (References.add_root database.references root))
        roots)
    database.owned;
  let instances = Instance_table.create 1024 in
  let note key = Instance_table.replace instances key () in
  Instance_table.iter (fun key _ -> note key) database.lowered;
  Instance_table.iter
    (fun key () ->
      ignore
        (References.set_successors database.references key
           (Some (list_instance_edges database key))))
    instances;
  settle_references database

let restore ~loaded ~find_text entries =
  let database = create ~loaded [] in
  let entries =
    List.map (fun (key, value) -> ((Marshal.from_string key 0 : Entry.t), value)) entries
  in
  restore_packages database ~find_text entries;
  restore_parts database entries;
  restore_namespaces database;
  restore_references database;
  List.iter (update_groups database) database.project;
  mark_saved database;
  database

type checker = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

let remove_duplicates diagnostics =
  List.sort_uniq
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    diagnostics

let list_definition_diagnostics database (key : Resolve.Names.key) checker =
  let owner = obtain_owner database key.module_.package in
  match checker with
  | Resolve ->
      List.concat_map
        (fun section -> Key_section_table.list_failures owner.resolved_names (key, section))
        Resolve.sections
  | Interface ->
      Key_table.list_failures owner.headers key
      @ Key_table.list_failures owner.interfaces key
      @ Key_table.list_failures owner.signature_checks key
  | Infer ->
      Key_table.list_failures owner.contracts key @ Key_table.list_failures owner.checked_bodies key
  | Patterns -> Key_table.list_failures owner.patterns key
  | Usage -> Key_table.list_failures owner.usage key
  | Ownership -> Key_table.list_failures owner.ownership key
  | Package_checks -> []

let sort_by_span_and_code diagnostics =
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    diagnostics

let list_package_outcomes database package =
  match find_package database package with
  | None -> []
  | Some package_database ->
      List.filter_map
        (fun check ->
          match Check_table.find_opt package_database.package_checks check with
          | Some (Value outcome) -> Some outcome
          | Some (Failed _ | Blocked) -> None
          | None -> report_uncomputed (Package_check (package, check)))
        (Package_checks.list_checks
           ((make_stored_name_lookups database).list_package_declarations package))

let list_checker_diagnostics database (file : Path.file) checker =
  let names = make_stored_name_lookups database in
  let package_database = obtain_owner database file.module_.package in
  let place_diagnostics key diagnostics =
    let ({ file = home; base } : Resolve.Names.place) = names.read_place key in
    if home = file then
      List.map (Diagnostic.map_spans (Source.Definition_span.to_file ~base)) diagnostics
    else []
  in
  let of_definitions () =
    List.concat_map
      (fun key -> place_diagnostics key (list_definition_diagnostics database key checker))
      (list_file_keys database file)
  in
  sort_by_span_and_code
    (match checker with
    | Resolve ->
        Option.value ~default:[] (File_table.find_opt package_database.import_checks file)
        @ of_definitions ()
    | Package_checks ->
        List.concat_map
          (function
            | Package_checks.Placed diagnostics ->
                List.concat_map
                  (fun (diagnostic : Package_checks.placed) ->
                    place_diagnostics diagnostic.key [ diagnostic.diagnostic ])
                  diagnostics
            | Unused_dependencies _ -> [])
          (list_package_outcomes database file.module_.package)
    | Interface | Infer | Patterns | Usage | Ownership -> of_definitions ())

let checkers = [ Resolve; Interface; Infer; Patterns; Usage; Ownership; Package_checks ]
let check database packages = drain database ~through:Package_checks packages

let read_checked_body database (key : Resolve.Names.key) =
  drain database ~through:Checked_bodies [ key.module_.package ];
  match Key_table.find_opt (obtain_owner database key.module_.package).checked_bodies key with
  | Some (Value checked) -> Some checked
  | Some (Failed _ | Blocked) -> None
  | None -> report_uncomputed (Checked_body key)

let list_file_diagnostics database (file : Path.file) =
  drain database ~through:Package_checks [ file.module_.package ];
  remove_duplicates
    ((read_parsed_file database file).diagnostics
    @ List.concat_map (list_checker_diagnostics database file) checkers)

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused_dependency of Path.package

let list_manifest_problems database package =
  drain database ~through:Package_checks [ package ];
  let grants = (obtain_owner database package).grants in
  List.concat_map
    (fun dependency ->
      match Package_table.find_opt grants dependency with
      | Some (grant : Interface.Environment.grant) ->
          List.map (fun name -> Not_a_capability { dependency; name }) grant.unknown
      | None -> report_uncomputed (Grant (package, dependency)))
    ((make_stored_name_lookups database).list_dependency_names package)
  @ List.concat_map
      (function
        | Package_checks.Unused_dependencies dependencies ->
            List.map (fun dependency -> Unused_dependency dependency) dependencies
        | Placed _ -> [])
      (list_package_outcomes database package)

let find_code_packages database package =
  drain database ~through:Checked_bodies [ package ];
  let checked_bodies = (obtain_owner database package).checked_bodies in
  let read_used (declaration : Resolve.Names.declaration) =
    match declaration.path with
    | Test _ -> Some []
    | _ -> (
        let key = Resolve.Names.make_key declaration in
        match Key_table.find_opt checked_bodies key with
        | Some (Value checked) -> Some checked.used_packages
        | Some (Failed _ | Blocked) -> None
        | None -> report_uncomputed (Checked_body key))
  in
  let used =
    List.map read_used ((make_stored_name_lookups database).list_package_declarations package)
  in
  if List.mem None used then None
  else Some (List.sort_uniq Path.compare_package (List.concat_map Option.get used))

let read_package_database database package =
  drain database ~through:Recursion_groups [ package ];
  match Package_table.find_opt database.package_databases package with
  | Some package_database -> package_database
  | None ->
      Compiler_bug.raise_bug ~stage:"Database" "%s is not a package of the build"
        (Path.show_package package)

type proofs = { database : t; keys : Resolve.Names.key list }

let prove database files =
  let packages =
    List.sort_uniq Path.compare_package
      (List.map (fun (file : Path.file) -> file.module_.package) files)
  in
  drain database ~through:Recursion_groups packages;
  let keys = List.concat_map (list_file_keys database) files in
  List.iter
    (fun (key : Resolve.Names.key) ->
      let part = Part.Proof key in
      if
        is_stale database part
        || not (Key_table.mem (obtain_owner database key.module_.package).proofs key)
      then begin
        unmark database part;
        compute_part database part
      end
      else own_template_checks database key)
    keys;
  { database; keys }

let read_proof proofs (key : Resolve.Names.key) =
  Key_table.find_opt (obtain_owner proofs.database key.module_.package).proofs key

let list_holes proofs path =
  let names = make_stored_name_lookups proofs.database in
  match Option.bind (names.find_key path) (read_proof proofs) with
  | Some (Value (Obligations { holes; _ })) ->
      List.map
        (fun ((home : Resolve.Names.key), location) ->
          let ({ file; base } : Resolve.Names.place) = names.read_place home in
          let span = Prover.resolve_location names home location in
          (file, (Source.Definition_span.to_file ~base span).start))
        holes
  | Some (Value (Unsupported _ | Not_proven_here) | Failed _ | Blocked) | None -> []

let list_template_checks (proofs : proofs) =
  let database = proofs.database in
  match
    List.sort_uniq compare (List.concat_map (list_proof_template_checks database) proofs.keys)
  with
  | [] -> []
  | checks ->
      drain database ~through:Test_keys
        (List.sort_uniq Path.compare_package
           (List.map (fun (key : Resolve.Names.key) -> key.module_.package) proofs.keys));
      List.filter
        (fun check ->
          match Instance_table.find_opt database.test_keys (make_template_check_root check) with
          | Some Blocked -> false
          | Some (Value _ | Failed _) | None -> true)
        checks

let list_proofs (proofs : proofs) =
  List.filter_map
    (fun key ->
      match read_proof proofs key with
      | Some (Value proof) -> Some (key, proof)
      | Some (Failed _ | Blocked) -> None
      | None -> report_uncomputed (Proof key))
    proofs.keys

let make_proof_lookups database = make_recording_proof_lookups database ignore

let read_parsed database (file : Path.file) =
  drain database ~through:Parse [ file.module_.package ];
  (read_parsed_file database file).tree

let make_name_lookups database packages =
  drain database ~through:Namespaces packages;
  make_stored_name_lookups database

let read_resolved database (key : Resolve.Names.key) =
  drain database ~through:Resolution [ key.module_.package ];
  let owner = obtain_owner database key.module_.package in
  match
    List.filter_map
      (fun section ->
        match Key_section_table.find_opt owner.resolved_names (key, section) with
        | Some (Value resolved) -> Some resolved
        | Some (Failed _ | Blocked) -> None
        | None -> report_uncomputed (Resolved (key, section)))
      Resolve.sections
  with
  | [] -> None
  | parts -> Some (Resolve.merge parts)

let request database packages ~through ~list_needs keys =
  drain database ~through packages;
  List.iter
    (fun key ->
      if not (List.for_all (is_current database) (list_needs key)) then
        Compiler_bug.raise_bug ~stage:"Database"
          "%s is requested, and no root of lowering reaches it" (Instance.to_string key))
    keys

let read_requested table part key =
  match Instance_table.find_opt table key with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) ->
      Compiler_bug.raise_bug ~stage:"Database" "%s is requested from code with errors"
        (Part.show_computed (Lowering part))
  | None -> report_uncomputed (Lowering part)

let make_interface_lookups database packages =
  drain database ~through:Signature_checks packages;
  make_recording_interface_lookups database ignore ~is_checked:true

let check_calls database interface viewers key = function
  | Ok lowered ->
      List.iter
        (fun viewer ->
          Option.iter
            (fun graph ->
              Compile.check_calls interface
                ~find_call_edges:(fun path -> Option.join (Call_graph.find_successors graph path))
                key lowered)
            (Package_table.find_opt database.graphs viewer))
        viewers
  | Error _ -> ()

let list_reached_todo_types database key =
  let list_reads part = Option.value (Computed_table.find_opt database.reads part) ~default:[] in
  let is_stored_blocked = function
    | Some Blocked -> true
    | Some (Value _ | Failed _) | None -> false
  in
  let is_blocked (part : Part.computed) =
    match part with
    | Lowering (Test_key key) -> is_stored_blocked (Instance_table.find_opt database.test_keys key)
    | Lowering (Lowered key) -> is_stored_blocked (Instance_table.find_opt database.lowered key)
    | _ -> false
  in
  let find_todo_type (part : Part.t) =
    match part with
    | Stored (Computed (Interface key)) -> (
        match Key_table.find_opt (obtain_owner database key.module_.package).interfaces key with
        | Some (Value { interface = Type_interface { shape = Todo_type; _ }; _ }) -> Some key.path
        | Some (Value _ | Failed _ | Blocked) | None -> None)
    | _ -> None
  in
  let visited = Part_table.create 16 in
  let rec visit todo_types (part : Part.t) =
    if Part_table.mem visited part then todo_types
    else begin
      Part_table.replace visited part ();
      match part with
      | Stored (Computed (Lowering (Lowered _) as part))
        when (make_stored database (Computed part)).is_failed ->
          List.filter_map find_todo_type (list_reads part) @ todo_types
      | Stored (Computed part) when is_blocked part ->
          List.fold_left visit todo_types (list_reads part)
      | _ -> todo_types
    end
  in
  List.sort_uniq Path.compare (visit [] (Stored (Computed (Lowering (Test_key key)))))

let make_lowering_requests database packages : Compile.requests =
  let interface = make_interface_lookups database packages in
  {
    settings = read_lowering_settings database;
    read_source = read_source database;
    interface;
    mir = make_recording_mir_lookups database ignore;
    find_lowered =
      (fun key ->
        request database packages ~through:Lowered_code
          ~list_needs:(fun key -> [ Lowered key ])
          [ key ];
        match Instance_table.find_opt database.lowered key with
        | Some (Value lowered) ->
            check_calls database interface packages key lowered;
            Some lowered
        | Some (Failed _ | Blocked) -> None
        | None -> report_uncomputed (Lowering (Lowered key)));
    read_test_key =
      (fun key ->
        request database packages ~through:Test_keys
          ~list_needs:(fun key -> [ Test_key key ])
          [ key ];
        read_requested database.test_keys (Test_key key) key);
    list_reached_todo_types =
      (fun key ->
        request database packages ~through:Test_keys
          ~list_needs:(fun key -> [ Test_key key ])
          [ key ];
        list_reached_todo_types database key);
  }

let find_main database package =
  drain database ~through:Namespaces [ package ];
  find_entry_point (make_stored_name_lookups database) package

let with_observer observe run =
  let previous = !observer in
  observer := observe;
  Fun.protect ~finally:(fun () -> observer := previous) run

module For_testing = struct
  type nonrec checker = checker =
    | Resolve
    | Interface
    | Infer
    | Patterns
    | Usage
    | Ownership
    | Package_checks

  let list_diagnostics checkers database (file : Path.file) =
    let through : Stage.t =
      if List.mem Package_checks checkers then Package_checks
      else if List.exists (fun checker -> List.mem checker [ Patterns; Usage; Ownership ]) checkers
      then Body_checks
      else if List.mem Infer checkers then Checked_bodies
      else if List.mem Interface checkers then Signature_checks
      else Import_checks
    in
    drain database ~through [ file.module_.package ];
    List.concat_map (list_checker_diagnostics database file) checkers

  let read_derived_form database path =
    drain database ~through:Checked_bodies [ Path.locate_package path ];
    match Infer.derive_form (make_recording_infer_lookups database ignore) path with
    | form -> form
    | exception Reads_failed_part -> None

  let read_core database path =
    drain database ~through:Mir [ Path.locate_package path ];
    Option.bind (make_form_origin database ignore path) (fun (origin, substitution) ->
        Option.map
          (fun form -> (form, substitution))
          (match origin with
          | Infer.Written key | Inherited key ->
              Option.map
                (fun (checked : Infer.checked) -> checked.form)
                (read_checked_body database key)
          | Derived _ -> read_derived_form database path))

  let make_mir_lookups database package =
    drain database ~through:Mir [ package ];
    make_recording_mir_lookups database ignore

  let list_reads database shown =
    match
      Computed_table.fold
        (fun part reads found -> if Part.show_computed part = shown then Some reads else found)
        database.reads None
    with
    | Some reads -> List.sort compare (List.map Part.show reads)
    | None -> Compiler_bug.raise_bug ~stage:"Database" "%s is not computed" shown

  let list_unread_parts database packages =
    drain database ~through:Recursion_groups packages;
    Computed_table.fold
      (fun part _ unread ->
        match Part_table.find_opt database.readers (Part.Stored (Computed part)) with
        | Some readers when Computed_table.length readers > 0 -> unread
        | Some _ | None -> part :: unread)
      database.reads []

  let list_differences hot cold =
    let parts = Stored_table.create 1024 in
    List.iter
      (fun database ->
        Computed_table.iter
          (fun part _ -> Stored_table.replace parts (Computed part) ())
          database.reads;
        Package_table.iter
          (fun _ package_database ->
            Path_table.iter
              (fun path _ -> Stored_table.replace parts (Recursion_group path) ())
              package_database.recursion_groups)
          database.package_databases)
      [ hot; cold ];
    let find_reads database (part : Part.stored) =
      match part with
      | Computed part ->
          Option.map (List.sort compare) (Computed_table.find_opt database.reads part)
      | Recursion_group _ -> None
    in
    List.sort compare
      (Stored_table.fold
         (fun part () differences ->
           if
             find_reads hot part <> find_reads cold part
             || not ((make_stored hot part).is_equal_in cold)
           then Part.show (Stored part) :: differences
           else differences)
         parts [])

  type observed = { recomputed : string list; collected : string list }

  let observe run =
    let recomputed = ref [] and collected = ref [] in
    with_observer
      (function
        | Computation { parts; _ } ->
            recomputed := List.map (fun part -> Part.show (Stored part)) parts @ !recomputed
        | Write { part = Computed (Lowering part); is_removal = true } ->
            collected := Part.show_computed (Lowering part) :: !collected
        | Write _ | Unchanged _ -> ())
      run;
    {
      recomputed = List.sort_uniq compare !recomputed;
      collected = List.sort_uniq compare !collected;
    }

  let add_root database key =
    own_roots database (Input Packages)
      (key :: Option.value (Part_table.find_opt database.owned (Input Packages)) ~default:[])

  let read_proof = read_proof

  let read_ownership database (key : Resolve.Names.key) =
    match Key_table.find_opt (obtain_owner database key.module_.package).ownership key with
    | Some part -> part
    | None -> report_uncomputed (Ownership key)
end

type counts = {
  kind : string;
  computed : int;
  unchanged : int;
  writes : int;
  reads : int;
  distinct_reads : int;
}

let locate_stage : Part.stored -> Stage.t = function
  | Computed part -> Stage.of_part part
  | Recursion_group _ -> Recursion_groups

let count run =
  let counts_by_kind = Hashtbl.create 32 in
  let add (part : Part.stored) increment =
    let stage = locate_stage part and kind = Part.show_kind (Stored part) in
    let counts =
      Option.value
        (Hashtbl.find_opt counts_by_kind (stage, kind))
        ~default:{ kind; computed = 0; unchanged = 0; writes = 0; reads = 0; distinct_reads = 0 }
    in
    Hashtbl.replace counts_by_kind (stage, kind) (increment counts)
  in
  let result =
    with_observer
      (function
        | Computation { parts = []; _ } ->
            Compiler_bug.raise_bug ~stage:"Database" "a computation computed no part"
        | Computation { parts = first :: _ as parts; reads; distinct_reads } ->
            add first (fun counts ->
                {
                  counts with
                  computed = counts.computed + List.length parts;
                  reads = counts.reads + reads;
                  distinct_reads = counts.distinct_reads + distinct_reads;
                })
        | Unchanged part ->
            add part (fun counts -> { counts with unchanged = counts.unchanged + 1 })
        | Write { part; _ } -> add part (fun counts -> { counts with writes = counts.writes + 1 }))
      run
  in
  ( result,
    List.map snd
      (List.sort
         (fun ((stage, kind), _) ((other_stage, other_kind), _) ->
           match Stage.compare stage other_stage with
           | 0 -> String.compare kind other_kind
           | order -> order)
         (List.of_seq (Hashtbl.to_seq counts_by_kind))) )
