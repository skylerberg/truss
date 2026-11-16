module Part = Part
module Names = Resolve.Names
module Environment = Interface.Environment
module Path_table = Hashtbl.Make (Path)
module Call_graph = Graph.Make (Path)

type 'a part = Value of 'a | Failed of Diagnostic.in_definition list | Blocked

exception Reads_failed_part

module Structural_key (Key : sig
  type t
end) =
struct
  type t = Key.t

  let equal : t -> t -> bool = ( = )
  let hash : t -> int = Hashtbl.hash_param 64 256
  let compare : t -> t -> int = Stdlib.compare
end

module Part_table = Hashtbl.Make (Structural_key (Part))

module Computed_table = Hashtbl.Make (Structural_key (struct
  type t = Part.computed
end))

module Stored_table = Hashtbl.Make (Structural_key (struct
  type t = Part.stored
end))

module Instance_key = Structural_key (struct
  type t = Instance.key
end)

module Instance_table = Hashtbl.Make (Instance_key)
module References = Graph.Make (Instance_key)

module Entry = struct
  type t =
    | Value of Part.stored
    | Reads of Part.computed
    | Stale of Part.computed
    | Package of Path.package
    | File of Path.file
    | Owned of Part.t
end

module Entry_table = Hashtbl.Make (Structural_key (Entry))

type parsed = { tree : Syntax.file; diagnostics : Diagnostic.t list; text : string }

type package_database = {
  name : Path.package;
  mutable dependencies : Manifest.dependency list;
  mutable modules : Path.module_ list;
  mutable files : Path.file list;
  sources : (Path.file, Source.t) Hashtbl.t;
  parsed : (Path.file, parsed) Hashtbl.t;
  mutable namespace : Names.namespace option;
  resolved_names : (Names.key * Resolve.section, Resolve.resolved part) Hashtbl.t;
  import_checks : (Path.file, Diagnostic.t list) Hashtbl.t;
  trait_headers : (Names.key, Resolve.trait_header part) Hashtbl.t;
  constant_values : Z.t option part Path_table.t;
  headers : (Names.key, Environment.header part) Hashtbl.t;
  interfaces : (Names.key, Environment.lowered_interface part) Hashtbl.t;
  derived_interfaces : (Path.t * Path.t, Types.impl_interface part) Hashtbl.t;
  type_facts : Environment.type_facts part Path_table.t;
  grants : (Path.package, Environment.grant) Hashtbl.t;
  signature_checks : (Names.key, unit part) Hashtbl.t;
  contracts : (Names.key, Core.t part) Hashtbl.t;
  checked_bodies : (Names.key, Infer.checked part) Hashtbl.t;
  derived_forms : Core.t part Path_table.t;
  body_parts : (Names.key, Mir.body_part part) Hashtbl.t;
  contract_parts : (Names.key, Mir.contract_part part) Hashtbl.t;
  generated_parts : (Mir.body_part * Mir.contract_part) part Path_table.t;
  call_edges : Path.t list part Path_table.t;
  patterns : (Names.key, unit part) Hashtbl.t;
  usage : (Names.key, unit part) Hashtbl.t;
  ownership : (Names.key, (Core.origin * Core.origin) list part) Hashtbl.t;
  used_packages : (Names.key, Path.package list part) Hashtbl.t;
  package_checks : (Package_checks.check, Package_checks.outcome part) Hashtbl.t;
  recursion_groups : Path.t list part Path_table.t;
  proofs : (Names.key, Prover.proof part) Hashtbl.t;
}

type t = {
  package_databases : (Path.package, package_database) Hashtbl.t;
  mutable project : Path.package list;
  absent : (Path.package, package_database) Hashtbl.t;
  reads : Part.t list Computed_table.t;
  readers : unit Computed_table.t Part_table.t;
  stale : (Path.package * Stage.t, unit Computed_table.t) Hashtbl.t;
  implied : (Path.package, Part.computed list) Hashtbl.t;
  graphs : (Path.package, Call_graph.t) Hashtbl.t;
  lowering : Compile.Lookups.settings option;
  lowered : (Compile.lowered, Compile.unsupported) result part Instance_table.t;
  test_keys : (string, Compile.unsupported) result part Instance_table.t;
  references : References.t;
  owners : Part.t list Instance_table.t;
  owned : Instance.key list Part_table.t;
  unsaved : unit Entry_table.t;
  mutable observe : observation -> unit;
}

and observation = Recomputed of Part.stored | Collected of Part.lowering

let make_empty_package_database name ~dependencies =
  {
    name;
    dependencies;
    modules = [];
    files = [];
    sources = Hashtbl.create 64;
    parsed = Hashtbl.create 64;
    namespace = None;
    resolved_names = Hashtbl.create 1024;
    import_checks = Hashtbl.create 64;
    trait_headers = Hashtbl.create 64;
    constant_values = Path_table.create 64;
    headers = Hashtbl.create 64;
    interfaces = Hashtbl.create 256;
    derived_interfaces = Hashtbl.create 16;
    type_facts = Path_table.create 64;
    grants = Hashtbl.create 4;
    signature_checks = Hashtbl.create 256;
    contracts = Hashtbl.create 256;
    checked_bodies = Hashtbl.create 256;
    derived_forms = Path_table.create 16;
    body_parts = Hashtbl.create 256;
    contract_parts = Hashtbl.create 256;
    generated_parts = Path_table.create 16;
    call_edges = Path_table.create 256;
    patterns = Hashtbl.create 64;
    usage = Hashtbl.create 64;
    ownership = Hashtbl.create 64;
    used_packages = Hashtbl.create 64;
    package_checks = Hashtbl.create 64;
    recursion_groups = Path_table.create 64;
    proofs = Hashtbl.create 64;
  }

let list_files (package_database : package_database) files =
  package_database.files <- List.sort compare files;
  package_database.modules <-
    List.sort_uniq compare
      (List.map (fun (file : Path.file) -> file.module_) package_database.files)

let source_of (file : Path.file) text = Source.create ~path:(Path.show_file file) text

let make_package_database name ~dependencies (texts : (Path.file * string) list) =
  let package_database = make_empty_package_database name ~dependencies in
  List.iter
    (fun (file, text) -> Hashtbl.replace package_database.sources file (source_of file text))
    texts;
  list_files package_database (List.map fst texts);
  package_database

let mark_unsaved database entry = Entry_table.replace database.unsaved entry ()

let mark_package_database_unsaved database (package_database : package_database) =
  mark_unsaved database (Package package_database.name);
  List.iter (fun file -> mark_unsaved database (File file)) package_database.files

let mark_stale database part =
  let slot = (Part.package part, Stage.of_part part) in
  let parts =
    match Hashtbl.find_opt database.stale slot with
    | Some parts -> parts
    | None ->
        let parts = Computed_table.create 64 in
        Hashtbl.replace database.stale slot parts;
        parts
  in
  if not (Computed_table.mem parts part) then begin
    Computed_table.replace parts part ();
    mark_unsaved database (Stale part)
  end

let is_stale database part =
  match Hashtbl.find_opt database.stale (Part.package part, Stage.of_part part) with
  | Some parts -> Computed_table.mem parts part
  | None -> false

let unmark database part =
  Option.iter
    (fun parts ->
      if Computed_table.mem parts part then begin
        Computed_table.remove parts part;
        mark_unsaved database (Stale part)
      end)
    (Hashtbl.find_opt database.stale (Part.package part, Stage.of_part part))

let stale_parts database package stage =
  match Hashtbl.find_opt database.stale (package, stage) with
  | Some parts -> Computed_table.fold (fun part () parts -> part :: parts) parts []
  | None -> []

let create ?(loaded = []) ?(checks = true) (packages : Project.package list) =
  let package_databases = Hashtbl.create 8 in
  List.iter
    (fun package_database ->
      Hashtbl.replace package_databases package_database.name package_database)
    loaded;
  let database =
    {
      package_databases;
      project = List.map (fun (package : Project.package) -> package.name) packages;
      absent = Hashtbl.create 4;
      reads = Computed_table.create 4096;
      readers = Part_table.create 4096;
      stale = Hashtbl.create 64;
      implied = Hashtbl.create 8;
      graphs = Hashtbl.create 8;
      lowering = Option.map (fun system -> { Compile.Lookups.checks; system }) Libc.host;
      lowered = Instance_table.create 1024;
      test_keys = Instance_table.create 1024;
      references = References.create ~tracks_blocked:false;
      owners = Instance_table.create 64;
      owned = Part_table.create 64;
      unsaved = Entry_table.create 4096;
      observe = ignore;
    }
  in
  List.iter
    (fun (package : Project.package) ->
      let package_database =
        make_package_database package.name ~dependencies:package.dependencies package.files
      in
      Hashtbl.replace package_databases package.name package_database;
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
    sources = Hashtbl.copy package_database.sources;
    parsed = Hashtbl.copy package_database.parsed;
    namespace = package_database.namespace;
    resolved_names = Hashtbl.copy package_database.resolved_names;
    import_checks = Hashtbl.copy package_database.import_checks;
    trait_headers = Hashtbl.copy package_database.trait_headers;
    constant_values = Path_table.copy package_database.constant_values;
    headers = Hashtbl.copy package_database.headers;
    interfaces = Hashtbl.copy package_database.interfaces;
    derived_interfaces = Hashtbl.copy package_database.derived_interfaces;
    type_facts = Path_table.copy package_database.type_facts;
    grants = Hashtbl.copy package_database.grants;
    signature_checks = Hashtbl.copy package_database.signature_checks;
    contracts = Hashtbl.copy package_database.contracts;
    checked_bodies = Hashtbl.copy package_database.checked_bodies;
    derived_forms = Path_table.copy package_database.derived_forms;
    body_parts = Hashtbl.copy package_database.body_parts;
    contract_parts = Hashtbl.copy package_database.contract_parts;
    generated_parts = Path_table.copy package_database.generated_parts;
    call_edges = Path_table.copy package_database.call_edges;
    patterns = Hashtbl.copy package_database.patterns;
    usage = Hashtbl.copy package_database.usage;
    ownership = Hashtbl.copy package_database.ownership;
    used_packages = Hashtbl.copy package_database.used_packages;
    package_checks = Hashtbl.copy package_database.package_checks;
    recursion_groups = Path_table.copy package_database.recursion_groups;
    proofs = Hashtbl.copy package_database.proofs;
  }

let copy database =
  let package_databases = Hashtbl.copy database.package_databases in
  Hashtbl.filter_map_inplace
    (fun name package_database ->
      Some
        (if List.mem name database.project then copy_package_database package_database
         else package_database))
    package_databases;
  let readers = Part_table.copy database.readers in
  Part_table.filter_map_inplace (fun _ parts -> Some (Computed_table.copy parts)) readers;
  let stale = Hashtbl.copy database.stale in
  Hashtbl.filter_map_inplace (fun _ parts -> Some (Computed_table.copy parts)) stale;
  let graphs = Hashtbl.copy database.graphs in
  Hashtbl.filter_map_inplace (fun _ graph -> Some (Call_graph.copy graph)) graphs;
  {
    package_databases;
    project = database.project;
    absent = Hashtbl.copy database.absent;
    reads = Computed_table.copy database.reads;
    readers;
    stale;
    implied = Hashtbl.copy database.implied;
    graphs;
    lowering = database.lowering;
    lowered = Instance_table.copy database.lowered;
    test_keys = Instance_table.copy database.test_keys;
    references = References.copy database.references;
    owners = Instance_table.copy database.owners;
    owned = Part_table.copy database.owned;
    unsaved = Entry_table.create 64;
    observe = ignore;
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

let computing database parts compute =
  let reads = Part_table.create 16 in
  let result = compute (fun part -> Part_table.replace reads part ()) in
  record database parts reads;
  result

type 'a slot = { stored : 'a option; replace : 'a -> unit; remove : unit -> unit }

let keyed table key =
  {
    stored = Hashtbl.find_opt table key;
    replace = Hashtbl.replace table key;
    remove = (fun () -> Hashtbl.remove table key);
  }

let at_path table path =
  {
    stored = Path_table.find_opt table path;
    replace = Path_table.replace table path;
    remove = (fun () -> Path_table.remove table path);
  }

let mark_readers ?(only = fun _ -> true) database part =
  Option.iter
    (Computed_table.iter (fun reader () -> if only reader then mark_stale database reader))
    (Part_table.find_opt database.readers part)

let store database part slot value =
  let is_changed =
    match (slot.stored, value) with
    | Some stored, Some value -> stored <> value
    | None, None -> false
    | Some _, None | None, Some _ -> true
  in
  if is_changed then begin
    (match value with Some value -> slot.replace value | None -> slot.remove ());
    mark_unsaved database (Value part);
    mark_readers database (Stored part)
  end

let compute_into database part slot compute =
  store database (Computed part) slot (computing database [ part ] compute)

let owner database package =
  match Hashtbl.find_opt database.package_databases package with
  | Some package_database -> package_database
  | None -> (
      match Hashtbl.find_opt database.absent package with
      | Some package_database -> package_database
      | None ->
          let package_database = make_empty_package_database package ~dependencies:[] in
          package_database.namespace <- Some Names.empty_namespace;
          Hashtbl.replace database.absent package package_database;
          package_database)

let call_graph database package =
  match Hashtbl.find_opt database.graphs package with
  | Some graph -> graph
  | None ->
      let graph = Call_graph.create ~tracks_blocked:true in
      Hashtbl.replace database.graphs package graph;
      graph

let unchecked part =
  Compiler_bug.bug ~stage:"Database" "%s is not computed" (Part.show_computed part)

let read database note part =
  note (Part.Stored (Computed part));
  if is_stale database part then
    Compiler_bug.bug ~stage:"Database" "%s is read while it is stale" (Part.show_computed part)

let read_part database note part_of select (key : Names.key) =
  let part = part_of key in
  read database note part;
  match Hashtbl.find_opt (select (owner database key.module_.package)) key with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> unchecked part

let computed compute argument =
  match compute argument with value -> Value value | exception Reads_failed_part -> Blocked

let checked_part check key =
  match check key with
  | [], value -> Value value
  | diagnostics, _ -> Failed diagnostics
  | exception Reads_failed_part -> Blocked

let value = function Value value -> value | Failed _ | Blocked -> raise Reads_failed_part
let package database name = Hashtbl.find_opt database.package_databases name

let dependency_names database name =
  match package database name with
  | Some package ->
      List.map (fun (dependency : Manifest.dependency) -> dependency.package) package.dependencies
  | None -> []

let modules database name =
  match package database name with Some package -> package.modules | None -> []

let source database (file : Path.file) =
  match Hashtbl.find_opt (owner database file.module_.package).sources file with
  | Some source -> source
  | None -> Compiler_bug.bug ~stage:"Database" "%s is not a file of the build" (Path.show_file file)

let in_dependency_order database packages =
  let seen = Hashtbl.create 8 in
  let order = ref [] in
  let rec visit package =
    if not (Hashtbl.mem seen package) then begin
      Hashtbl.replace seen package ();
      List.iter visit (List.sort Path.compare_package (dependency_names database package));
      order := package :: !order
    end
  in
  visit Path.standard_package;
  List.iter visit packages;
  List.rev !order

let namespace database package =
  match (owner database package).namespace with
  | Some namespace -> namespace
  | None -> unchecked (Namespace package)

let names_over database ~namespace =
  Names.of_namespaces ~namespace
    ~module_exists:(fun (module_ : Path.module_) ->
      module_ = Intrinsic.module_ || List.mem module_ (modules database module_.package))
    ~split_module:
      (Path.split_module ~is_package:(fun name -> Option.is_some (package database name)))
    ~dependency_names:(dependency_names database)

let names_lookups database = names_over database ~namespace:(namespace database)

let recording (names : Names.lookups) (note : Part.t -> unit) : Names.lookups =
  let noting (part : Part.name) read =
    note (Name part);
    read
  in
  let noting_input (part : Part.input) read =
    note (Input part);
    read
  in
  {
    find = (fun module_ name -> noting (Entry (module_, name)) (names.find module_ name));
    entries = (fun module_ -> noting (Entries module_) (names.entries module_));
    imports = (fun key -> noting (Imports key) (names.imports key));
    module_exists =
      (fun module_ -> noting_input (Modules module_.package) (names.module_exists module_));
    split_module = (fun parts -> noting_input Packages (names.split_module parts));
    dependency_names =
      (fun package -> noting_input (Dependencies package) (names.dependency_names package));
    key =
      (fun path ->
        (match path with
        | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ }
          ->
            note (Name (Declaration { module_; path; ordinal = 0 }))
        | Method { owner; name; _ } | Member_constant { owner; name } ->
            note (Name (Members (owner, name)))
        | Derived _ | Unresolved _ -> ());
        names.key path);
    declaration = (fun key -> noting (Declaration key) (names.declaration key));
    declarations =
      (fun module_ -> noting (Module_declarations module_) (names.declarations module_));
    declarations_in = (fun file -> noting (File_declarations file) (names.declarations_in file));
    package_declarations =
      (fun package -> noting (Package_declarations package) (names.package_declarations package));
    definition = (fun key -> noting (Tree key) (names.definition key));
    text = (fun key -> noting (Text key) (names.text key));
    spans = (fun key -> noting (Tree key) (names.spans key));
    recovered = (fun key -> noting (Tree key) (names.recovered key));
    place = (fun key -> noting (Place key) (names.place key));
    container = (fun key -> noting (Container key) (names.container key));
    contained = (fun key -> noting (Contained key) (names.contained key));
    members = (fun owner name -> noting (Members (owner, name)) (names.members owner name));
    traits_declaring =
      (fun package name ->
        noting (Traits_declaring (package, name)) (names.traits_declaring package name));
    impls = (fun package -> noting (Impl_index package) (names.impls package));
    impls_of_type =
      (fun package type_ ->
        noting (Impls_of_type (package, type_)) (names.impls_of_type package type_));
    impls_of_trait =
      (fun package trait ->
        noting (Impls_of_trait (package, trait)) (names.impls_of_trait package trait));
    law_proofs =
      (fun package name -> noting (Law_proofs (package, name)) (names.law_proofs package name));
  }

let recording_names database note = recording (names_lookups database) note

let parsed_file database (file : Path.file) =
  match Hashtbl.find_opt (owner database file.module_.package).parsed file with
  | Some parsed -> parsed
  | None -> unchecked (Parsed file)

let namespace_of database note (package_database : package_database) =
  note (Part.Input (Modules package_database.name));
  Names.namespace (recording_names database note) package_database.name
    (List.map
       (fun module_ ->
         ( module_,
           List.filter_map
             (fun (file : Path.file) ->
               if file.module_ = module_ then begin
                 read database note (Parsed file);
                 let parsed = parsed_file database file in
                 Some (file, parsed.tree, parsed.text)
               end
               else None)
             package_database.files ))
       package_database.modules)

let file_keys database file = List.map Names.key_of ((names_lookups database).declarations_in file)

let resolved_part database note section (key : Names.key) =
  read database note (Resolved (key, section));
  match Hashtbl.find_opt (owner database key.module_.package).resolved_names (key, section) with
  | Some part -> part
  | None -> unchecked (Resolved (key, section))

let resolved database note section key = value (resolved_part database note section key)

let read_whole_resolution database note key =
  Resolve.merge (List.map (fun section -> resolved database note section key) Resolve.sections)

let lowered_interface database note ~is_checked (key : Names.key) =
  let owner = owner database key.module_.package in
  read database note (Interface key);
  if is_checked then begin
    read database note (Signature_check key);
    match Hashtbl.find_opt owner.signature_checks key with
    | Some (Failed _ | Blocked) -> raise Reads_failed_part
    | Some (Value ()) -> ()
    | None -> unchecked (Signature_check key)
  end;
  match Hashtbl.find_opt owner.interfaces key with
  | Some part -> value part
  | None -> unchecked (Interface key)

let interface_lookups database note ~is_checked : Interface.Lookups.t =
  let names = recording_names database note in
  let lowered_interface = lowered_interface database note ~is_checked in
  {
    names;
    resolved = resolved database note;
    trait_header =
      (fun path ->
        Option.bind (names.key path) (fun key ->
            read database note (Trait_header key);
            Option.map value
              (Hashtbl.find_opt (owner database key.module_.package).trait_headers key)));
    constant_value =
      (fun path ->
        read database note (Constant_value path);
        Option.bind
          (Path_table.find_opt (owner database (Path.package path)).constant_values path)
          value);
    header =
      (fun key ->
        read database note (Header key);
        Option.map value (Hashtbl.find_opt (owner database key.module_.package).headers key));
    lowered_interface;
    derived_interface =
      (fun ~type_ ~trait ->
        Option.iter (fun key -> ignore (lowered_interface key)) (names.key type_);
        read database note (Derived_interface { type_; trait });
        Option.map value
          (Hashtbl.find_opt (owner database (Path.package type_)).derived_interfaces (type_, trait)));
    type_facts =
      (fun path ->
        read database note (Type_facts path);
        Option.map value (Path_table.find_opt (owner database (Path.package path)).type_facts path));
    granted =
      (fun package dependency ->
        read database note (Grant (package, dependency));
        Hashtbl.find_opt (owner database package).grants dependency);
  }

let interface_part (lowered : Environment.lowered_interface) =
  match (lowered.diagnostics, lowered.interface) with
  | [], Error_interface _ -> Blocked
  | [], _ -> Value lowered
  | diagnostics, _ -> Failed diagnostics

let type_interface lookups path =
  match computed (Interface.Definition.type_interface lookups) path with
  | Value interface -> interface
  | Failed _ | Blocked -> None

let list_derived_methods (names : Names.lookups) package =
  List.concat_map
    (fun (((trait : Path.t), _), (impl : Path.t)) ->
      match (impl, names.key trait) with
      | Derived _, Some trait_key ->
          List.filter_map
            (fun (member : Names.key) ->
              match member.path with
              | Method { name; receiver; _ } -> Some (Path.Method { owner = impl; name; receiver })
              | _ -> None)
            (names.contained trait_key)
      | _ -> [])
    (names.impls package)

let package_parts database (names : Names.lookups) package : Part.computed list =
  let package_database = owner database package in
  let declarations = names.package_declarations package in
  let paths = List.map (fun (declaration : Names.declaration) -> declaration.path) declarations in
  let of_declaration (declaration : Names.declaration) : Part.computed list =
    let key = Names.key_of declaration in
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
        Used_packages key;
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
      (names.impls package)
  @ List.concat_map
      (fun path -> [ Part.Derived_form path; Generated_mir path ])
      (list_derived_methods names package)
  @ List.concat_map
      (fun path -> [ Part.Call_edges path; Callees (path, package) ])
      (List.sort_uniq Path.compare paths)
  @ List.map
      (fun dependency -> Part.Grant (package, dependency))
      (List.sort_uniq Path.compare_package (names.dependency_names package))
  @ List.map (fun file -> Part.Import_check file) package_database.files
  @ List.map
      (fun check -> Part.Package_check (package, check))
      (Package_checks.list_checks declarations)

let checked_body database note key =
  read_part database note (fun key -> Part.Checked_body key) (fun owner -> owner.checked_bodies) key

let checked_core database note key = (checked_body database note key).form

let infer_lookups database note : Infer.Lookups.t =
  {
    interface = interface_lookups database note ~is_checked:true;
    contract = read_part database note (fun key -> Part.Contract key) (fun owner -> owner.contracts);
  }

let type_check run lookups key =
  match run lookups key with
  | Ok checked -> Value checked
  | Error [] -> Blocked
  | Error diagnostics -> Failed diagnostics
  | exception Reads_failed_part -> Blocked

let form_origin database note =
  Infer.form_origin (interface_lookups database note ~is_checked:true) ~is_derived:(fun path ->
      read database note (Derived_form path);
      Path_table.mem (owner database (Path.package path)).derived_forms path)

let body_mir database note =
  read_part database note (fun key -> Part.Body_mir key) (fun owner -> owner.body_parts)

let mir_lookups database note : Mir.lookups =
  {
    form_origin = form_origin database note;
    body_part = body_mir database note;
    contract_part =
      read_part database note (fun key -> Part.Contract_mir key) (fun owner -> owner.contract_parts);
    generated_parts =
      (fun path ->
        read database note (Generated_mir path);
        match Path_table.find_opt (owner database (Path.package path)).generated_parts path with
        | Some (Value parts) -> parts
        | Some (Failed _ | Blocked) -> raise Reads_failed_part
        | None -> unchecked (Generated_mir path));
  }

let call_edge_lookups database note : Mir.Call_edges.lookups =
  { interface = interface_lookups database note ~is_checked:true; mir = mir_lookups database note }

let read_call_edges database note path =
  read database note (Call_edges path);
  match Path_table.find_opt (owner database (Path.package path)).call_edges path with
  | Some part -> part
  | None -> Blocked

let patterns_lookups database note : Patterns.Lookups.t =
  {
    core = checked_core database note;
    interface = interface_lookups database note ~is_checked:true;
  }

let usage_lookups database note : Usage.Lookups.t =
  {
    names = recording_names database note;
    resolved = read_whole_resolution database note;
    tables = (fun key -> (checked_body database note key).tables);
  }

let ownership_lookups database note : Ownership.Lookups.t =
  {
    graph = (fun key -> Mir.graph (body_mir database note key));
    interface = interface_lookups database note ~is_checked:true;
  }

let used_packages database note (key : Names.key) =
  let { Infer.form; evidence_packages; _ } = checked_body database note key in
  Package_checks.list_used_packages
    (read_whole_resolution database note key)
    ~evidence_packages form

let package_checks_lookups database note : Package_checks.Lookups.t =
  {
    interface = interface_lookups database note ~is_checked:true;
    core = checked_core database note;
    used_packages =
      read_part database note (fun key -> Part.Used_packages key) (fun owner -> owner.used_packages);
  }

let used_imports database note file =
  note (Part.Name (File_declarations file));
  let used =
    List.concat_map
      (fun key ->
        List.map
          (fun section ->
            match resolved_part database note section key with
            | Value resolved -> Some resolved.used_imports
            | Failed _ | Blocked -> None)
          Resolve.sections)
      (file_keys database file)
  in
  if List.for_all Option.is_some used then Some (List.concat_map Option.get used) else None

let import_diagnostics database note (file : Path.file) =
  read database note (Parsed file);
  note (Part.Input (Source file));
  Resolve.file_diagnostics (recording_names database note) file (parsed_file database file).tree
    ~text:(Source.text (source database file))
    ~used:(used_imports database note file)

let list_callees database note ~viewer path =
  match read_call_edges database note path with
  | Failed _ | Blocked -> None
  | Value call_edges -> (
      match Mir.Call_edges.list_implementations (call_edge_lookups database note) ~viewer path with
      | implementations -> Some (List.sort_uniq Path.compare (call_edges @ implementations))
      | exception Reads_failed_part -> None)

let recursion_group database note path =
  note (Part.Stored (Recursion_group path));
  match Path_table.find_opt (owner database (Path.package path)).recursion_groups path with
  | Some (Value members) -> members
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> []

let proof_lookups database note : Prover.Lookups.t =
  {
    source =
      (fun file ->
        note (Part.Input (Source file));
        source database file);
    interface = interface_lookups database note ~is_checked:true;
    mir = mir_lookups database note;
    patterns = read_part database note (fun key -> Part.Patterns key) (fun owner -> owner.patterns);
    must_be_disjoint =
      read_part database note (fun key -> Part.Ownership key) (fun owner -> owner.ownership);
    recursion_group = recursion_group database note;
  }

let stage_lowering_lookups database note : Compile.Lookups.t =
  { interface = interface_lookups database note ~is_checked:true; mir = mir_lookups database note }

let instance_part database note table part instance =
  read database note (Lowering part);
  match Instance_table.find_opt table instance with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> unchecked (Lowering part)

let lowered database note key = instance_part database note database.lowered (Lowered key) key
let test_key database note key = instance_part database note database.test_keys (Test_key key) key

let instance_slot table instance =
  {
    stored = Instance_table.find_opt table instance;
    replace = Instance_table.replace table instance;
    remove = (fun () -> Instance_table.remove table instance);
  }

exception Reaches_unsupported of Compile.unsupported

let compute_test_keys database keys =
  let outcome =
    computing database
      (List.map (fun key -> Part.Lowering (Test_key key)) keys)
      (fun note ->
        let supported = function
          | Ok value -> value
          | Error unsupported -> raise (Reaches_unsupported unsupported)
        in
        match
          Compile.test_keys
            ~lowered:(fun key -> supported (lowered database note key))
            ~known:(fun key -> supported (test_key database note key))
            keys
        with
        | test_keys -> Value (Ok test_keys)
        | exception Reaches_unsupported unsupported -> Value (Error unsupported)
        | exception Reads_failed_part -> Blocked)
  in
  List.iter
    (fun key ->
      let part = Part.Lowering (Test_key key) in
      database.observe (Recomputed (Computed part));
      store database (Computed part)
        (instance_slot database.test_keys key)
        (Some
           (match outcome with
           | Value (Ok test_keys) -> Value (Ok (List.assoc key test_keys))
           | Value (Error unsupported) -> Value (Error unsupported)
           | Failed _ | Blocked -> Blocked)))
    keys

type stored = {
  is_failed : bool;
  remove : unit -> unit;
  is_equal_in : t -> bool;
  saved : unit -> string option;
  restore : string -> unit;
}

let marshalled value = Marshal.to_string value []

let stored database (part : Part.stored) =
  let package =
    match part with Computed part -> Part.package part | Recursion_group path -> Path.package path
  in
  let package_database = owner database package in
  let failed = function Failed _ -> true | Value _ | Blocked -> false in
  let never _ = false in
  let keyed ~is_failed select key =
    let table = select package_database in
    {
      is_failed = Option.fold ~none:false ~some:is_failed (Hashtbl.find_opt table key);
      remove = (fun () -> Hashtbl.remove table key);
      is_equal_in =
        (fun other ->
          compare (Hashtbl.find_opt (select (owner other package)) key) (Hashtbl.find_opt table key)
          = 0);
      saved = (fun () -> Option.map marshalled (Hashtbl.find_opt table key));
      restore = (fun bytes -> Hashtbl.replace table key (Marshal.from_string bytes 0));
    }
  in
  let at_path ~is_failed select path =
    let table = select package_database in
    {
      is_failed = Option.fold ~none:false ~some:is_failed (Path_table.find_opt table path);
      remove = (fun () -> Path_table.remove table path);
      is_equal_in =
        (fun other ->
          compare
            (Path_table.find_opt (select (owner other package)) path)
            (Path_table.find_opt table path)
          = 0);
      saved = (fun () -> Option.map marshalled (Path_table.find_opt table path));
      restore = (fun bytes -> Path_table.replace table path (Marshal.from_string bytes 0));
    }
  in
  let of_instance select instance =
    let find database = Instance_table.find_opt (select database) instance in
    {
      is_failed = Option.fold ~none:false ~some:failed (find database);
      remove = (fun () -> Instance_table.remove (select database) instance);
      is_equal_in = (fun other -> compare (find other) (find database) = 0);
      saved = (fun () -> Option.map marshalled (find database));
      restore =
        (fun bytes ->
          Instance_table.replace (select database) instance (Marshal.from_string bytes 0));
    }
  in
  match part with
  | Recursion_group path ->
      at_path ~is_failed:failed (fun package_database -> package_database.recursion_groups) path
  | Computed part -> (
      match part with
      | Parsed file -> keyed ~is_failed:never (fun package_database -> package_database.parsed) file
      | Namespace _ ->
          {
            is_failed = false;
            remove = (fun () -> package_database.namespace <- None);
            is_equal_in =
              (fun other -> compare (owner other package).namespace package_database.namespace = 0);
            saved = (fun () -> None);
            restore = ignore;
          }
      | Resolved (key, section) ->
          keyed ~is_failed:failed
            (fun package_database -> package_database.resolved_names)
            (key, section)
      | Import_check file ->
          keyed ~is_failed:never (fun package_database -> package_database.import_checks) file
      | Trait_header key ->
          keyed ~is_failed:failed (fun package_database -> package_database.trait_headers) key
      | Constant_value path ->
          at_path ~is_failed:failed (fun package_database -> package_database.constant_values) path
      | Header key -> keyed ~is_failed:failed (fun package_database -> package_database.headers) key
      | Interface key ->
          keyed ~is_failed:failed (fun package_database -> package_database.interfaces) key
      | Derived_interface { type_; trait } ->
          keyed ~is_failed:failed
            (fun package_database -> package_database.derived_interfaces)
            (type_, trait)
      | Type_facts path ->
          at_path ~is_failed:failed (fun package_database -> package_database.type_facts) path
      | Grant (_, dependency) ->
          keyed ~is_failed:never (fun package_database -> package_database.grants) dependency
      | Signature_check key ->
          keyed ~is_failed:failed (fun package_database -> package_database.signature_checks) key
      | Contract key ->
          keyed ~is_failed:failed (fun package_database -> package_database.contracts) key
      | Checked_body key ->
          keyed ~is_failed:failed (fun package_database -> package_database.checked_bodies) key
      | Derived_form path ->
          at_path ~is_failed:failed (fun package_database -> package_database.derived_forms) path
      | Body_mir key ->
          keyed ~is_failed:failed (fun package_database -> package_database.body_parts) key
      | Contract_mir key ->
          keyed ~is_failed:failed (fun package_database -> package_database.contract_parts) key
      | Generated_mir path ->
          at_path ~is_failed:failed (fun package_database -> package_database.generated_parts) path
      | Call_edges path ->
          at_path ~is_failed:failed (fun package_database -> package_database.call_edges) path
      | Patterns key ->
          keyed ~is_failed:failed (fun package_database -> package_database.patterns) key
      | Usage key -> keyed ~is_failed:failed (fun package_database -> package_database.usage) key
      | Ownership key ->
          keyed ~is_failed:failed (fun package_database -> package_database.ownership) key
      | Used_packages key ->
          keyed ~is_failed:failed (fun package_database -> package_database.used_packages) key
      | Package_check (_, check) ->
          keyed ~is_failed:failed (fun package_database -> package_database.package_checks) check
      | Callees (path, viewer) ->
          let callees database =
            Option.bind (Hashtbl.find_opt database.graphs viewer) (fun graph ->
                Call_graph.successors graph path)
          in
          {
            is_failed = false;
            remove = (fun () -> Call_graph.remove_successors (call_graph database viewer) path);
            is_equal_in = (fun other -> callees other = callees database);
            saved = (fun () -> Option.map marshalled (callees database));
            restore =
              (fun bytes ->
                ignore
                  (Call_graph.set_successors (call_graph database viewer) path
                     (Marshal.from_string bytes 0)));
          }
      | Proof key -> keyed ~is_failed:failed (fun package_database -> package_database.proofs) key
      | Lowering (Lowered key) -> of_instance (fun database -> database.lowered) key
      | Lowering (Test_key key) -> of_instance (fun database -> database.test_keys) key)

let discard database part =
  unmark database part;
  record database [ part ] (Part_table.create 0);
  Computed_table.remove database.reads part;
  mark_unsaved database (Reads part)

let instance_parts key : Part.lowering list = [ Lowered key; Test_key key ]

let is_stored database (part : Part.lowering) =
  match part with
  | Lowered key -> Instance_table.mem database.lowered key
  | Test_key key -> Instance_table.mem database.test_keys key

let is_created database part = is_stale database (Lowering part) || is_stored database part
let is_current database part = (not (is_stale database (Lowering part))) && is_stored database part

let create_instance database key =
  List.iter
    (fun part -> if not (is_created database part) then mark_stale database (Lowering part))
    (instance_parts key)

let rec sorted_difference compare left right =
  match (left, right) with
  | [], _ -> []
  | left, [] -> left
  | item :: rest, other :: others ->
      let order = compare item other in
      if order = 0 then sorted_difference compare rest others
      else if order < 0 then item :: sorted_difference compare rest right
      else sorted_difference compare left others

let rec forget database parts =
  let removed = Computed_table.create 16 in
  List.iter (fun part -> Computed_table.replace removed part ()) parts;
  List.iter
    (fun part ->
      (stored database (Computed part)).remove ();
      mark_unsaved database (Value (Computed part));
      discard database part)
    parts;
  let is_kept reader = not (Computed_table.mem removed reader) in
  List.iter (fun part -> mark_readers ~only:is_kept database (Stored (Computed part))) parts;
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
    let owners root = Option.value (Instance_table.find_opt database.owners root) ~default:[] in
    List.iter
      (fun root ->
        match List.filter (fun other -> other <> owner) (owners root) with
        | [] ->
            Instance_table.remove database.owners root;
            References.remove_root database.references root
        | others -> Instance_table.replace database.owners root others)
      (sorted_difference Instance.compare before roots);
    List.iter
      (fun root ->
        Instance_table.replace database.owners root (owner :: owners root);
        if References.add_root database.references root then create_instance database root)
      (sorted_difference Instance.compare roots before);
    settle_references database
  end

and settle_references database =
  if References.has_changes database.references then
    collect database (References.update database.references).removed

and collect database keys =
  let parts = List.concat_map instance_parts keys in
  List.iter (fun part -> database.observe (Collected part)) parts;
  forget database (List.map (fun part -> Part.Lowering part) parts)

let list_lowered_references database key =
  match Instance_table.find_opt database.lowered key with
  | Some (Value (Ok lowered)) -> Compile.references lowered
  | Some (Value (Error _) | Failed _ | Blocked) | None -> []

let list_instance_edges database key =
  List.sort_uniq Instance.compare (list_lowered_references database key)

let update_references database key =
  let edges = list_instance_edges database key in
  if References.successors database.references key <> Some (Some edges) then begin
    List.iter (create_instance database)
      (References.set_successors database.references key (Some edges));
    settle_references database
  end

let list_current_edges database key =
  if is_stale database (Lowering (Lowered key)) then [] else list_lowered_references database key

let list_ready_instances database =
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

let lowering_settings database =
  match database.lowering with
  | Some settings -> settings
  | None -> Compiler_bug.bug ~stage:"Database" "this host has no lowering settings"

let proof_template_checks database (key : Names.key) =
  match Hashtbl.find_opt (owner database key.module_.package).proofs key with
  | Some (Value (Obligations { obligations; _ })) ->
      List.filter_map
        (fun (obligation : Prover.State.obligation) ->
          Option.map
            (fun (template_clause : Prover.State.template_clause) -> template_clause.check)
            obligation.template_clause)
        obligations
  | Some (Value (Unsupported _ | Not_proven_here) | Failed _ | Blocked) | None -> []

let template_check_root ({ from_template; literals; clauses } : Prover.State.template_check) =
  Instance.Template_check { from_template; literals; clauses }

let own_template_checks database (key : Names.key) =
  if Option.is_some database.lowering then
    own_roots database (Stored (Computed (Proof key)))
      (List.map template_check_root (proof_template_checks database key))

let entry_point (names : Names.lookups) package =
  List.find_map
    (fun (declaration : Names.declaration) ->
      match declaration.path with
      | Top { name = "main"; _ } when declaration.kind = Function && declaration.ordinal = 0 ->
          Some declaration.path
      | _ -> None)
    (names.declarations { package; modules = [] })

let own_lowering_roots database (names : Names.lookups) package =
  if Option.is_some database.lowering then
    own_roots database (Stored (Computed (Namespace package)))
      (Compile.roots
         ~tests:
           (List.filter_map
              (fun (declaration : Names.declaration) ->
                match declaration.path with Test _ -> Some declaration.path | _ -> None)
              (names.package_declarations package))
         ~mains:(Option.to_list (entry_point names package)))

let holds_position database (part : Part.computed) =
  match part with
  | Proof _ | Package_check _ | Lowering (Lowered _) -> true
  | _ -> (stored database (Computed part)).is_failed

let mark_change database package (change : Names.change) =
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
  | Positions _ -> mark_readers ~only:(holds_position database) database (Name part)
  | _ -> mark_readers database (Name part)

let is_own_namespace_part package (part : Part.t) =
  match part with
  | Name part -> Part.name_package part = package
  | Stored (Computed (Namespace namespace_package)) -> namespace_package = package
  | Input _ | Stored _ -> false

let namespace_and_implied database (package_database : package_database) =
  let package = package_database.name in
  let namespace, implied =
    computing database [ Part.Namespace package ] (fun note ->
        let note part = if not (is_own_namespace_part package part) then note part in
        let own_namespace = namespace_of database note package_database in
        let names =
          names_over database ~namespace:(fun name ->
              if name = package then own_namespace else namespace database name)
        in
        (own_namespace, package_parts database (recording names note) package))
  in
  package_database.namespace <- Some namespace;
  Hashtbl.replace database.implied package implied;
  (namespace, implied)

let compute_namespace database (package_database : package_database) =
  let package = package_database.name in
  let before = Option.value package_database.namespace ~default:Names.empty_namespace in
  let implied_before = Option.value ~default:[] (Hashtbl.find_opt database.implied package) in
  let after, implied = namespace_and_implied database package_database in
  let membership parts =
    let members = Computed_table.create 256 in
    List.iter (fun part -> Computed_table.replace members part ()) parts;
    Computed_table.mem members
  in
  let was_implied = membership implied_before and is_implied = membership implied in
  let graph = call_graph database package in
  List.iter
    (function
      | Part.Callees (root, _) as part when not (is_implied part) ->
          Call_graph.remove_root graph root
      | _ -> ())
    implied_before;
  List.iter
    (function
      | Part.Callees (root, _) as part when not (was_implied part) ->
          ignore (Call_graph.add_root graph root)
      | _ -> ())
    implied;
  List.iter (mark_change database package) (Names.changes before after);
  List.iter (fun part -> if not (was_implied part) then mark_stale database part) implied;
  forget database (List.filter (fun part -> not (is_implied part)) implied_before);
  own_lowering_roots database (names_lookups database) package

let compute_type_facts database paths =
  let facts =
    computing database
      (List.map (fun path -> Part.Type_facts path) paths)
      (fun note ->
        let lookups = interface_lookups database note ~is_checked:false in
        let interfaces = List.map (fun path -> (path, type_interface lookups path)) paths in
        if List.for_all (fun (_, interface) -> Option.is_some interface) interfaces then
          computed
            (Interface.Properties.component_facts lookups)
            (List.filter_map
               (fun (path, interface) -> Option.map (fun interface -> (path, interface)) interface)
               interfaces)
        else Blocked)
  in
  List.iter
    (fun path ->
      database.observe (Recomputed (Computed (Type_facts path)));
      store database (Computed (Type_facts path))
        (at_path (owner database (Path.package path)).type_facts path)
        (Some
           (match facts with
           | Value facts -> (
               match List.assoc_opt path facts with Some facts -> Value facts | None -> Blocked)
           | Failed _ | Blocked -> Blocked)))
    paths

let compute_part database (part : Part.computed) =
  database.observe (Recomputed (Computed part));
  let package_database = owner database (Part.package part) in
  let into slot compute = compute_into database part slot compute in
  match part with
  | Parsed file ->
      into (keyed package_database.parsed file) (fun note ->
          note (Input (Source file));
          let source = source database file in
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
      into
        (keyed package_database.resolved_names (key, section))
        (fun note ->
          Some
            (match Resolve.resolve (recording_names database note) key section with
            | Some (Ok resolved) -> Value resolved
            | Some (Error diagnostics) -> Failed diagnostics
            | None -> Blocked))
  | Import_check file ->
      into (keyed package_database.import_checks file) (fun note ->
          Some (import_diagnostics database note file))
  | Trait_header key ->
      into (keyed package_database.trait_headers key) (fun note ->
          Some
            (match
               ( (recording_names database note).definition key,
                 resolved_part database note Interface key )
             with
            | definition, Value resolved -> (
                match Resolve.trait_header definition resolved with
                | Some header -> Value header
                | None -> Blocked)
            | _, (Failed _ | Blocked) -> Blocked))
  | Constant_value path ->
      into (at_path package_database.constant_values path) (fun note ->
          Some
            (computed
               (Interface.Constants.value_of (interface_lookups database note ~is_checked:false))
               path))
  | Header key ->
      into (keyed package_database.headers key) (fun note ->
          Some
            (match
               computed
                 (Interface.Definition.header (interface_lookups database note ~is_checked:false))
                 key
             with
            | Value (Ok header) -> Value header
            | Value (Error (_ :: _ as diagnostics)) -> Failed diagnostics
            | Value (Error []) | Failed _ | Blocked -> Blocked))
  | Interface key ->
      into (keyed package_database.interfaces key) (fun note ->
          Some
            (match
               computed
                 (Interface.Definition.lower (interface_lookups database note ~is_checked:false))
                 key
             with
            | Value lowered -> interface_part lowered
            | Failed _ | Blocked -> Blocked))
  | Derived_interface { type_; trait } ->
      into
        (keyed package_database.derived_interfaces (type_, trait))
        (fun note ->
          Some
            (match
               computed
                 (fun trait ->
                   Interface.Impls.derived_interface
                     (interface_lookups database note ~is_checked:false)
                     ~type_ ~trait)
                 trait
             with
            | Value (Some interface) -> Value interface
            | Value None | Failed _ | Blocked -> Blocked))
  | Type_facts path -> compute_type_facts database [ path ]
  | Grant (package, dependency) ->
      let entry =
        List.find
          (fun (entry : Manifest.dependency) -> entry.package = dependency)
          package_database.dependencies
      in
      into (keyed package_database.grants dependency) (fun note ->
          note (Input (Dependencies package));
          Some
            (Interface.Grants.resolve_grant
               (interface_lookups database note ~is_checked:false)
               ~package entry.capabilities))
  | Signature_check key ->
      into (keyed package_database.signature_checks key) (fun note ->
          read database note (Interface key);
          Some
            (match Hashtbl.find_opt package_database.interfaces key with
            | Some (Value _) ->
                checked_part
                  (fun key ->
                    ( Interface.Check.diagnostics
                        (interface_lookups database note ~is_checked:false)
                        key,
                      () ))
                  key
            | Some (Failed _ | Blocked) -> Blocked
            | None -> unchecked (Interface key)))
  | Contract key ->
      into (keyed package_database.contracts key) (fun note ->
          Some
            (match type_check Infer.contract (infer_lookups database note) key with
            | Value (checked : Infer.checked) -> Value checked.form
            | Failed diagnostics -> Failed diagnostics
            | Blocked -> Blocked))
  | Checked_body key ->
      into (keyed package_database.checked_bodies key) (fun note ->
          Some (type_check Infer.body (infer_lookups database note) key))
  | Derived_form path ->
      into (at_path package_database.derived_forms path) (fun note ->
          match Infer.derived (infer_lookups database note) path with
          | Some form -> Some (Value form)
          | None -> None
          | exception Reads_failed_part -> Some Blocked)
  | Body_mir key ->
      into (keyed package_database.body_parts key) (fun note ->
          read database note (Checked_body key);
          Some
            (match Hashtbl.find_opt package_database.checked_bodies key with
            | Some (Value checked) -> (
                match lowered_interface database note ~is_checked:true key with
                | lowered -> Value (Mir.body_part ~interface:lowered.interface checked.form)
                | exception Reads_failed_part -> Blocked)
            | Some (Failed _ | Blocked) -> Blocked
            | None -> unchecked (Checked_body key)))
  | Contract_mir key ->
      into (keyed package_database.contract_parts key) (fun note ->
          read database note (Contract key);
          Some
            (match Hashtbl.find_opt package_database.contracts key with
            | Some (Value form) ->
                Value
                  (Mir.contract_part
                     ~type_interface:
                       (Interface.Definition.type_interface
                          (interface_lookups database note ~is_checked:true))
                     key.path form)
            | Some (Failed _ | Blocked) -> Blocked
            | None -> unchecked (Contract key)))
  | Generated_mir path ->
      into (at_path package_database.generated_parts path) (fun note ->
          read database note (Derived_form path);
          Option.map
            (function
              | Value form ->
                  Value
                    ( Mir.body_part form,
                      Mir.contract_part
                        ~type_interface:
                          (Interface.Definition.type_interface
                             (interface_lookups database note ~is_checked:true))
                        path form )
              | Failed _ | Blocked -> Blocked)
            (Path_table.find_opt package_database.derived_forms path))
  | Call_edges path ->
      into (at_path package_database.call_edges path) (fun note ->
          Some (computed (Mir.Call_edges.of_path (call_edge_lookups database note)) path))
  | Patterns key ->
      into (keyed package_database.patterns key) (fun note ->
          Some
            (checked_part
               (fun key -> (Patterns.check (patterns_lookups database note) key, ()))
               key))
  | Usage key ->
      into (keyed package_database.usage key) (fun note ->
          Some (checked_part (fun key -> (Usage.check (usage_lookups database note) key, ())) key))
  | Ownership key ->
      into (keyed package_database.ownership key) (fun note ->
          Some
            (checked_part
               (fun key ->
                 let result = Ownership.check (ownership_lookups database note) key in
                 (result.diagnostics, result.must_be_disjoint))
               key))
  | Used_packages key ->
      into (keyed package_database.used_packages key) (fun note ->
          Some (computed (used_packages database note) key))
  | Package_check (package, check) ->
      into (keyed package_database.package_checks check) (fun note ->
          Some (computed (Package_checks.run (package_checks_lookups database note) package) check))
  | Callees (path, viewer) ->
      let graph = call_graph database viewer in
      into
        {
          stored = Call_graph.successors graph path;
          replace =
            (fun callees ->
              List.iter
                (fun node -> mark_stale database (Callees (node, viewer)))
                (Call_graph.set_successors graph path callees));
          remove = (fun () -> Call_graph.remove_successors graph path);
        }
        (fun note -> Some (list_callees database note ~viewer path))
  | Proof key ->
      into (keyed package_database.proofs key) (fun note ->
          Some (computed (Prover.proof (proof_lookups database note)) key));
      own_template_checks database key
  | Lowering (Lowered key) ->
      into (instance_slot database.lowered key) (fun note ->
          Some
            (match
               Compile.lower (lowering_settings database) (stage_lowering_lookups database note) key
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

let compute database = function
  | Single part -> compute_part database part
  | Type_fact_component paths -> compute_type_facts database paths
  | Test_key_component keys -> compute_test_keys database keys

let list_components database (stage : Stage.t) package parts =
  match stage with
  | Type_facts ->
      let paths =
        List.filter_map (function Part.Type_facts path -> Some path | _ -> None) parts
      in
      let in_closure = Path_table.create 64 in
      List.iter (fun path -> Path_table.replace in_closure path ()) paths;
      let lookups = interface_lookups database ignore ~is_checked:false in
      List.map
        (fun paths -> Type_fact_component paths)
        (Strongly_connected.find_components
           (module Path)
           ~successors:(fun path ->
             match type_interface lookups path with
             | Some interface ->
                 List.filter (Path_table.mem in_closure)
                   (Interface.Properties.fields_named ~package interface)
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
    (Strongly_connected.find_components
       (module Instance_key)
       ~successors:(fun key ->
         match Instance_table.find_opt database.lowered key with
         | Some (Value (Ok lowered)) ->
             List.filter (Instance_table.mem in_closure) (Compile.references lowered)
         | Some (Value (Error _) | Failed _ | Blocked) | None -> [])
       keys)

let update_groups database package =
  match Hashtbl.find_opt database.graphs package with
  | Some graph when Call_graph.has_changes graph ->
      let { Call_graph.touched; removed } = Call_graph.update graph in
      List.iter
        (fun node ->
          let part = Part.Callees (node, package) in
          mark_unsaved database (Value (Computed part));
          discard database part)
        removed;
      let groups = at_path (owner database package).recursion_groups in
      let is_own node = Path.package node = package in
      List.iter
        (fun node ->
          if is_own node then begin
            database.observe (Recomputed (Recursion_group node));
            store database (Recursion_group node) (groups node)
              (match Call_graph.group graph node with
              | Blocked -> Some Blocked
              | Members [] -> None
              | Members members -> Some (Value members))
          end)
        touched;
      List.iter
        (fun node -> if is_own node then store database (Recursion_group node) (groups node) None)
        removed
  | Some _ | None -> ()

let has_work database package (stage : Stage.t) =
  match stage with
  | Recursion_groups -> (
      match Hashtbl.find_opt database.graphs package with
      | Some graph -> Call_graph.has_changes graph
      | None -> false)
  | stage -> (
      match Hashtbl.find_opt database.stale (package, stage) with
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
                   && List.mem (Part.package reader) packages
                   && is_drained reader
                 then close reader))
            (Part_table.find_opt database.readers (Stored (Computed part)))
        end
      in
      List.iter
        (fun package ->
          List.iter close (List.filter is_drained (stale_parts database package stage)))
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
      let parts_where keep =
        Computed_table.fold
          (fun part () parts -> if keep part then part :: parts else parts)
          closure []
      in
      let all_parts () = parts_where (fun _ -> true) in
      match stage with
      | Lowered_code -> compute_components (List.map (fun part -> Single part) (all_parts ()))
      | Test_keys -> compute_components (list_test_key_components database (all_parts ()))
      | stage ->
          List.iter
            (fun package ->
              compute_components
                (list_components database stage package
                   (parts_where (fun part -> Part.package part = package))))
            packages)

let drain_where ?on_bug database ~drains requested =
  let packages = in_dependency_order database requested in
  let broken = Computed_table.create 0 in
  let on_raise parts raised =
    match (on_bug, raised) with
    | Some on_bug, Compiler_bug.Bug bug ->
        List.iter (fun part -> Computed_table.replace broken part ()) parts;
        on_bug bug
    | _ -> raise raised
  in
  let rec next () =
    let ready = lazy (list_ready_instances database) in
    let is_drained part = is_drained ~ready part && not (Computed_table.mem broken part) in
    let has_drained_work stage =
      List.exists
        (fun package ->
          has_work database package stage
          && ((Computed_table.length broken = 0 && not (Stage.is_lowering stage))
             || List.exists is_drained (stale_parts database package stage)))
        packages
    in
    match List.find_opt (fun stage -> drains stage && has_drained_work stage) Stage.all with
    | Some stage ->
        drain_stage database ~is_drained ~on_raise stage packages;
        next ()
    | None -> ()
  in
  next ()

let drain database ~through requested =
  drain_where database ~drains:(Stage.drains ~through) requested

let propagate ?on_bug database =
  drain_where ?on_bug database ~drains:(fun _ -> true) database.project

type read = { dependent : Part.t; dependency : Part.t }

let definition_set paths =
  let set = Path_table.create 8 in
  List.iter (fun path -> Path_table.replace set path ()) paths;
  set

let is_of_other definition part =
  match Part.definition part with Some other -> not (Path.equal other definition) | None -> false

let drain_checks database = drain database ~through:Proofs database.project
let is_checked part = not (Stage.is_lowering (Stage.of_part part))

let list_dependencies database paths =
  drain_checks database;
  let wanted = definition_set paths in
  Computed_table.fold
    (fun dependent dependencies found ->
      let dependent_part = Part.Stored (Computed dependent) in
      match Part.definition dependent_part with
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
  let wanted = definition_set paths in
  Part_table.fold
    (fun dependency readers found ->
      match Part.definition dependency with
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
        if Option.is_some (Part.definition (Stored part)) then Stored_table.replace parts part ()
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
            (owner database package).recursion_groups)
        database.project)
    [ database; other ];
  Stored_table.fold
    (fun part () changed ->
      if (stored database part).is_equal_in other then changed else Part.Stored part :: changed)
    parts []

let update database changes =
  List.iter
    (fun ((file : Path.file), text) ->
      let package = file.module_.package in
      let package_database =
        match Hashtbl.find_opt database.package_databases package with
        | Some package_database -> package_database
        | None ->
            Compiler_bug.bug ~stage:"Database" "%s is not a package of the build"
              (Path.show_package package)
      in
      let previous = Hashtbl.find_opt package_database.sources file in
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
            Hashtbl.replace package_database.sources file (source_of file text);
            mark_stale database (Parsed file)
        | None ->
            Hashtbl.remove package_database.sources file;
            forget database [ Parsed file ]);
        mark_readers database (Input (Source file));
        if Option.is_none previous || Option.is_none text then begin
          let modules = package_database.modules in
          list_files package_database
            (List.filter (( <> ) file) package_database.files
            @ if Option.is_some text then [ file ] else []);
          if modules <> package_database.modules then
            mark_readers database (Input (Modules package));
          mark_stale database (Namespace package)
        end
      end)
    changes

let list_stored_parts (package_database : package_database) : Part.stored list =
  let keyed table part = Hashtbl.fold (fun key _ parts -> part key :: parts) table [] in
  let at_paths table part = Path_table.fold (fun path _ parts -> part path :: parts) table [] in
  at_paths package_database.recursion_groups (fun path -> Part.Recursion_group path)
  @ List.map
      (fun part -> Part.Computed part)
      (List.concat
         [
           keyed package_database.parsed (fun file -> Part.Parsed file);
           keyed package_database.resolved_names (fun (key, section) ->
               Part.Resolved (key, section));
           keyed package_database.import_checks (fun file -> Part.Import_check file);
           keyed package_database.trait_headers (fun key -> Part.Trait_header key);
           at_paths package_database.constant_values (fun path -> Part.Constant_value path);
           keyed package_database.headers (fun key -> Part.Header key);
           keyed package_database.interfaces (fun key -> Part.Interface key);
           keyed package_database.derived_interfaces (fun (type_, trait) ->
               Part.Derived_interface { type_; trait });
           at_paths package_database.type_facts (fun path -> Part.Type_facts path);
           keyed package_database.grants (fun dependency ->
               Part.Grant (package_database.name, dependency));
           keyed package_database.signature_checks (fun key -> Part.Signature_check key);
           keyed package_database.contracts (fun key -> Part.Contract key);
           keyed package_database.checked_bodies (fun key -> Part.Checked_body key);
           at_paths package_database.derived_forms (fun path -> Part.Derived_form path);
           keyed package_database.body_parts (fun key -> Part.Body_mir key);
           keyed package_database.contract_parts (fun key -> Part.Contract_mir key);
           at_paths package_database.generated_parts (fun path -> Part.Generated_mir path);
           at_paths package_database.call_edges (fun path -> Part.Call_edges path);
           keyed package_database.patterns (fun key -> Part.Patterns key);
           keyed package_database.usage (fun key -> Part.Usage key);
           keyed package_database.ownership (fun key -> Part.Ownership key);
           keyed package_database.used_packages (fun key -> Part.Used_packages key);
           keyed package_database.package_checks (fun check ->
               Part.Package_check (package_database.name, check));
           keyed package_database.proofs (fun key -> Part.Proof key);
         ])

let mark_differences database name ~(before : package_database option)
    ~(after : package_database option) =
  let empty () =
    let package_database = make_empty_package_database name ~dependencies:[] in
    package_database.namespace <- Some Names.empty_namespace;
    package_database
  in
  let before = match before with Some package_database -> package_database | None -> empty () in
  let after = match after with Some package_database -> package_database | None -> empty () in
  let namespace (package_database : package_database) =
    Option.value package_database.namespace ~default:Names.empty_namespace
  in
  List.iter (mark_change database name) (Names.changes (namespace before) (namespace after));
  let text (package_database : package_database) file =
    Option.map Source.text (Hashtbl.find_opt package_database.sources file)
  in
  List.iter
    (fun file ->
      if text before file <> text after file then mark_readers database (Input (Source file)))
    (List.sort_uniq compare (before.files @ after.files));
  if before.modules <> after.modules then mark_readers database (Input (Modules name));
  if before.dependencies <> after.dependencies then
    mark_readers database (Input (Dependencies name));
  let view (package_database : package_database) =
    let package_databases = Hashtbl.create 1 in
    Hashtbl.replace package_databases name package_database;
    { database with package_databases }
  in
  let parts = Stored_table.create 1024 in
  List.iter
    (fun part -> Stored_table.replace parts part ())
    (list_stored_parts before @ list_stored_parts after);
  Stored_table.iter
    (fun part () ->
      if not ((stored (view before) part).is_equal_in (view after)) then
        mark_readers database (Stored part))
    parts

let retire database (package_database : package_database) =
  let package = package_database.name in
  own_roots database (Stored (Computed (Namespace package))) [];
  Hashtbl.iter
    (fun key _ -> own_roots database (Stored (Computed (Proof key))) [])
    package_database.proofs;
  let is_own part = (not (Stage.is_lowering (Stage.of_part part))) && Part.package part = package in
  mark_package_database_unsaved database package_database;
  List.iter (fun part -> mark_unsaved database (Value part)) (list_stored_parts package_database);
  List.iter
    (fun part ->
      mark_unsaved database (Value (Computed part));
      discard database part)
    (Computed_table.fold
       (fun part _ parts -> if is_own part then part :: parts else parts)
       database.reads []);
  Hashtbl.filter_map_inplace
    (fun (owner, stage) parts ->
      if owner = package && not (Stage.is_lowering stage) then begin
        Computed_table.iter (fun part () -> mark_unsaved database (Stale part)) parts;
        None
      end
      else Some parts)
    database.stale;
  Hashtbl.remove database.graphs package;
  Hashtbl.remove database.implied package;
  Hashtbl.remove database.package_databases package

let relayout database ~(loaded : package_database list) (packages : Project.package list) =
  let project = List.map (fun (package : Project.package) -> package.name) packages in
  let loaded_as name =
    List.find_opt (fun (package_database : package_database) -> package_database.name = name) loaded
  in
  let names_before =
    Hashtbl.fold (fun name _ names -> name :: names) database.package_databases []
  in
  List.iter
    (fun name ->
      let before = Hashtbl.find database.package_databases name in
      let is_kept =
        if List.mem name database.project then List.mem name project
        else
          match loaded_as name with
          | Some package_database -> package_database == before
          | None -> false
      in
      if not is_kept then begin
        let after = if List.mem name project then None else loaded_as name in
        mark_differences database name ~before:(Some before) ~after;
        retire database before;
        Option.iter (Hashtbl.replace database.package_databases name) after
      end)
    names_before;
  List.iter
    (fun (package_database : package_database) ->
      if not (Hashtbl.mem database.package_databases package_database.name) then begin
        mark_differences database package_database.name ~before:None ~after:(Some package_database);
        Hashtbl.remove database.absent package_database.name;
        Hashtbl.replace database.package_databases package_database.name package_database
      end)
    loaded;
  List.iter
    (fun (package : Project.package) ->
      match Hashtbl.find_opt database.package_databases package.name with
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
          Hashtbl.remove database.absent package.name;
          Hashtbl.replace database.package_databases package.name package_database;
          mark_package_database_unsaved database package_database;
          mark_readers database (Input (Modules package.name));
          mark_readers database (Input (Dependencies package.name));
          List.iter (fun file -> mark_stale database (Parsed file)) package_database.files;
          mark_stale database (Namespace package.name))
    packages;
  let names_after =
    Hashtbl.fold (fun name _ names -> name :: names) database.package_databases []
  in
  if List.sort compare names_before <> List.sort compare names_after then
    mark_readers database (Input Packages);
  database.project <- project

let fingerprint text = Digest.BLAKE128.to_hex (Digest.BLAKE128.string text)

let is_saved_part database (part : Part.stored) =
  match part with
  | Computed (Namespace _) -> false
  | Computed (Lowering _) -> true
  | Computed part -> List.mem (Part.package part) database.project
  | Recursion_group path -> List.mem (Path.package path) database.project

let saved_value database (entry : Entry.t) =
  match entry with
  | Value part -> if is_saved_part database part then (stored database part).saved () else None
  | Reads part ->
      if is_saved_part database (Computed part) then
        Option.map marshalled (Computed_table.find_opt database.reads part)
      else None
  | Stale part ->
      if is_saved_part database (Computed part) && is_stale database part then Some "" else None
  | Package name ->
      if List.mem name database.project then
        Option.map
          (fun (package_database : package_database) -> marshalled package_database.dependencies)
          (package database name)
      else None
  | File file ->
      let name = file.module_.package in
      if List.mem name database.project then
        Option.bind (package database name) (fun (package_database : package_database) ->
            Option.map
              (fun source -> fingerprint (Source.text source))
              (Hashtbl.find_opt package_database.sources file))
      else None
  | Owned owner -> Option.map marshalled (Part_table.find_opt database.owned owner)

let list_unsaved database =
  drain database ~through:Namespaces database.project;
  List.iter (update_groups database) database.project;
  Entry_table.fold
    (fun entry () entries ->
      (Marshal.to_string entry [ No_sharing ], saved_value database entry) :: entries)
    database.unsaved []

let mark_saved database = Entry_table.reset database.unsaved

let restore_packages database ~texts entries =
  let files = Hashtbl.create 64 in
  List.iter
    (function
      | Entry.File (file : Path.file), saved ->
          let name = file.module_.package in
          Hashtbl.replace files name
            ((file, saved) :: Option.value ~default:[] (Hashtbl.find_opt files name))
      | _ -> ())
    entries;
  List.iter
    (function
      | Entry.Package name, dependencies ->
          let package_database =
            make_empty_package_database name ~dependencies:(Marshal.from_string dependencies 0)
          in
          let listed = Option.value ~default:[] (Hashtbl.find_opt files name) in
          List.iter
            (fun (file, saved) ->
              match texts file with
              | Some text when String.equal (fingerprint text) saved ->
                  Hashtbl.replace package_database.sources file (source_of file text)
              | Some _ | None -> ())
            listed;
          list_files package_database (List.map fst listed);
          Hashtbl.replace database.package_databases name package_database;
          database.project <- name :: database.project
      | _ -> ())
    entries;
  database.project <- List.sort Path.compare_package database.project

let restore_parts database entries =
  List.iter
    (fun ((entry : Entry.t), bytes) ->
      match entry with
      | Value part when is_saved_part database part -> (stored database part).restore bytes
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
        let _, implied =
          namespace_and_implied database (Hashtbl.find database.package_databases name)
        in
        let graph = call_graph database name in
        List.iter
          (function Part.Callees (root, _) -> ignore (Call_graph.add_root graph root) | _ -> ())
          implied
      end)
    (in_dependency_order database database.project)

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

let restore ~loaded ~texts entries =
  let database = create ~loaded [] in
  let entries =
    List.map (fun (key, value) -> ((Marshal.from_string key 0 : Entry.t), value)) entries
  in
  restore_packages database ~texts entries;
  restore_parts database entries;
  restore_namespaces database;
  restore_references database;
  List.iter (update_groups database) database.project;
  mark_saved database;
  database

type checker = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

let without_duplicates diagnostics =
  List.sort_uniq
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    diagnostics

let failed table key =
  match Hashtbl.find_opt table key with
  | Some (Failed diagnostics) -> diagnostics
  | Some (Value _ | Blocked) | None -> []

let definition_diagnostics database (key : Names.key) checker =
  let owner = owner database key.module_.package in
  match checker with
  | Resolve ->
      List.concat_map (fun section -> failed owner.resolved_names (key, section)) Resolve.sections
  | Interface ->
      without_duplicates
        (failed owner.headers key @ failed owner.interfaces key @ failed owner.signature_checks key)
  | Infer -> failed owner.contracts key @ failed owner.checked_bodies key
  | Patterns -> failed owner.patterns key
  | Usage -> failed owner.usage key
  | Ownership -> failed owner.ownership key
  | Package_checks -> []

let by_span_and_code diagnostics =
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    diagnostics

let list_package_outcomes database package =
  let package_checks = (owner database package).package_checks in
  List.filter_map
    (fun check ->
      match Hashtbl.find_opt package_checks check with
      | Some (Value outcome) -> Some outcome
      | Some (Failed _ | Blocked) | None -> None)
    (Package_checks.list_checks ((names_lookups database).package_declarations package))

let list_checker_diagnostics database (file : Path.file) checker =
  let names = names_lookups database in
  let package_database = owner database file.module_.package in
  let placed key diagnostics =
    let ({ file = home; base } : Names.place) = names.place key in
    if home = file then
      List.map (Diagnostic.map_spans (Source.Definition_span.to_file ~base)) diagnostics
    else []
  in
  let of_definitions () =
    List.concat_map
      (fun key -> placed key (definition_diagnostics database key checker))
      (file_keys database file)
  in
  by_span_and_code
    (match checker with
    | Resolve ->
        Option.value ~default:[] (Hashtbl.find_opt package_database.import_checks file)
        @ of_definitions ()
    | Package_checks ->
        List.concat_map
          (function
            | Package_checks.Placed diagnostics ->
                List.concat_map
                  (fun (diagnostic : Package_checks.placed) ->
                    placed diagnostic.key [ diagnostic.diagnostic ])
                  diagnostics
            | Unused_dependencies _ -> [])
          (list_package_outcomes database file.module_.package)
    | Interface | Infer | Patterns | Usage | Ownership -> of_definitions ())

let checkers = [ Resolve; Interface; Infer; Patterns; Usage; Ownership; Package_checks ]
let check database packages = drain database ~through:Package_checks packages

let read_checked_body database (key : Names.key) =
  drain database ~through:Checked_bodies [ key.module_.package ];
  match Hashtbl.find_opt (owner database key.module_.package).checked_bodies key with
  | Some (Value checked) -> Some checked
  | Some (Failed _ | Blocked) | None -> None

let list_file_diagnostics database (file : Path.file) =
  drain database ~through:Package_checks [ file.module_.package ];
  without_duplicates
    ((parsed_file database file).diagnostics
    @ List.concat_map (list_checker_diagnostics database file) checkers)

type manifest_problem =
  | Not_a_capability of { dependency : Path.package; name : string }
  | Unused_dependency of Path.package

let list_manifest_problems database package =
  drain database ~through:Package_checks [ package ];
  let grants = (owner database package).grants in
  List.concat_map
    (fun dependency ->
      match Hashtbl.find_opt grants dependency with
      | Some (grant : Environment.grant) ->
          List.map (fun name -> Not_a_capability { dependency; name }) grant.unknown
      | None -> unchecked (Grant (package, dependency)))
    ((names_lookups database).dependency_names package)
  @ List.concat_map
      (function
        | Package_checks.Unused_dependencies dependencies ->
            List.map (fun dependency -> Unused_dependency dependency) dependencies
        | Placed _ -> [])
      (list_package_outcomes database package)

let list_code_packages database package =
  drain database ~through:Body_checks [ package ];
  let used_packages = (owner database package).used_packages in
  let read_used (declaration : Names.declaration) =
    match declaration.path with
    | Test _ -> Some []
    | _ -> (
        let key = Names.key_of declaration in
        match Hashtbl.find_opt used_packages key with
        | Some (Value used) -> Some used
        | Some (Failed _ | Blocked) -> None
        | None -> unchecked (Used_packages key))
  in
  let used = List.map read_used ((names_lookups database).package_declarations package) in
  if List.mem None used then None
  else Some (List.sort_uniq Path.compare_package (List.concat_map Option.get used))

let read_package_database database package =
  drain database ~through:Recursion_groups [ package ];
  match Hashtbl.find_opt database.package_databases package with
  | Some package_database -> package_database
  | None ->
      Compiler_bug.bug ~stage:"Database" "%s is not a package of the build"
        (Path.show_package package)

type proofs = { database : t; keys : Names.key list }

let prove database files =
  let packages =
    List.sort_uniq Path.compare_package
      (List.map (fun (file : Path.file) -> file.module_.package) files)
  in
  drain database ~through:Recursion_groups packages;
  let keys = List.concat_map (file_keys database) files in
  List.iter
    (fun (key : Names.key) ->
      let part = Part.Proof key in
      if is_stale database part || not (Hashtbl.mem (owner database key.module_.package).proofs key)
      then begin
        unmark database part;
        compute_part database part
      end
      else own_template_checks database key)
    keys;
  { database; keys }

let read_proof proofs (key : Names.key) =
  Hashtbl.find_opt (owner proofs.database key.module_.package).proofs key

let list_holes proofs path =
  let names = names_lookups proofs.database in
  match Option.bind (names.key path) (read_proof proofs) with
  | Some (Value (Obligations { holes; _ })) ->
      List.map
        (fun ((home : Names.key), (span : Source.Definition_span.t)) ->
          let ({ file; base } : Names.place) = names.place home in
          (file, (Source.Definition_span.to_file ~base span).start))
        holes
  | Some (Value (Unsupported _ | Not_proven_here) | Failed _ | Blocked) | None -> []

let list_template_checks (proofs : proofs) =
  let database = proofs.database in
  match List.sort_uniq compare (List.concat_map (proof_template_checks database) proofs.keys) with
  | [] -> []
  | checks ->
      drain database ~through:Test_keys
        (List.sort_uniq Path.compare_package
           (List.map (fun (key : Names.key) -> key.module_.package) proofs.keys));
      List.filter
        (fun check ->
          match Instance_table.find_opt database.test_keys (template_check_root check) with
          | Some Blocked -> false
          | Some (Value _ | Failed _) | None -> true)
        checks

let list_proofs (proofs : proofs) =
  List.filter_map
    (fun key ->
      match read_proof proofs key with
      | Some (Value proof) -> Some (key, proof)
      | Some (Failed _ | Blocked) | None -> None)
    proofs.keys

let make_proof_lookups database = proof_lookups database ignore

let read_parsed database (file : Path.file) =
  drain database ~through:Parse [ file.module_.package ];
  (parsed_file database file).tree

let make_name_lookups database packages =
  drain database ~through:Namespaces packages;
  names_lookups database

let read_resolved database (key : Names.key) =
  drain database ~through:Resolution [ key.module_.package ];
  let owner = owner database key.module_.package in
  match
    List.filter_map
      (fun section ->
        match Hashtbl.find_opt owner.resolved_names (key, section) with
        | Some (Value resolved) -> Some resolved
        | Some (Failed _ | Blocked) | None -> None)
      Resolve.sections
  with
  | [] -> None
  | parts -> Some (Resolve.merge parts)

let request database packages ~through ~needs keys =
  drain database ~through packages;
  List.iter
    (fun key ->
      if not (List.for_all (is_current database) (needs key)) then
        Compiler_bug.bug ~stage:"Database" "%s is requested, and no root of lowering reaches it"
          (Instance.to_string key))
    keys

let requested table part key =
  match Instance_table.find_opt table key with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) ->
      Compiler_bug.bug ~stage:"Database" "%s is requested from code with errors"
        (Part.show_computed (Lowering part))
  | None -> unchecked (Lowering part)

let make_interface_lookups database packages =
  drain database ~through:Signature_checks packages;
  interface_lookups database ignore ~is_checked:true

let check_calls database interface viewers key = function
  | Ok lowered ->
      List.iter
        (fun viewer ->
          Option.iter
            (fun graph ->
              Compile.check_calls interface
                ~list_callees:(fun path -> Option.join (Call_graph.successors graph path))
                key lowered)
            (Hashtbl.find_opt database.graphs viewer))
        viewers
  | Error _ -> ()

let reached_todo_types database key =
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
        match Hashtbl.find_opt (owner database key.module_.package).interfaces key with
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
        when (stored database (Computed part)).is_failed ->
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
    settings = lowering_settings database;
    source = source database;
    interface;
    mir = mir_lookups database ignore;
    lowered =
      (fun key ->
        request database packages ~through:Lowered_code ~needs:(fun key -> [ Lowered key ]) [ key ];
        let lowered = requested database.lowered (Lowered key) key in
        check_calls database interface packages key lowered;
        lowered);
    test_key =
      (fun key ->
        request database packages ~through:Test_keys ~needs:(fun key -> [ Test_key key ]) [ key ];
        requested database.test_keys (Test_key key) key);
    reached_todo_types =
      (fun key ->
        request database packages ~through:Test_keys ~needs:(fun key -> [ Test_key key ]) [ key ];
        reached_todo_types database key);
  }

let find_main database package =
  drain database ~through:Namespaces [ package ];
  entry_point (names_lookups database) package

let list_callers database ~viewer path =
  drain database ~through:Recursion_groups [ viewer ];
  match Hashtbl.find_opt database.graphs viewer with
  | None -> []
  | Some graph ->
      let reached = Path_table.create 64 in
      let rec visit = function
        | [] -> ()
        | node :: rest when Path_table.mem reached node -> visit rest
        | node :: rest ->
            Path_table.replace reached node ();
            visit (Call_graph.predecessors graph node @ rest)
      in
      visit [ path ];
      Path_table.fold (fun node () nodes -> node :: nodes) reached []

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
    drain database ~through:Derived_forms [ Path.package path ];
    match Path_table.find_opt (owner database (Path.package path)).derived_forms path with
    | Some (Value form) -> Some form
    | Some (Failed _ | Blocked) | None -> None

  let read_core database path =
    drain database ~through:Derived_forms [ Path.package path ];
    Option.bind (form_origin database ignore path) (fun (origin, substitution) ->
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
    mir_lookups database ignore

  let list_reads database shown =
    match
      Computed_table.fold
        (fun part reads found -> if Part.show_computed part = shown then Some reads else found)
        database.reads None
    with
    | Some reads -> List.sort compare (List.map Part.show reads)
    | None -> Compiler_bug.bug ~stage:"Database" "%s is not computed" shown

  let list_differences hot cold =
    let parts = Stored_table.create 1024 in
    List.iter
      (fun database ->
        Computed_table.iter
          (fun part _ -> Stored_table.replace parts (Computed part) ())
          database.reads;
        Hashtbl.iter
          (fun _ package_database ->
            Path_table.iter
              (fun path _ -> Stored_table.replace parts (Recursion_group path) ())
              package_database.recursion_groups)
          database.package_databases)
      [ hot; cold ];
    let reads database (part : Part.stored) =
      match part with
      | Computed part ->
          Option.map (List.sort compare) (Computed_table.find_opt database.reads part)
      | Recursion_group _ -> None
    in
    List.sort compare
      (Stored_table.fold
         (fun part () differences ->
           if reads hot part <> reads cold part || not ((stored hot part).is_equal_in cold) then
             Part.show (Stored part) :: differences
           else differences)
         parts [])

  type observed = { recomputed : string list; collected : string list }

  let observe database run =
    let recomputed = ref [] and collected = ref [] in
    database.observe <-
      (function
      | Recomputed part -> recomputed := Part.show (Stored part) :: !recomputed
      | Collected part -> collected := Part.show_computed (Lowering part) :: !collected);
    Fun.protect ~finally:(fun () -> database.observe <- ignore) run;
    {
      recomputed = List.sort_uniq compare !recomputed;
      collected = List.sort_uniq compare !collected;
    }

  let root database key =
    own_roots database (Input Packages)
      (key :: Option.value (Part_table.find_opt database.owned (Input Packages)) ~default:[])

  let read_proof = read_proof

  let read_ownership database (key : Names.key) =
    match Hashtbl.find_opt (owner database key.module_.package).ownership key with
    | Some part -> part
    | None -> unchecked (Ownership key)
end
