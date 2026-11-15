module Part = Part
module Names = Resolve.Names
module Environment = Interface.Environment

module Path_key = struct
  type t = Path.t

  let equal = Path.equal
  let hash path = Hashtbl.hash_param 64 256 path
  let compare = Path.compare
end

module Path_table = Hashtbl.Make (Path_key)
module Call_graph = Graph.Make (Path_key)

type 'a part = Value of 'a | Failed of Syntax.diagnostic list | Blocked

exception Reads_failed_part

module Part_table = Hashtbl.Make (Part)

module Part_components = Components.Make (struct
  include Part

  let compare = compare
end)

module Instance_key = struct
  type t = Instance.key

  let equal = Instance.equal
  let hash = Hashtbl.hash_param 64 256
  let compare = Instance.compare
end

module Instance_table = Hashtbl.Make (Instance_key)
module References = Graph.Make (Instance_key)

module Ground_key = struct
  type t = Ground.ty

  let equal left right = Ground.compare left right = 0
  let hash = Hashtbl.hash_param 64 256
  let compare = Ground.compare
end

module Type_table = Hashtbl.Make (Ground_key)
module Type_components = Components.Make (Ground_key)

module Entry = struct
  type t =
    | Value of Part.t
    | Reads of Part.t
    | Stale of Part.t
    | Package of Path.package
    | File of Path.file
    | Owned of Part.t

  let equal : t -> t -> bool = ( = )
  let hash (entry : t) = Hashtbl.hash_param 64 256 entry
end

module Entry_table = Hashtbl.Make (Entry)

type state = {
  name : Path.package;
  mutable dependencies : Manifest.dependency list;
  mutable modules : Path.module_ list;
  mutable files : Path.file list;
  sources : (Path.file, Source.t) Hashtbl.t;
  parsed : (Path.file, Parsed.file) Hashtbl.t;
  mutable namespace : Names.namespace option;
  resolved_names : (Names.key * Resolve.section, Resolve.resolved part) Hashtbl.t;
  import_checks : (Path.file, Diagnostic.t list) Hashtbl.t;
  trait_headers : (Names.key, Resolve.trait_header part) Hashtbl.t;
  constant_values : Z.t option part Path_table.t;
  headers : (Names.key, Environment.header part) Hashtbl.t;
  interfaces : (Names.key, Environment.lowered_interface part) Hashtbl.t;
  derived_interfaces : Types.impl_interface part Path_table.t;
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
  states : (Path.package, state) Hashtbl.t;
  mutable project : Path.package list;
  absent : (Path.package, state) Hashtbl.t;
  reads : Part.t list Part_table.t;
  readers : unit Part_table.t Part_table.t;
  stale : (Path.package * Stage.t, unit Part_table.t) Hashtbl.t;
  implied : (Path.package, Part.t list) Hashtbl.t;
  graphs : (Path.package, Call_graph.t) Hashtbl.t;
  lowering : Compile.Lookups.settings option;
  ground_types : Compile.ground_types part Instance_table.t;
  layouts : Memory_layout.t part Type_table.t;
  holders : unit Instance_table.t Type_table.t;
  lowered : (Compile.lowered, Compile.unsupported) result part Instance_table.t;
  test_keys : (string, Compile.unsupported) result part Instance_table.t;
  references : References.t;
  owners : Part.t list Instance_table.t;
  owned : Instance.key list Part_table.t;
  unsaved : unit Entry_table.t;
  mutable observe : observation -> unit;
}

and observation = Computed of Part.t | Collected of Part.t

let empty_state name ~dependencies =
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
    derived_interfaces = Path_table.create 16;
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

let list_files (state : state) files =
  state.files <- List.sort compare files;
  state.modules <-
    List.sort_uniq compare (List.map (fun (file : Path.file) -> file.module_) state.files)

let source_of (file : Path.file) text = Source.create ~path:(Path.show_file file) text

let fresh_state name ~dependencies (texts : (Path.file * string) list) =
  let state = empty_state name ~dependencies in
  List.iter (fun (file, text) -> Hashtbl.replace state.sources file (source_of file text)) texts;
  list_files state (List.map fst texts);
  state

let mark_unsaved pipeline entry = Entry_table.replace pipeline.unsaved entry ()

let mark_state_unsaved pipeline (state : state) =
  mark_unsaved pipeline (Package state.name);
  List.iter (fun file -> mark_unsaved pipeline (File file)) state.files

let mark_stale pipeline part =
  let slot = (Part.package part, Stage.of_part part) in
  let parts =
    match Hashtbl.find_opt pipeline.stale slot with
    | Some parts -> parts
    | None ->
        let parts = Part_table.create 64 in
        Hashtbl.replace pipeline.stale slot parts;
        parts
  in
  if not (Part_table.mem parts part) then begin
    Part_table.replace parts part ();
    mark_unsaved pipeline (Stale part)
  end

let is_stale pipeline part =
  match Stage.of_part part with
  | Input -> false
  | stage -> (
      match Hashtbl.find_opt pipeline.stale (Part.package part, stage) with
      | Some parts -> Part_table.mem parts part
      | None -> false)

let unmark pipeline part =
  Option.iter
    (fun parts ->
      if Part_table.mem parts part then begin
        Part_table.remove parts part;
        mark_unsaved pipeline (Stale part)
      end)
    (Hashtbl.find_opt pipeline.stale (Part.package part, Stage.of_part part))

let stale_parts pipeline package stage =
  match Hashtbl.find_opt pipeline.stale (package, stage) with
  | Some parts -> Part_table.fold (fun part () parts -> part :: parts) parts []
  | None -> []

let create ?(loaded = []) ?(checks = true) (packages : Project.package list) =
  let states = Hashtbl.create 8 in
  List.iter (fun state -> Hashtbl.replace states state.name state) loaded;
  let pipeline =
    {
      states;
      project = List.map (fun (package : Project.package) -> package.name) packages;
      absent = Hashtbl.create 4;
      reads = Part_table.create 4096;
      readers = Part_table.create 4096;
      stale = Hashtbl.create 64;
      implied = Hashtbl.create 8;
      graphs = Hashtbl.create 8;
      lowering = Option.map (fun system -> { Compile.Lookups.checks; system }) Libc.host;
      ground_types = Instance_table.create 1024;
      layouts = Type_table.create 1024;
      holders = Type_table.create 1024;
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
      let state = fresh_state package.name ~dependencies:package.dependencies package.files in
      Hashtbl.replace states package.name state;
      mark_state_unsaved pipeline state;
      List.iter (fun file -> mark_stale pipeline (Parsed file)) state.files;
      mark_stale pipeline (Namespace package.name))
    packages;
  pipeline

let copy_state (state : state) =
  {
    name = state.name;
    dependencies = state.dependencies;
    modules = state.modules;
    files = state.files;
    sources = Hashtbl.copy state.sources;
    parsed = Hashtbl.copy state.parsed;
    namespace = state.namespace;
    resolved_names = Hashtbl.copy state.resolved_names;
    import_checks = Hashtbl.copy state.import_checks;
    trait_headers = Hashtbl.copy state.trait_headers;
    constant_values = Path_table.copy state.constant_values;
    headers = Hashtbl.copy state.headers;
    interfaces = Hashtbl.copy state.interfaces;
    derived_interfaces = Path_table.copy state.derived_interfaces;
    type_facts = Path_table.copy state.type_facts;
    grants = Hashtbl.copy state.grants;
    signature_checks = Hashtbl.copy state.signature_checks;
    contracts = Hashtbl.copy state.contracts;
    checked_bodies = Hashtbl.copy state.checked_bodies;
    derived_forms = Path_table.copy state.derived_forms;
    body_parts = Hashtbl.copy state.body_parts;
    contract_parts = Hashtbl.copy state.contract_parts;
    generated_parts = Path_table.copy state.generated_parts;
    call_edges = Path_table.copy state.call_edges;
    patterns = Hashtbl.copy state.patterns;
    usage = Hashtbl.copy state.usage;
    ownership = Hashtbl.copy state.ownership;
    used_packages = Hashtbl.copy state.used_packages;
    package_checks = Hashtbl.copy state.package_checks;
    recursion_groups = Path_table.copy state.recursion_groups;
    proofs = Hashtbl.copy state.proofs;
  }

let copy pipeline =
  let states = Hashtbl.copy pipeline.states in
  Hashtbl.filter_map_inplace
    (fun name state -> Some (if List.mem name pipeline.project then copy_state state else state))
    states;
  let readers = Part_table.copy pipeline.readers in
  Part_table.filter_map_inplace (fun _ parts -> Some (Part_table.copy parts)) readers;
  let stale = Hashtbl.copy pipeline.stale in
  Hashtbl.filter_map_inplace (fun _ parts -> Some (Part_table.copy parts)) stale;
  let graphs = Hashtbl.copy pipeline.graphs in
  Hashtbl.filter_map_inplace (fun _ graph -> Some (Call_graph.copy graph)) graphs;
  let holders = Type_table.copy pipeline.holders in
  Type_table.filter_map_inplace (fun _ instances -> Some (Instance_table.copy instances)) holders;
  {
    states;
    project = pipeline.project;
    absent = Hashtbl.copy pipeline.absent;
    reads = Part_table.copy pipeline.reads;
    readers;
    stale;
    implied = Hashtbl.copy pipeline.implied;
    graphs;
    lowering = pipeline.lowering;
    ground_types = Instance_table.copy pipeline.ground_types;
    layouts = Type_table.copy pipeline.layouts;
    holders;
    lowered = Instance_table.copy pipeline.lowered;
    test_keys = Instance_table.copy pipeline.test_keys;
    references = References.copy pipeline.references;
    owners = Instance_table.copy pipeline.owners;
    owned = Part_table.copy pipeline.owned;
    unsaved = Entry_table.create 64;
    observe = ignore;
  }

let add_reads pipeline part read_parts =
  Part_table.replace pipeline.reads part read_parts;
  List.iter
    (fun read ->
      let readers =
        match Part_table.find_opt pipeline.readers read with
        | Some readers -> readers
        | None ->
            let readers = Part_table.create 4 in
            Part_table.replace pipeline.readers read readers;
            readers
      in
      Part_table.replace readers part ())
    read_parts

let record pipeline parts reads =
  let read_parts =
    Part_table.fold
      (fun part () read_parts ->
        if List.exists (Part.equal part) parts then read_parts else part :: read_parts)
      reads []
  in
  List.iter
    (fun part ->
      let before = Part_table.find_opt pipeline.reads part in
      let is_unchanged =
        match before with
        | Some before ->
            List.length before = List.length read_parts
            && List.for_all (Part_table.mem reads) before
        | None -> false
      in
      if not is_unchanged then mark_unsaved pipeline (Reads part);
      Option.iter
        (List.iter (fun read ->
             Option.iter
               (fun readers -> Part_table.remove readers part)
               (Part_table.find_opt pipeline.readers read)))
        before;
      add_reads pipeline part read_parts)
    parts

let computing pipeline parts compute =
  let reads = Part_table.create 16 in
  let result = compute (fun part -> Part_table.replace reads part ()) in
  record pipeline parts reads;
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

let mark_readers ?(only = fun _ -> true) pipeline part =
  Option.iter
    (Part_table.iter (fun reader () -> if only reader then mark_stale pipeline reader))
    (Part_table.find_opt pipeline.readers part)

let store pipeline part slot value =
  let is_changed =
    match (slot.stored, value) with
    | Some stored, Some value -> stored <> value
    | None, None -> false
    | Some _, None | None, Some _ -> true
  in
  if is_changed then begin
    (match value with Some value -> slot.replace value | None -> slot.remove ());
    mark_unsaved pipeline (Value part);
    mark_readers pipeline part
  end

let compute_into pipeline part slot compute =
  store pipeline part slot (computing pipeline [ part ] compute)

let owner pipeline package =
  match Hashtbl.find_opt pipeline.states package with
  | Some state -> state
  | None -> (
      match Hashtbl.find_opt pipeline.absent package with
      | Some state -> state
      | None ->
          let state = empty_state package ~dependencies:[] in
          state.namespace <- Some Names.empty_namespace;
          Hashtbl.replace pipeline.absent package state;
          state)

let call_graph pipeline package =
  match Hashtbl.find_opt pipeline.graphs package with
  | Some graph -> graph
  | None ->
      let graph = Call_graph.create ~tracks_blocked:true in
      Hashtbl.replace pipeline.graphs package graph;
      graph

let unchecked name = Compiler_bug.bug ~stage:"Pipeline" "%s is not computed" name

let read pipeline note part =
  note part;
  if is_stale pipeline part then
    Compiler_bug.bug ~stage:"Pipeline" "%s is read while it is stale" (Part.show part)

let read_part pipeline note part_of select (key : Names.key) =
  let part = part_of key in
  read pipeline note part;
  match Hashtbl.find_opt (select (owner pipeline key.module_.package)) key with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> unchecked (Part.show part)

let computed compute argument =
  match compute argument with value -> Value value | exception Reads_failed_part -> Blocked

let checked_part check key =
  match check key with
  | [], value -> Value value
  | diagnostics, _ -> Failed diagnostics
  | exception Reads_failed_part -> Blocked

let value = function Value value -> value | Failed _ | Blocked -> raise Reads_failed_part
let package pipeline name = Hashtbl.find_opt pipeline.states name

let dependencies pipeline name =
  match package pipeline name with Some package -> package.dependencies | None -> []

let dependency_names pipeline name =
  List.map
    (fun (dependency : Manifest.dependency) -> dependency.package)
    (dependencies pipeline name)

let modules pipeline name =
  match package pipeline name with Some package -> package.modules | None -> []

let source pipeline (file : Path.file) =
  match Hashtbl.find_opt (owner pipeline file.module_.package).sources file with
  | Some source -> source
  | None -> Compiler_bug.bug ~stage:"Pipeline" "%s is not a file of the build" (Path.show_file file)

let visible_packages pipeline note package =
  let seen = Hashtbl.create 8 in
  let rec visit package =
    if not (Hashtbl.mem seen package) then begin
      Hashtbl.replace seen package ();
      note (Part.Dependencies package);
      List.iter visit (dependency_names pipeline package)
    end
  in
  visit package;
  visit Path.standard_package;
  List.sort Path.compare_package
    (Hashtbl.fold (fun package () packages -> package :: packages) seen [])

let in_dependency_order pipeline packages =
  let seen = Hashtbl.create 8 in
  let order = ref [] in
  let rec visit package =
    if not (Hashtbl.mem seen package) then begin
      Hashtbl.replace seen package ();
      List.iter visit (List.sort Path.compare_package (dependency_names pipeline package));
      order := package :: !order
    end
  in
  visit Path.standard_package;
  List.iter visit packages;
  List.rev !order

let namespace pipeline package =
  match (owner pipeline package).namespace with
  | Some namespace -> namespace
  | None -> unchecked (Part.show (Namespace package))

let names_over pipeline ~namespace =
  Names.of_namespaces ~namespace
    ~module_exists:(fun (module_ : Path.module_) ->
      module_ = Intrinsic.module_ || List.mem module_ (modules pipeline module_.package))
    ~split_module:
      (Path.split_module ~is_package:(fun name -> Option.is_some (package pipeline name)))
    ~dependency_names:(dependency_names pipeline)

let names_lookups pipeline = names_over pipeline ~namespace:(namespace pipeline)

let recording (names : Names.lookups) (note : Part.t -> unit) : Names.lookups =
  let noting (part : Part.t) read =
    note part;
    read
  in
  {
    find = (fun module_ name -> noting (Entry (module_, name)) (names.find module_ name));
    entries = (fun module_ -> noting (Entries module_) (names.entries module_));
    imports = (fun key -> noting (Imports key) (names.imports key));
    module_exists = (fun module_ -> noting (Modules module_.package) (names.module_exists module_));
    split_module = (fun parts -> noting Packages (names.split_module parts));
    dependency_names =
      (fun package -> noting (Dependencies package) (names.dependency_names package));
    key =
      (fun path ->
        (match path with
        | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ }
          ->
            note (Declaration { module_; path; ordinal = 0 })
        | Method { owner; name; _ } | Member_constant { owner; name } ->
            note (Members (owner, name))
        | Derived _ -> ());
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

let recording_names pipeline note = recording (names_lookups pipeline) note

let parsed_file pipeline (file : Path.file) =
  match Hashtbl.find_opt (owner pipeline file.module_.package).parsed file with
  | Some parsed -> parsed
  | None -> unchecked (Part.show (Parsed file))

let namespace_of pipeline note (state : state) =
  note (Part.Modules state.name);
  Names.namespace (recording_names pipeline note) state.name
    (List.map
       (fun module_ ->
         ( module_,
           List.filter_map
             (fun (file : Path.file) ->
               if file.module_ = module_ then begin
                 read pipeline note (Parsed file);
                 let parsed = parsed_file pipeline file in
                 Some (file, { Syntax.uses = parsed.uses; definitions = parsed.definitions })
               end
               else None)
             state.files ))
       state.modules)

let file_keys pipeline file = List.map Names.key_of ((names_lookups pipeline).declarations_in file)

let resolved_part pipeline note section (key : Names.key) =
  read pipeline note (Resolved (key, section));
  match Hashtbl.find_opt (owner pipeline key.module_.package).resolved_names (key, section) with
  | Some part -> part
  | None -> unchecked (Part.show (Resolved (key, section)))

let resolved pipeline note section (key : Names.key) =
  read pipeline note (Resolved (key, section));
  Option.map value
    (Hashtbl.find_opt (owner pipeline key.module_.package).resolved_names (key, section))

let lowered_interface pipeline note ~is_checked (key : Names.key) =
  let owner = owner pipeline key.module_.package in
  read pipeline note (Interface key);
  if is_checked then begin
    read pipeline note (Signature_check key);
    match Hashtbl.find_opt owner.signature_checks key with
    | Some (Failed _ | Blocked) -> raise Reads_failed_part
    | Some (Value ()) | None -> ()
  end;
  Option.map value (Hashtbl.find_opt owner.interfaces key)

let interface_lookups pipeline note ~is_checked : Interface.Lookups.t =
  let names = recording_names pipeline note in
  let lowered_interface = lowered_interface pipeline note ~is_checked in
  {
    names;
    resolved = resolved pipeline note;
    trait_header =
      (fun path ->
        Option.bind (names.key path) (fun key ->
            read pipeline note (Trait_header key);
            Option.map value
              (Hashtbl.find_opt (owner pipeline key.module_.package).trait_headers key)));
    constant_value =
      (fun path ->
        read pipeline note (Constant_value path);
        Option.bind
          (Path_table.find_opt (owner pipeline (Path.package path)).constant_values path)
          value);
    header =
      (fun key ->
        read pipeline note (Header key);
        Option.map value (Hashtbl.find_opt (owner pipeline key.module_.package).headers key));
    lowered_interface;
    derived_interface =
      (fun path ->
        (match path with
        | Derived { type_; _ } ->
            Option.iter (fun key -> ignore (lowered_interface key)) (names.key type_)
        | _ -> ());
        read pipeline note (Derived_interface path);
        Option.map value
          (Path_table.find_opt (owner pipeline (Path.package path)).derived_interfaces path));
    type_facts =
      (fun path ->
        read pipeline note (Type_facts path);
        Option.map value (Path_table.find_opt (owner pipeline (Path.package path)).type_facts path));
    granted =
      (fun package dependency ->
        read pipeline note (Grant (package, dependency));
        Hashtbl.find_opt (owner pipeline package).grants dependency);
  }

let interface_part = function
  | Some (lowered : Environment.lowered_interface) -> (
      match (lowered.diagnostics, lowered.interface) with
      | [], Error_interface _ -> Blocked
      | [], _ -> Value lowered
      | diagnostics, _ -> Failed diagnostics)
  | None -> Blocked

module Path_components = Components.Make (struct
  type t = Path.t

  let equal = Path.equal
  let hash path = Hashtbl.hash_param 64 256 path
  let compare = Path.compare
end)

let type_interface lookups path =
  match computed (Interface.Definition.type_interface lookups) path with
  | Value interface -> interface
  | Failed _ | Blocked -> None

let impl_methods (names : Names.lookups) package =
  List.concat_map
    (fun (((trait : Path.t), _), (impl : Path.t)) ->
      match names.key trait with
      | Some trait_key ->
          List.filter_map
            (fun (member : Names.key) ->
              match member.path with
              | Method { name; receiver; _ } -> Some (Path.Method { owner = impl; name; receiver })
              | _ -> None)
            (names.contained trait_key)
      | None -> [])
    (names.impls package)

let derived_paths names package =
  List.filter
    (function Path.Method { owner = Derived _; _ } -> true | _ -> false)
    (impl_methods names package)

let package_parts pipeline (names : Names.lookups) package : Part.t list =
  let state = owner pipeline package in
  let declarations = names.package_declarations package in
  let paths = List.map (fun (declaration : Names.declaration) -> declaration.path) declarations in
  let of_declaration (declaration : Names.declaration) : Part.t list =
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
      (function _, (Path.Derived _ as impl) -> Some (Part.Derived_interface impl) | _ -> None)
      (names.impls package)
  @ List.concat_map
      (fun path -> [ Part.Derived_form path; Generated_mir path ])
      (derived_paths names package)
  @ List.map
      (fun path -> Part.Call_edges path)
      (List.sort_uniq Path.compare (paths @ impl_methods names package))
  @ List.map (fun path -> Part.Successors (path, package)) (List.sort_uniq Path.compare paths)
  @ List.map
      (fun dependency -> Part.Grant (package, dependency))
      (List.sort_uniq Path.compare_package (names.dependency_names package))
  @ List.map (fun file -> Part.Import_check file) state.files
  @ List.map (fun check -> Part.Package_check (package, check)) (Package_checks.checks declarations)

let checked_body pipeline note key =
  read_part pipeline note (fun key -> Part.Checked_body key) (fun owner -> owner.checked_bodies) key

let checked_core pipeline note key = (checked_body pipeline note key).form

let infer_lookups pipeline note : Infer.Lookups.t =
  {
    interface = interface_lookups pipeline note ~is_checked:true;
    contract = read_part pipeline note (fun key -> Part.Contract key) (fun owner -> owner.contracts);
  }

let type_check run lookups key =
  match run lookups key with
  | Some (Ok checked) -> Some (Value checked)
  | Some (Error []) -> Some Blocked
  | Some (Error diagnostics) -> Some (Failed diagnostics)
  | None -> None
  | exception Reads_failed_part -> Some Blocked

let form_origin pipeline note =
  Infer.form_origin (interface_lookups pipeline note ~is_checked:true) ~is_derived:(fun path ->
      read pipeline note (Derived_form path);
      Path_table.mem (owner pipeline (Path.package path)).derived_forms path)

let body_mir pipeline note =
  read_part pipeline note (fun key -> Part.Body_mir key) (fun owner -> owner.body_parts)

let mir_lookups pipeline note : Mir.lookups =
  {
    form_origin = form_origin pipeline note;
    body_part = body_mir pipeline note;
    contract_part =
      read_part pipeline note (fun key -> Part.Contract_mir key) (fun owner -> owner.contract_parts);
    generated_parts =
      (fun path ->
        read pipeline note (Generated_mir path);
        match Path_table.find_opt (owner pipeline (Path.package path)).generated_parts path with
        | Some (Value parts) -> parts
        | Some (Failed _ | Blocked) -> raise Reads_failed_part
        | None -> unchecked (Part.show (Generated_mir path)));
  }

let call_edge_lookups pipeline note : Mir.Call_edges.lookups =
  { interface = interface_lookups pipeline note ~is_checked:true; mir = mir_lookups pipeline note }

let call_edge_part pipeline note path =
  read pipeline note (Call_edges path);
  match Path_table.find_opt (owner pipeline (Path.package path)).call_edges path with
  | Some part -> part
  | None -> Value []

let patterns_lookups pipeline note : Patterns.Lookups.t =
  {
    core = (fun key -> Some (checked_core pipeline note key));
    interface = interface_lookups pipeline note ~is_checked:true;
  }

let usage_lookups pipeline note : Usage.Lookups.t =
  {
    names = recording_names pipeline note;
    resolved = resolved pipeline note;
    tables = (fun key -> Some (checked_body pipeline note key).tables);
  }

let ownership_lookups pipeline note : Ownership.Lookups.t =
  {
    graph = (fun key -> Mir.graph (body_mir pipeline note key));
    interface = interface_lookups pipeline note ~is_checked:true;
  }

let used_packages pipeline note (key : Names.key) =
  let { Infer.form; evidence_packages; _ } = checked_body pipeline note key in
  match Resolve.whole (resolved pipeline note) key with
  | Some resolved -> Package_checks.used_packages resolved ~evidence_packages form
  | None -> raise Reads_failed_part

let package_checks_lookups pipeline note : Package_checks.Lookups.t =
  {
    dependencies =
      (fun package ->
        note (Part.Dependencies package);
        dependencies pipeline package);
    interface = interface_lookups pipeline note ~is_checked:true;
    core = (fun key -> Some (checked_core pipeline note key));
    used_packages =
      read_part pipeline note (fun key -> Part.Used_packages key) (fun owner -> owner.used_packages);
  }

let used_imports pipeline note file =
  note (Part.File_declarations file);
  let used =
    List.concat_map
      (fun key ->
        List.map
          (fun section ->
            match resolved_part pipeline note section key with
            | Value resolved -> Some resolved.used_imports
            | Failed _ | Blocked -> None)
          Resolve.sections)
      (file_keys pipeline file)
  in
  if List.for_all Option.is_some used then Some (List.concat_map Option.get used) else None

let import_diagnostics pipeline note (file : Path.file) =
  read pipeline note (Parsed file);
  note (Source file);
  let parsed = parsed_file pipeline file in
  Resolve.file_diagnostics (recording_names pipeline note) file
    { uses = parsed.uses; definitions = parsed.definitions }
    ~text:(Source.text (source pipeline file))
    ~used:(used_imports pipeline note file)

let successors pipeline note ~viewer path =
  match call_edge_part pipeline note path with
  | Failed _ | Blocked -> None
  | Value callees -> (
      match
        Mir.Call_edges.implementations (call_edge_lookups pipeline note)
          ~visible:(visible_packages pipeline note viewer)
          path
      with
      | implementations -> Some (List.sort_uniq Path.compare (callees @ implementations))
      | exception Reads_failed_part -> None)

let recursion_group pipeline note path =
  read pipeline note (Recursion_group path);
  match Path_table.find_opt (owner pipeline (Path.package path)).recursion_groups path with
  | Some (Value members) -> members
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> []

let proof_lookups pipeline note : Prover.Lookups.t =
  {
    source =
      (fun file ->
        note (Part.Source file);
        source pipeline file);
    interface = interface_lookups pipeline note ~is_checked:true;
    mir = mir_lookups pipeline note;
    patterns = read_part pipeline note (fun key -> Part.Patterns key) (fun owner -> owner.patterns);
    must_be_disjoint =
      read_part pipeline note (fun key -> Part.Ownership key) (fun owner -> owner.ownership);
    recursion_group = recursion_group pipeline note;
  }

let layout pipeline note ty =
  read pipeline note (Layout ty);
  match Type_table.find_opt pipeline.layouts ty with
  | Some (Value layout) -> layout
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> unchecked (Part.show (Layout ty))

let stage_lowering_lookups pipeline note : Compile.Lookups.t =
  { interface = interface_lookups pipeline note ~is_checked:true; mir = mir_lookups pipeline note }

let instance_part pipeline note table part instance =
  read pipeline note part;
  match Instance_table.find_opt table instance with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> unchecked (Part.show part)

let ground_types pipeline note key =
  instance_part pipeline note pipeline.ground_types (Ground_types key) key

let lowered pipeline note key = instance_part pipeline note pipeline.lowered (Lowered key) key
let test_key pipeline note key = instance_part pipeline note pipeline.test_keys (Test_key key) key

let instance_layout pipeline note key =
  let types =
    lazy
      (let types = Type_table.create 64 in
       List.iter (fun ty -> Type_table.replace types ty ()) (ground_types pipeline note key).types;
       types)
  in
  fun ty ->
    if not (Type_table.mem (Lazy.force types) ty) then
      Compiler_bug.bug ~stage:"Pipeline" "%s reads the layout of %s, which its ground types lack"
        (Instance.to_string key) (Ground.to_string ty);
    layout pipeline note ty

let instance_slot table instance =
  {
    stored = Instance_table.find_opt table instance;
    replace = Instance_table.replace table instance;
    remove = (fun () -> Instance_table.remove table instance);
  }

exception Reaches_unsupported of Compile.unsupported

let compute_test_keys pipeline keys =
  let outcome =
    computing pipeline
      (List.map (fun key -> Part.Test_key key) keys)
      (fun note ->
        let supported = function
          | Ok value -> value
          | Error unsupported -> raise (Reaches_unsupported unsupported)
        in
        match
          Compile.test_keys
            ~lowered:(fun key -> supported (lowered pipeline note key))
            ~known:(fun key -> supported (test_key pipeline note key))
            keys
        with
        | test_keys -> Value (Ok test_keys)
        | exception Reaches_unsupported unsupported -> Value (Error unsupported)
        | exception Reads_failed_part -> Blocked)
  in
  List.iter
    (fun key ->
      let part = Part.Test_key key in
      pipeline.observe (Computed part);
      store pipeline part
        (instance_slot pipeline.test_keys key)
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

let stored pipeline (part : Part.t) =
  let package = Part.package part in
  let state = owner pipeline package in
  let failed = function Failed _ -> true | Value _ | Blocked -> false in
  let never _ = false in
  let keyed ~is_failed select key =
    let table = select state in
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
    let table = select state in
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
    let find pipeline = Instance_table.find_opt (select pipeline) instance in
    {
      is_failed = Option.fold ~none:false ~some:failed (find pipeline);
      remove = (fun () -> Instance_table.remove (select pipeline) instance);
      is_equal_in = (fun other -> compare (find other) (find pipeline) = 0);
      saved = (fun () -> Option.map marshalled (find pipeline));
      restore =
        (fun bytes ->
          Instance_table.replace (select pipeline) instance (Marshal.from_string bytes 0));
    }
  in
  let unsaved () =
    Compiler_bug.bug ~stage:"Pipeline" "%s is computed when a database opens, not saved"
      (Part.show part)
  in
  match part with
  | Parsed file -> keyed ~is_failed:never (fun state -> state.parsed) file
  | Namespace _ ->
      {
        is_failed = false;
        remove = (fun () -> state.namespace <- None);
        is_equal_in = (fun other -> compare (owner other package).namespace state.namespace = 0);
        saved = unsaved;
        restore = (fun _ -> unsaved ());
      }
  | Resolved (key, section) ->
      keyed ~is_failed:failed (fun state -> state.resolved_names) (key, section)
  | Import_check file -> keyed ~is_failed:never (fun state -> state.import_checks) file
  | Trait_header key -> keyed ~is_failed:failed (fun state -> state.trait_headers) key
  | Constant_value path -> at_path ~is_failed:failed (fun state -> state.constant_values) path
  | Header key -> keyed ~is_failed:failed (fun state -> state.headers) key
  | Interface key -> keyed ~is_failed:failed (fun state -> state.interfaces) key
  | Derived_interface path -> at_path ~is_failed:failed (fun state -> state.derived_interfaces) path
  | Type_facts path -> at_path ~is_failed:failed (fun state -> state.type_facts) path
  | Grant (_, dependency) -> keyed ~is_failed:never (fun state -> state.grants) dependency
  | Signature_check key -> keyed ~is_failed:failed (fun state -> state.signature_checks) key
  | Contract key -> keyed ~is_failed:failed (fun state -> state.contracts) key
  | Checked_body key -> keyed ~is_failed:failed (fun state -> state.checked_bodies) key
  | Derived_form path -> at_path ~is_failed:failed (fun state -> state.derived_forms) path
  | Body_mir key -> keyed ~is_failed:failed (fun state -> state.body_parts) key
  | Contract_mir key -> keyed ~is_failed:failed (fun state -> state.contract_parts) key
  | Generated_mir path -> at_path ~is_failed:failed (fun state -> state.generated_parts) path
  | Call_edges path -> at_path ~is_failed:failed (fun state -> state.call_edges) path
  | Patterns key -> keyed ~is_failed:failed (fun state -> state.patterns) key
  | Usage key -> keyed ~is_failed:failed (fun state -> state.usage) key
  | Ownership key -> keyed ~is_failed:failed (fun state -> state.ownership) key
  | Used_packages key -> keyed ~is_failed:failed (fun state -> state.used_packages) key
  | Package_check (_, check) -> keyed ~is_failed:failed (fun state -> state.package_checks) check
  | Successors (path, viewer) ->
      let successors pipeline =
        Option.bind (Hashtbl.find_opt pipeline.graphs viewer) (fun graph ->
            Call_graph.successors graph path)
      in
      {
        is_failed = false;
        remove = (fun () -> Call_graph.remove_successors (call_graph pipeline viewer) path);
        is_equal_in = (fun other -> successors other = successors pipeline);
        saved = (fun () -> Option.map marshalled (successors pipeline));
        restore =
          (fun bytes ->
            ignore
              (Call_graph.set_successors (call_graph pipeline viewer) path
                 (Marshal.from_string bytes 0)));
      }
  | Recursion_group path -> at_path ~is_failed:failed (fun state -> state.recursion_groups) path
  | Proof key -> keyed ~is_failed:failed (fun state -> state.proofs) key
  | Ground_types key -> of_instance (fun pipeline -> pipeline.ground_types) key
  | Lowered key -> of_instance (fun pipeline -> pipeline.lowered) key
  | Test_key key -> of_instance (fun pipeline -> pipeline.test_keys) key
  | Layout ty ->
      let find pipeline = Type_table.find_opt pipeline.layouts ty in
      {
        is_failed = Option.fold ~none:false ~some:failed (find pipeline);
        remove = (fun () -> Type_table.remove pipeline.layouts ty);
        is_equal_in = (fun other -> compare (find other) (find pipeline) = 0);
        saved = (fun () -> Option.map marshalled (find pipeline));
        restore =
          (fun bytes -> Type_table.replace pipeline.layouts ty (Marshal.from_string bytes 0));
      }
  | Source _ | Packages | Modules _ | Dependencies _ | Entry _ | Entries _ | Imports _
  | Declaration _ | Tree _ | Text _ | Place _ | Container _ | Contained _ | Module_declarations _
  | File_declarations _ | Package_declarations _ | Members _ | Traits_declaring _ | Impl_index _
  | Impls_of_type _ | Impls_of_trait _ | Law_proofs _ ->
      Compiler_bug.bug ~stage:"Pipeline" "%s is not stored as a part" (Part.show part)

let discard pipeline part =
  unmark pipeline part;
  record pipeline [ part ] (Part_table.create 0);
  Part_table.remove pipeline.reads part;
  mark_unsaved pipeline (Reads part)

let instance_parts key : Part.t list = [ Ground_types key; Lowered key; Test_key key ]

let is_stored pipeline (part : Part.t) =
  match part with
  | Ground_types key -> Instance_table.mem pipeline.ground_types key
  | Lowered key -> Instance_table.mem pipeline.lowered key
  | Test_key key -> Instance_table.mem pipeline.test_keys key
  | Layout ty -> Type_table.mem pipeline.layouts ty
  | part -> Compiler_bug.bug ~stage:"Pipeline" "%s is not a part of lowering" (Part.show part)

let is_created pipeline part = is_stale pipeline part || is_stored pipeline part
let is_current pipeline part = (not (is_stale pipeline part)) && is_stored pipeline part

let create_instance pipeline key =
  List.iter
    (fun part -> if not (is_created pipeline part) then mark_stale pipeline part)
    (instance_parts key)

let held_types pipeline key =
  match Instance_table.find_opt pipeline.ground_types key with
  | Some (Value ground) -> List.sort_uniq Ground.compare ground.types
  | Some (Failed _ | Blocked) | None -> []

let rec sorted_difference compare left right =
  match (left, right) with
  | [], _ -> []
  | left, [] -> left
  | item :: rest, other :: others ->
      let order = compare item other in
      if order = 0 then sorted_difference compare rest others
      else if order < 0 then item :: sorted_difference compare rest right
      else sorted_difference compare left others

let release pipeline key ty =
  match Type_table.find_opt pipeline.holders ty with
  | Some holders ->
      Instance_table.remove holders key;
      let is_unheld = Instance_table.length holders = 0 in
      if is_unheld then Type_table.remove pipeline.holders ty;
      is_unheld
  | None -> false

let hold pipeline key ty =
  let holders =
    match Type_table.find_opt pipeline.holders ty with
    | Some holders -> holders
    | None ->
        let holders = Instance_table.create 4 in
        Type_table.replace pipeline.holders ty holders;
        holders
  in
  Instance_table.replace holders key ();
  if not (is_created pipeline (Layout ty)) then mark_stale pipeline (Layout ty)

let rec forget pipeline parts =
  let removed = Part_table.create 16 in
  List.iter (fun part -> Part_table.replace removed part ()) parts;
  List.iter
    (fun part ->
      (stored pipeline part).remove ();
      mark_unsaved pipeline (Value part);
      discard pipeline part)
    parts;
  List.iter (mark_readers ~only:(fun reader -> not (Part_table.mem removed reader)) pipeline) parts;
  List.iter (function Part.Proof _ as owner -> own_roots pipeline owner [] | _ -> ()) parts

and own_roots pipeline owner roots =
  let before = Option.value (Part_table.find_opt pipeline.owned owner) ~default:[] in
  let roots = List.sort_uniq Instance.compare roots in
  if roots <> before then begin
    if roots = [] then Part_table.remove pipeline.owned owner
    else Part_table.replace pipeline.owned owner roots;
    mark_unsaved pipeline (Owned owner);
    let owners root = Option.value (Instance_table.find_opt pipeline.owners root) ~default:[] in
    List.iter
      (fun root ->
        match List.filter (fun other -> not (Part.equal other owner)) (owners root) with
        | [] ->
            Instance_table.remove pipeline.owners root;
            References.remove_root pipeline.references root
        | others -> Instance_table.replace pipeline.owners root others)
      (sorted_difference Instance.compare before roots);
    List.iter
      (fun root ->
        Instance_table.replace pipeline.owners root (owner :: owners root);
        if References.add_root pipeline.references root then create_instance pipeline root)
      (sorted_difference Instance.compare roots before);
    settle_references pipeline
  end

and settle_references pipeline =
  if References.has_changes pipeline.references then
    collect pipeline (References.update pipeline.references).removed

and collect pipeline keys =
  let layouts =
    List.concat_map
      (fun key ->
        List.filter_map
          (fun ty -> if release pipeline key ty then Some (Part.Layout ty) else None)
          (held_types pipeline key))
      keys
  in
  let parts = List.concat_map instance_parts keys @ layouts in
  List.iter (fun part -> pipeline.observe (Collected part)) parts;
  forget pipeline parts

let update_holders pipeline key ~before =
  let after = held_types pipeline key in
  let unheld = List.filter (release pipeline key) (sorted_difference Ground.compare before after) in
  List.iter (hold pipeline key) (sorted_difference Ground.compare after before);
  if unheld <> [] then begin
    let parts = List.map (fun ty -> Part.Layout ty) unheld in
    List.iter (fun part -> pipeline.observe (Collected part)) parts;
    forget pipeline parts
  end

let instance_edges pipeline key =
  List.sort_uniq Instance.compare
    ((match Instance_table.find_opt pipeline.ground_types key with
       | Some (Value ground) ->
           List.map (fun path -> Instance.Constant path) ground.folded_constants
       | Some (Failed _ | Blocked) | None -> [])
    @
    match Instance_table.find_opt pipeline.lowered key with
    | Some (Value (Ok lowered)) -> Compile.references lowered
    | Some (Value (Error _) | Failed _ | Blocked) | None -> [])

let update_references pipeline key =
  let edges = instance_edges pipeline key in
  if References.successors pipeline.references key <> Some (Some edges) then begin
    List.iter (create_instance pipeline)
      (References.set_successors pipeline.references key (Some edges));
    settle_references pipeline
  end

let refers_currently pipeline referrer (key : Instance.key) =
  (not (is_stale pipeline (Ground_types referrer)))
  && ((match (key, Instance_table.find_opt pipeline.ground_types referrer) with
        | Constant path, Some (Value ground) ->
            List.exists (Path.equal path) ground.folded_constants
        | _ -> false)
     || (not (is_stale pipeline (Lowered referrer)))
        &&
        match Instance_table.find_opt pipeline.lowered referrer with
        | Some (Value (Ok lowered)) -> List.exists (Instance.equal key) (Compile.references lowered)
        | Some (Value (Error _) | Failed _ | Blocked) | None -> false)

let is_ready pipeline key =
  List.exists
    (fun owner -> not (is_stale pipeline owner))
    (Option.value (Instance_table.find_opt pipeline.owners key) ~default:[])
  || List.exists
       (fun referrer -> refers_currently pipeline referrer key)
       (References.predecessors pipeline.references key)

let is_drained pipeline (part : Part.t) =
  match part with
  | Ground_types key | Lowered key | Test_key key -> is_ready pipeline key
  | Layout ty -> (
      match Type_table.find_opt pipeline.holders ty with
      | Some holders ->
          Seq.exists
            (fun holder -> not (is_stale pipeline (Ground_types holder)))
            (Instance_table.to_seq_keys holders)
      | None -> false)
  | _ -> true

let lowering_settings pipeline =
  match pipeline.lowering with
  | Some settings -> settings
  | None -> Compiler_bug.bug ~stage:"Pipeline" "this host has no lowering settings"

let own_template_checks pipeline (key : Names.key) =
  if Option.is_some pipeline.lowering then
    own_roots pipeline (Proof key)
      (match Hashtbl.find_opt (owner pipeline key.module_.package).proofs key with
      | Some (Value (Obligations { obligations; _ })) ->
          List.filter_map
            (fun (obligation : Prover.State.obligation) ->
              Option.map
                (fun ({ from_template; texts; _ } : Prover.State.evaluation) ->
                  Instance.Template_check { from_template; texts })
                obligation.evaluation)
            obligations
      | Some (Value (Unsupported _ | Not_proven_here) | Failed _ | Blocked) | None -> [])

let entry_point (names : Names.lookups) package =
  List.find_map
    (fun (declaration : Names.declaration) ->
      match declaration.path with
      | Top { name = "main"; _ } when declaration.kind = Function && declaration.ordinal = 0 ->
          Some declaration.path
      | _ -> None)
    (names.declarations { package; modules = [] })

let own_lowering_roots pipeline (names : Names.lookups) package =
  if Option.is_some pipeline.lowering then
    own_roots pipeline (Namespace package)
      (Compile.roots
         ~tests:
           (List.filter_map
              (fun (declaration : Names.declaration) ->
                match declaration.path with Test _ -> Some declaration.path | _ -> None)
              (names.package_declarations package))
         ~mains:(Option.to_list (entry_point names package)))

let holds_position pipeline (part : Part.t) =
  match part with
  | Proof _ | Package_check _ | Lowered _ -> true
  | _ -> (stored pipeline part).is_failed

let mark_change pipeline package (change : Names.change) =
  let part : Part.t =
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
  | Positions _ -> mark_readers ~only:(holds_position pipeline) pipeline part
  | _ -> mark_readers pipeline part

let is_own_namespace_part package (part : Part.t) =
  match part with
  | Packages -> false
  | part -> Stage.of_part part = Namespaces && Part.package part = package

let namespace_and_implied pipeline (state : state) =
  let package = state.name in
  let namespace, implied =
    computing pipeline [ Part.Namespace package ] (fun note ->
        let note part = if not (is_own_namespace_part package part) then note part in
        let own_namespace = namespace_of pipeline note state in
        let names =
          names_over pipeline ~namespace:(fun name ->
              if name = package then own_namespace else namespace pipeline name)
        in
        (own_namespace, package_parts pipeline (recording names note) package))
  in
  state.namespace <- Some namespace;
  Hashtbl.replace pipeline.implied package implied;
  (namespace, implied)

let compute_namespace pipeline (state : state) =
  let package = state.name in
  let before = Option.value state.namespace ~default:Names.empty_namespace in
  let implied_before = Option.value ~default:[] (Hashtbl.find_opt pipeline.implied package) in
  let after, implied = namespace_and_implied pipeline state in
  let membership parts =
    let members = Part_table.create 256 in
    List.iter (fun part -> Part_table.replace members part ()) parts;
    Part_table.mem members
  in
  let was_implied = membership implied_before and is_implied = membership implied in
  let graph = call_graph pipeline package in
  List.iter
    (function
      | Part.Successors (root, _) as part when not (is_implied part) ->
          Call_graph.remove_root graph root
      | _ -> ())
    implied_before;
  List.iter
    (function
      | Part.Successors (root, _) as part when not (was_implied part) ->
          ignore (Call_graph.add_root graph root)
      | _ -> ())
    implied;
  List.iter (mark_change pipeline package) (Names.changes before after);
  List.iter (fun part -> if not (was_implied part) then mark_stale pipeline part) implied;
  forget pipeline (List.filter (fun part -> not (is_implied part)) implied_before);
  own_lowering_roots pipeline (names_lookups pipeline) package

let compute_type_facts pipeline paths =
  let facts =
    computing pipeline
      (List.map (fun path -> Part.Type_facts path) paths)
      (fun note ->
        let lookups = interface_lookups pipeline note ~is_checked:false in
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
      pipeline.observe (Computed (Type_facts path));
      store pipeline (Type_facts path)
        (at_path (owner pipeline (Path.package path)).type_facts path)
        (Some
           (match facts with
           | Value facts -> (
               match List.assoc_opt path facts with Some facts -> Value facts | None -> Blocked)
           | Failed _ | Blocked -> Blocked)))
    paths

let compute_part pipeline (part : Part.t) =
  pipeline.observe (Computed part);
  let state = owner pipeline (Part.package part) in
  let into slot compute = compute_into pipeline part slot compute in
  match part with
  | Parsed file ->
      into (keyed state.parsed file) (fun note ->
          note (Source file);
          Some (Parsed.parse (source pipeline file)))
  | Namespace _ -> compute_namespace pipeline state
  | Resolved (key, section) ->
      into
        (keyed state.resolved_names (key, section))
        (fun note ->
          Some
            (match Resolve.resolve (recording_names pipeline note) key section with
            | Some (Ok resolved) -> Value resolved
            | Some (Error diagnostics) -> Failed diagnostics
            | None -> Blocked))
  | Import_check file ->
      into (keyed state.import_checks file) (fun note ->
          Some (import_diagnostics pipeline note file))
  | Trait_header key ->
      into (keyed state.trait_headers key) (fun note ->
          Some
            (match
               ( (recording_names pipeline note).definition key,
                 resolved_part pipeline note Interface key )
             with
            | Some definition, Value resolved -> (
                match Resolve.trait_header definition resolved with
                | Some header -> Value header
                | None -> Blocked)
            | _ -> Blocked))
  | Constant_value path ->
      into (at_path state.constant_values path) (fun note ->
          Some
            (computed
               (Interface.Constants.value_of (interface_lookups pipeline note ~is_checked:false))
               path))
  | Header key ->
      into (keyed state.headers key) (fun note ->
          Some
            (match
               computed
                 (Interface.Definition.header (interface_lookups pipeline note ~is_checked:false))
                 key
             with
            | Value (Some (Ok header)) -> Value header
            | Value (Some (Error (_ :: _ as diagnostics))) -> Failed diagnostics
            | Value (Some (Error [])) | Value None | Failed _ | Blocked -> Blocked))
  | Interface key ->
      into (keyed state.interfaces key) (fun note ->
          Some
            (match
               computed
                 (Interface.Definition.lower (interface_lookups pipeline note ~is_checked:false))
                 key
             with
            | Value lowered -> interface_part lowered
            | Failed _ | Blocked -> Blocked))
  | Derived_interface (Derived { type_; trait } as impl) ->
      into (at_path state.derived_interfaces impl) (fun note ->
          Some
            (match
               computed
                 (fun trait ->
                   Interface.Impls.derived_interface
                     (interface_lookups pipeline note ~is_checked:false)
                     ~type_ ~trait)
                 trait
             with
            | Value (Some interface) -> Value interface
            | Value None | Failed _ | Blocked -> Blocked))
  | Type_facts path -> compute_type_facts pipeline [ path ]
  | Grant (package, dependency) ->
      let entry =
        List.find
          (fun (entry : Manifest.dependency) -> entry.package = dependency)
          state.dependencies
      in
      into (keyed state.grants dependency) (fun note ->
          note (Dependencies package);
          Some
            (Interface.Grants.grant
               (interface_lookups pipeline note ~is_checked:false)
               ~package entry.capabilities))
  | Signature_check key ->
      into (keyed state.signature_checks key) (fun note ->
          read pipeline note (Interface key);
          Some
            (match Hashtbl.find_opt state.interfaces key with
            | Some (Value _) ->
                checked_part
                  (fun key ->
                    ( Interface.Check.diagnostics
                        (interface_lookups pipeline note ~is_checked:false)
                        key,
                      () ))
                  key
            | Some (Failed _ | Blocked) | None -> Blocked))
  | Contract key ->
      into (keyed state.contracts key) (fun note ->
          Option.map
            (function
              | Value (checked : Infer.checked) -> Value checked.form
              | Failed diagnostics -> Failed diagnostics
              | Blocked -> Blocked)
            (type_check Infer.contract (infer_lookups pipeline note) key))
  | Checked_body key ->
      into (keyed state.checked_bodies key) (fun note ->
          type_check Infer.body (infer_lookups pipeline note) key)
  | Derived_form path ->
      into (at_path state.derived_forms path) (fun note ->
          match Infer.derived (infer_lookups pipeline note) path with
          | Some form -> Some (Value form)
          | None -> None
          | exception Reads_failed_part -> Some Blocked)
  | Body_mir key ->
      into (keyed state.body_parts key) (fun note ->
          read pipeline note (Checked_body key);
          Some
            (match Hashtbl.find_opt state.checked_bodies key with
            | Some (Value checked) -> (
                match lowered_interface pipeline note ~is_checked:true key with
                | lowered ->
                    let interface =
                      Option.map
                        (fun (lowered : Environment.lowered_interface) -> lowered.interface)
                        lowered
                    in
                    Value (Mir.body_part ?interface checked.form)
                | exception Reads_failed_part -> Blocked)
            | Some (Failed _ | Blocked) | None -> Blocked))
  | Contract_mir key ->
      into (keyed state.contract_parts key) (fun note ->
          read pipeline note (Contract key);
          Some
            (match Hashtbl.find_opt state.contracts key with
            | Some (Value form) ->
                Value
                  (Mir.contract_part
                     ~type_interface:
                       (Interface.Definition.type_interface
                          (interface_lookups pipeline note ~is_checked:true))
                     key.path form)
            | Some (Failed _ | Blocked) | None -> Blocked))
  | Generated_mir path ->
      into (at_path state.generated_parts path) (fun note ->
          read pipeline note (Derived_form path);
          Option.map
            (function
              | Value form ->
                  Value
                    ( Mir.body_part form,
                      Mir.contract_part
                        ~type_interface:
                          (Interface.Definition.type_interface
                             (interface_lookups pipeline note ~is_checked:true))
                        path form )
              | Failed _ | Blocked -> Blocked)
            (Path_table.find_opt state.derived_forms path))
  | Call_edges path ->
      into (at_path state.call_edges path) (fun note ->
          Some (computed (Mir.Call_edges.of_path (call_edge_lookups pipeline note)) path))
  | Patterns key ->
      into (keyed state.patterns key) (fun note ->
          Some
            (checked_part
               (fun key -> (Patterns.check (patterns_lookups pipeline note) key, ()))
               key))
  | Usage key ->
      into (keyed state.usage key) (fun note ->
          Some (checked_part (fun key -> (Usage.check (usage_lookups pipeline note) key, ())) key))
  | Ownership key ->
      into (keyed state.ownership key) (fun note ->
          Some
            (checked_part
               (fun key ->
                 match Ownership.check (ownership_lookups pipeline note) key with
                 | Some result -> (result.diagnostics, result.must_be_disjoint)
                 | None -> ([], []))
               key))
  | Used_packages key ->
      into (keyed state.used_packages key) (fun note ->
          Some (computed (used_packages pipeline note) key))
  | Package_check (package, check) ->
      into (keyed state.package_checks check) (fun note ->
          Some (computed (Package_checks.run (package_checks_lookups pipeline note) package) check))
  | Successors (path, viewer) ->
      let graph = call_graph pipeline viewer in
      into
        {
          stored = Call_graph.successors graph path;
          replace =
            (fun successors ->
              List.iter
                (fun node -> mark_stale pipeline (Successors (node, viewer)))
                (Call_graph.set_successors graph path successors));
          remove = (fun () -> Call_graph.remove_successors graph path);
        }
        (fun note -> Some (successors pipeline note ~viewer path))
  | Proof key ->
      into (keyed state.proofs key) (fun note ->
          Some (computed (Prover.proof (proof_lookups pipeline note)) key));
      own_template_checks pipeline key
  | Ground_types key ->
      let before = held_types pipeline key in
      into (instance_slot pipeline.ground_types key) (fun note ->
          Some
            (computed
               (Compile.ground_types (lowering_settings pipeline)
                  (stage_lowering_lookups pipeline note))
               key));
      update_holders pipeline key ~before;
      update_references pipeline key
  | Lowered key ->
      into (instance_slot pipeline.lowered key) (fun note ->
          let layout_of = instance_layout pipeline note key in
          Some
            (computed
               (fun key ->
                 match
                   Compile.lower (lowering_settings pipeline)
                     (stage_lowering_lookups pipeline note)
                     ~layout_of ~lowered:(lowered pipeline note) key
                 with
                 | lowered -> lowered
                 | exception Compile.Todo_type ty ->
                     ignore (layout_of ty);
                     Compiler_bug.bug ~stage:"Pipeline" "%s is defined as todo, and has a layout"
                       (Ground.to_string ty))
               key));
      update_references pipeline key
  | Layout ty ->
      into
        {
          stored = Type_table.find_opt pipeline.layouts ty;
          replace = Type_table.replace pipeline.layouts ty;
          remove = (fun () -> Type_table.remove pipeline.layouts ty);
        }
        (fun note ->
          Some
            (match
               Compile.layout
                 (interface_lookups pipeline note ~is_checked:true)
                 ~layout_of:(layout pipeline note) ty
             with
            | layout -> Value layout
            | exception Reads_failed_part -> Blocked
            | exception Compile.Todo_type _ -> Failed []))
  | Source _ | Packages | Modules _ | Dependencies _ | Derived_interface _ | Entry _ | Entries _
  | Imports _ | Declaration _ | Tree _ | Text _ | Place _ | Container _ | Contained _
  | Module_declarations _ | File_declarations _ | Package_declarations _ | Members _
  | Traits_declaring _ | Impl_index _ | Impls_of_type _ | Impls_of_trait _ | Law_proofs _
  | Recursion_group _ ->
      Compiler_bug.bug ~stage:"Pipeline" "%s is not computed by a stage" (Part.show part)
  | Test_key _ ->
      Compiler_bug.bug ~stage:"Pipeline" "%s is computed with its component" (Part.show part)

let compute pipeline = function
  | Part.Test_key _ :: _ as parts ->
      compute_test_keys pipeline
        (List.map
           (function
             | Part.Test_key key -> key
             | part ->
                 Compiler_bug.bug ~stage:"Pipeline" "%s is computed with test keys" (Part.show part))
           parts)
  | [ part ] -> compute_part pipeline part
  | parts ->
      compute_type_facts pipeline
        (List.map
           (function
             | Part.Type_facts path -> path
             | part ->
                 Compiler_bug.bug ~stage:"Pipeline" "%s is computed with other parts"
                   (Part.show part))
           parts)

let units pipeline (stage : Stage.t) package parts =
  match stage with
  | Type_facts ->
      let paths =
        List.filter_map (function Part.Type_facts path -> Some path | _ -> None) parts
      in
      let in_closure = Path_table.create 64 in
      List.iter (fun path -> Path_table.replace in_closure path ()) paths;
      let lookups = interface_lookups pipeline ignore ~is_checked:false in
      List.map
        (List.map (fun path -> Part.Type_facts path))
        (Path_components.of_graph
           ~successors:(fun path ->
             match type_interface lookups path with
             | Some interface ->
                 List.filter (Path_table.mem in_closure)
                   (Interface.Properties.fields_named ~package interface)
             | None -> [])
           paths)
  | _ -> List.map (fun part -> [ part ]) parts

let layout_units pipeline parts =
  let types = List.filter_map (function Part.Layout ty -> Some ty | _ -> None) parts in
  let in_closure = Type_table.create 64 in
  List.iter (fun ty -> Type_table.replace in_closure ty ()) types;
  let interface = interface_lookups pipeline ignore ~is_checked:true in
  let successors ty =
    match Compile.stored_in_place interface ty with
    | stored -> List.filter (Type_table.mem in_closure) stored
    | exception Reads_failed_part -> []
  in
  List.map
    (function
      | [ ty ] when not (List.exists (Ground_key.equal ty) (successors ty)) -> [ Part.Layout ty ]
      | cycle ->
          Compiler_bug.bug ~stage:"Pipeline"
            "%s contains itself in place, which the type checker rejects"
            (String.concat ", " (List.map Ground.to_string cycle)))
    (Type_components.of_graph ~successors types)

let constant_units pipeline parts =
  let in_closure = Part_table.create 64 in
  List.iter (fun part -> Part_table.replace in_closure part ()) parts;
  let successors (part : Part.t) =
    match part with
    | Lowered (Constant _ as key) -> (
        match Instance_table.find_opt pipeline.ground_types key with
        | Some (Value { folded_constants; _ }) ->
            List.filter (Part_table.mem in_closure)
              (List.map (fun path -> Part.Lowered (Constant path)) folded_constants)
        | Some (Failed _ | Blocked) | None -> [])
    | _ -> []
  in
  List.map
    (function
      | [ part ] when not (List.exists (Part.equal part) (successors part)) -> [ part ]
      | cycle ->
          Compiler_bug.bug ~stage:"Pipeline" "constants that read one another: %s"
            (String.concat ", " (List.map Part.show cycle)))
    (Part_components.of_graph ~successors parts)

let test_key_units pipeline parts =
  let in_closure = Part_table.create 64 in
  List.iter (fun part -> Part_table.replace in_closure part ()) parts;
  Part_components.of_graph
    ~successors:(fun (part : Part.t) ->
      match part with
      | Test_key key -> (
          match Instance_table.find_opt pipeline.lowered key with
          | Some (Value (Ok lowered)) ->
              List.filter (Part_table.mem in_closure)
                (List.map (fun reference -> Part.Test_key reference) (Compile.references lowered))
          | Some (Value (Error _) | Failed _ | Blocked) | None -> [])
      | _ -> [])
    parts

let update_groups pipeline package =
  match Hashtbl.find_opt pipeline.graphs package with
  | Some graph when Call_graph.has_changes graph ->
      let { Call_graph.touched; removed } = Call_graph.update graph in
      List.iter
        (fun node ->
          let part = Part.Successors (node, package) in
          mark_unsaved pipeline (Value part);
          discard pipeline part)
        removed;
      let groups = at_path (owner pipeline package).recursion_groups in
      let is_own node = Path.package node = package in
      List.iter
        (fun node ->
          if is_own node then begin
            pipeline.observe (Computed (Recursion_group node));
            store pipeline (Recursion_group node) (groups node)
              (match Call_graph.group graph node with
              | Blocked -> Some Blocked
              | Members [] -> None
              | Members members -> Some (Value members))
          end)
        touched;
      List.iter
        (fun node -> if is_own node then store pipeline (Recursion_group node) (groups node) None)
        removed
  | Some _ | None -> ()

let has_work pipeline package (stage : Stage.t) =
  match stage with
  | Recursion_groups -> (
      match Hashtbl.find_opt pipeline.graphs package with
      | Some graph -> Call_graph.has_changes graph
      | None -> false)
  | stage -> (
      match Hashtbl.find_opt pipeline.stale (package, stage) with
      | Some parts -> Part_table.length parts > 0
      | None -> false)

let drain_stage pipeline ~is_drained ~on_raise (stage : Stage.t) packages =
  match stage with
  | Recursion_groups -> List.iter (update_groups pipeline) packages
  | stage -> (
      let closure = Part_table.create 64 in
      let rec close part =
        if not (Part_table.mem closure part) then begin
          Part_table.replace closure part ();
          Option.iter
            (Part_table.iter (fun reader () ->
                 if
                   Stage.of_part reader = stage
                   && List.mem (Part.package reader) packages
                   && is_drained reader
                 then close reader))
            (Part_table.find_opt pipeline.readers part)
        end
      in
      List.iter
        (fun package ->
          List.iter close (List.filter is_drained (stale_parts pipeline package stage)))
        packages;
      let compute_units =
        List.iter (fun unit ->
            if List.exists (is_stale pipeline) unit then begin
              List.iter (unmark pipeline) unit;
              match compute pipeline unit with
              | () -> ()
              | exception raised ->
                  List.iter (mark_stale pipeline) unit;
                  on_raise unit raised
            end)
      in
      let parts_where keep =
        Part_table.fold (fun part () parts -> if keep part then part :: parts else parts) closure []
      in
      let all_parts () = parts_where (fun _ -> true) in
      match stage with
      | Layouts -> compute_units (layout_units pipeline (all_parts ()))
      | Lowered_code -> compute_units (constant_units pipeline (all_parts ()))
      | Test_keys -> compute_units (test_key_units pipeline (all_parts ()))
      | Ground_types -> compute_units (List.map (fun part -> [ part ]) (all_parts ()))
      | stage ->
          List.iter
            (fun package ->
              compute_units
                (units pipeline stage package
                   (parts_where (fun part -> Part.package part = package))))
            packages)

let drain_where ?on_bug pipeline ~drains requested =
  let packages = in_dependency_order pipeline requested in
  let broken = Part_table.create 0 in
  let is_drained part = is_drained pipeline part && not (Part_table.mem broken part) in
  let on_raise unit raised =
    match (on_bug, raised) with
    | Some on_bug, Compiler_bug.Bug bug ->
        List.iter (fun part -> Part_table.replace broken part ()) unit;
        on_bug bug
    | _ -> raise raised
  in
  let has_drained_work stage =
    List.exists
      (fun package ->
        has_work pipeline package stage
        && ((Part_table.length broken = 0 && not (Stage.is_lowering stage))
           || List.exists is_drained (stale_parts pipeline package stage)))
      packages
  in
  let rec next () =
    match List.find_opt (fun stage -> drains stage && has_drained_work stage) Stage.all with
    | Some stage ->
        drain_stage pipeline ~is_drained ~on_raise stage packages;
        next ()
    | None -> ()
  in
  next ()

let drain pipeline ~through requested =
  drain_where pipeline ~drains:(Stage.drains ~through) requested

let propagate ?on_bug pipeline =
  drain_where ?on_bug pipeline ~drains:(fun _ -> true) pipeline.project

type read = { dependent : Part.t; dependency : Part.t }

let definition_set paths =
  let set = Path_table.create 8 in
  List.iter (fun path -> Path_table.replace set path ()) paths;
  set

let is_of_other definition part =
  match Part.definition part with Some other -> not (Path.equal other definition) | None -> false

let drain_checks pipeline = drain pipeline ~through:Proofs pipeline.project
let is_checked part = not (Stage.is_lowering (Stage.of_part part))

let dependencies pipeline paths =
  drain_checks pipeline;
  let wanted = definition_set paths in
  Part_table.fold
    (fun dependent dependencies found ->
      match Part.definition dependent with
      | Some definition when is_checked dependent && Path_table.mem wanted definition ->
          List.fold_left
            (fun found dependency ->
              if is_of_other definition dependency then { dependent; dependency } :: found
              else found)
            found dependencies
      | Some _ | None -> found)
    pipeline.reads []

let dependents pipeline paths =
  drain_checks pipeline;
  let wanted = definition_set paths in
  Part_table.fold
    (fun dependency readers found ->
      match Part.definition dependency with
      | Some definition when Path_table.mem wanted definition ->
          Part_table.fold
            (fun dependent () found ->
              if is_checked dependent && is_of_other definition dependent then
                { dependent; dependency } :: found
              else found)
            readers found
      | Some _ | None -> found)
    pipeline.readers []

let changes pipeline other =
  drain_checks pipeline;
  drain_checks other;
  let parts = Part_table.create 1024 in
  let add part =
    match Stage.of_part part with
    | Input | Namespaces -> ()
    | _ ->
        if is_checked part && Option.is_some (Part.definition part) then
          Part_table.replace parts part ()
  in
  List.iter
    (fun pipeline ->
      Part_table.iter (fun part _ -> add part) pipeline.reads;
      Part_table.iter (fun part _ -> add part) pipeline.readers;
      List.iter
        (fun package ->
          Path_table.iter
            (fun path _ -> add (Recursion_group path))
            (owner pipeline package).recursion_groups)
        pipeline.project)
    [ pipeline; other ];
  Part_table.fold
    (fun part () changed ->
      if (stored pipeline part).is_equal_in other then changed else part :: changed)
    parts []

let update pipeline changes =
  List.iter
    (fun ((file : Path.file), text) ->
      let package = file.module_.package in
      let state =
        match Hashtbl.find_opt pipeline.states package with
        | Some state -> state
        | None ->
            Compiler_bug.bug ~stage:"Pipeline" "%s is not a package of the build"
              (Path.show_package package)
      in
      let previous = Hashtbl.find_opt state.sources file in
      let is_unchanged =
        match (previous, text) with
        | Some source, Some text -> String.equal (Source.text source) text
        | None, None -> not (List.mem file state.files)
        | Some _, None | None, Some _ -> false
      in
      if not is_unchanged then begin
        mark_unsaved pipeline (File file);
        (match text with
        | Some text ->
            Hashtbl.replace state.sources file (source_of file text);
            mark_stale pipeline (Parsed file)
        | None ->
            Hashtbl.remove state.sources file;
            forget pipeline [ Parsed file ]);
        mark_readers pipeline (Source file);
        if Option.is_none previous || Option.is_none text then begin
          let modules = state.modules in
          list_files state
            (List.filter (( <> ) file) state.files @ if Option.is_some text then [ file ] else []);
          if modules <> state.modules then mark_readers pipeline (Modules package);
          mark_stale pipeline (Namespace package)
        end
      end)
    changes

let state_parts (state : state) : Part.t list =
  let keyed table part = Hashtbl.fold (fun key _ parts -> part key :: parts) table [] in
  let at_paths table part = Path_table.fold (fun path _ parts -> part path :: parts) table [] in
  List.concat
    [
      keyed state.parsed (fun file -> Part.Parsed file);
      keyed state.resolved_names (fun (key, section) -> Part.Resolved (key, section));
      keyed state.import_checks (fun file -> Part.Import_check file);
      keyed state.trait_headers (fun key -> Part.Trait_header key);
      at_paths state.constant_values (fun path -> Part.Constant_value path);
      keyed state.headers (fun key -> Part.Header key);
      keyed state.interfaces (fun key -> Part.Interface key);
      at_paths state.derived_interfaces (fun path -> Part.Derived_interface path);
      at_paths state.type_facts (fun path -> Part.Type_facts path);
      keyed state.grants (fun dependency -> Part.Grant (state.name, dependency));
      keyed state.signature_checks (fun key -> Part.Signature_check key);
      keyed state.contracts (fun key -> Part.Contract key);
      keyed state.checked_bodies (fun key -> Part.Checked_body key);
      at_paths state.derived_forms (fun path -> Part.Derived_form path);
      keyed state.body_parts (fun key -> Part.Body_mir key);
      keyed state.contract_parts (fun key -> Part.Contract_mir key);
      at_paths state.generated_parts (fun path -> Part.Generated_mir path);
      at_paths state.call_edges (fun path -> Part.Call_edges path);
      keyed state.patterns (fun key -> Part.Patterns key);
      keyed state.usage (fun key -> Part.Usage key);
      keyed state.ownership (fun key -> Part.Ownership key);
      keyed state.used_packages (fun key -> Part.Used_packages key);
      keyed state.package_checks (fun check -> Part.Package_check (state.name, check));
      at_paths state.recursion_groups (fun path -> Part.Recursion_group path);
      keyed state.proofs (fun key -> Part.Proof key);
    ]

let mark_differences pipeline name ~(before : state option) ~(after : state option) =
  let empty () =
    let state = empty_state name ~dependencies:[] in
    state.namespace <- Some Names.empty_namespace;
    state
  in
  let before = match before with Some state -> state | None -> empty () in
  let after = match after with Some state -> state | None -> empty () in
  let namespace (state : state) = Option.value state.namespace ~default:Names.empty_namespace in
  List.iter (mark_change pipeline name) (Names.changes (namespace before) (namespace after));
  let text (state : state) file = Option.map Source.text (Hashtbl.find_opt state.sources file) in
  List.iter
    (fun file -> if text before file <> text after file then mark_readers pipeline (Source file))
    (List.sort_uniq compare (before.files @ after.files));
  if before.modules <> after.modules then mark_readers pipeline (Modules name);
  if before.dependencies <> after.dependencies then mark_readers pipeline (Dependencies name);
  let view (state : state) =
    let states = Hashtbl.create 1 in
    Hashtbl.replace states name state;
    { pipeline with states }
  in
  let parts = Part_table.create 1024 in
  List.iter (fun part -> Part_table.replace parts part ()) (state_parts before @ state_parts after);
  Part_table.iter
    (fun part () ->
      if not ((stored (view before) part).is_equal_in (view after)) then mark_readers pipeline part)
    parts

let retire pipeline (state : state) =
  let package = state.name in
  own_roots pipeline (Namespace package) [];
  Hashtbl.iter (fun key _ -> own_roots pipeline (Proof key) []) state.proofs;
  let is_own (part : Part.t) =
    match Stage.of_part part with
    | Input -> false
    | stage -> (not (Stage.is_lowering stage)) && Part.package part = package
  in
  mark_state_unsaved pipeline state;
  List.iter (fun part -> mark_unsaved pipeline (Value part)) (state_parts state);
  List.iter
    (fun part ->
      mark_unsaved pipeline (Value part);
      discard pipeline part)
    (Part_table.fold
       (fun part _ parts -> if is_own part then part :: parts else parts)
       pipeline.reads []);
  Hashtbl.filter_map_inplace
    (fun (owner, stage) parts ->
      if owner = package && not (Stage.is_lowering stage) then begin
        Part_table.iter (fun part () -> mark_unsaved pipeline (Stale part)) parts;
        None
      end
      else Some parts)
    pipeline.stale;
  Hashtbl.remove pipeline.graphs package;
  Hashtbl.remove pipeline.implied package;
  Hashtbl.remove pipeline.states package

let relayout pipeline ~(loaded : state list) (packages : Project.package list) =
  let project = List.map (fun (package : Project.package) -> package.name) packages in
  let loaded_as name = List.find_opt (fun (state : state) -> state.name = name) loaded in
  let names_before = Hashtbl.fold (fun name _ names -> name :: names) pipeline.states [] in
  List.iter
    (fun name ->
      let before = Hashtbl.find pipeline.states name in
      let is_kept =
        if List.mem name pipeline.project then List.mem name project
        else match loaded_as name with Some state -> state == before | None -> false
      in
      if not is_kept then begin
        let after = if List.mem name project then None else loaded_as name in
        mark_differences pipeline name ~before:(Some before) ~after;
        retire pipeline before;
        Option.iter (Hashtbl.replace pipeline.states name) after
      end)
    names_before;
  List.iter
    (fun (state : state) ->
      if not (Hashtbl.mem pipeline.states state.name) then begin
        mark_differences pipeline state.name ~before:None ~after:(Some state);
        Hashtbl.remove pipeline.absent state.name;
        Hashtbl.replace pipeline.states state.name state
      end)
    loaded;
  List.iter
    (fun (package : Project.package) ->
      match Hashtbl.find_opt pipeline.states package.name with
      | Some state ->
          if state.dependencies <> package.dependencies then begin
            state.dependencies <- package.dependencies;
            mark_unsaved pipeline (Package package.name);
            mark_readers pipeline (Dependencies package.name);
            mark_stale pipeline (Namespace package.name)
          end;
          update pipeline
            (List.map (fun (file, text) -> (file, Some text)) package.files
            @ List.filter_map
                (fun file -> if List.mem_assoc file package.files then None else Some (file, None))
                state.files)
      | None ->
          let state = fresh_state package.name ~dependencies:package.dependencies package.files in
          Hashtbl.remove pipeline.absent package.name;
          Hashtbl.replace pipeline.states package.name state;
          mark_state_unsaved pipeline state;
          mark_readers pipeline (Modules package.name);
          mark_readers pipeline (Dependencies package.name);
          List.iter (fun file -> mark_stale pipeline (Parsed file)) state.files;
          mark_stale pipeline (Namespace package.name))
    packages;
  let names_after = Hashtbl.fold (fun name _ names -> name :: names) pipeline.states [] in
  if List.sort compare names_before <> List.sort compare names_after then
    mark_readers pipeline Packages;
  pipeline.project <- project

let fingerprint text = Digest.BLAKE128.to_hex (Digest.BLAKE128.string text)

let is_saved_part pipeline (part : Part.t) =
  match Stage.of_part part with
  | Input | Namespaces -> false
  | stage -> Stage.is_lowering stage || List.mem (Part.package part) pipeline.project

let saved_value pipeline (entry : Entry.t) =
  match entry with
  | Value part -> if is_saved_part pipeline part then (stored pipeline part).saved () else None
  | Reads part ->
      if is_saved_part pipeline part then
        Option.map marshalled (Part_table.find_opt pipeline.reads part)
      else None
  | Stale part -> if is_saved_part pipeline part && is_stale pipeline part then Some "" else None
  | Package name ->
      if List.mem name pipeline.project then
        Option.map (fun (state : state) -> marshalled state.dependencies) (package pipeline name)
      else None
  | File file ->
      let name = file.module_.package in
      if List.mem name pipeline.project then
        Option.bind (package pipeline name) (fun (state : state) ->
            Option.map
              (fun source -> fingerprint (Source.text source))
              (Hashtbl.find_opt state.sources file))
      else None
  | Owned owner -> Option.map marshalled (Part_table.find_opt pipeline.owned owner)

let unsaved pipeline =
  drain pipeline ~through:Namespaces pipeline.project;
  List.iter (update_groups pipeline) pipeline.project;
  Entry_table.fold
    (fun entry () entries ->
      (Marshal.to_string entry [ No_sharing ], saved_value pipeline entry) :: entries)
    pipeline.unsaved []

let mark_saved pipeline = Entry_table.reset pipeline.unsaved

let restore_packages pipeline ~texts entries =
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
          let state = empty_state name ~dependencies:(Marshal.from_string dependencies 0) in
          let listed = Option.value ~default:[] (Hashtbl.find_opt files name) in
          List.iter
            (fun (file, saved) ->
              match texts file with
              | Some text when String.equal (fingerprint text) saved ->
                  Hashtbl.replace state.sources file (source_of file text)
              | Some _ | None -> ())
            listed;
          list_files state (List.map fst listed);
          Hashtbl.replace pipeline.states name state;
          pipeline.project <- name :: pipeline.project
      | _ -> ())
    entries;
  pipeline.project <- List.sort Path.compare_package pipeline.project

let restore_parts pipeline entries =
  List.iter
    (fun ((entry : Entry.t), bytes) ->
      match entry with
      | Value part when is_saved_part pipeline part -> (stored pipeline part).restore bytes
      | Reads part when is_saved_part pipeline part ->
          add_reads pipeline part (Marshal.from_string bytes 0)
      | Stale part when is_saved_part pipeline part -> mark_stale pipeline part
      | Owned owner -> Part_table.replace pipeline.owned owner (Marshal.from_string bytes 0)
      | Value _ | Reads _ | Stale _ | Package _ | File _ -> ())
    entries

let restore_namespaces pipeline =
  List.iter
    (fun name ->
      if List.mem name pipeline.project then begin
        let _, implied = namespace_and_implied pipeline (Hashtbl.find pipeline.states name) in
        let graph = call_graph pipeline name in
        List.iter
          (function
            | Part.Successors (root, _) -> ignore (Call_graph.add_root graph root) | _ -> ())
          implied
      end)
    (in_dependency_order pipeline pipeline.project)

let restore_references pipeline =
  Part_table.iter
    (fun owner roots ->
      List.iter
        (fun root ->
          Instance_table.replace pipeline.owners root
            (owner :: Option.value (Instance_table.find_opt pipeline.owners root) ~default:[]);
          ignore (References.add_root pipeline.references root))
        roots)
    pipeline.owned;
  let instances = Instance_table.create 1024 in
  let note key _ = Instance_table.replace instances key () in
  Instance_table.iter note pipeline.ground_types;
  Instance_table.iter note pipeline.lowered;
  Instance_table.iter
    (fun key () ->
      List.iter (hold pipeline key) (held_types pipeline key);
      ignore
        (References.set_successors pipeline.references key (Some (instance_edges pipeline key))))
    instances;
  settle_references pipeline

let restore ~loaded ~texts entries =
  let pipeline = create ~loaded [] in
  let entries =
    List.map (fun (key, value) -> ((Marshal.from_string key 0 : Entry.t), value)) entries
  in
  restore_packages pipeline ~texts entries;
  restore_parts pipeline entries;
  restore_namespaces pipeline;
  restore_references pipeline;
  List.iter (update_groups pipeline) pipeline.project;
  mark_saved pipeline;
  pipeline

type stage = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

let without_duplicates diagnostics =
  List.sort_uniq
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    diagnostics

let failed table key =
  match Hashtbl.find_opt table key with
  | Some (Failed diagnostics) -> diagnostics
  | Some (Value _ | Blocked) | None -> []

let definition_diagnostics pipeline (key : Names.key) stage =
  let owner = owner pipeline key.module_.package in
  match stage with
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

let package_check pipeline package check =
  Hashtbl.find_opt (owner pipeline package).package_checks check

let package_outcomes pipeline package =
  List.filter_map
    (fun check ->
      match package_check pipeline package check with
      | Some (Value outcome) -> Some outcome
      | Some (Failed _ | Blocked) | None -> None)
    (Package_checks.checks ((names_lookups pipeline).package_declarations package))

let stage_diagnostics pipeline (file : Path.file) stage =
  let names = names_lookups pipeline in
  let state = owner pipeline file.module_.package in
  let placed key diagnostics =
    match names.place key with
    | Some { file = home; base } when home = file ->
        List.map (Diagnostic.map_spans (Syntax.Span.to_source ~base)) diagnostics
    | Some _ | None -> []
  in
  let of_definitions () =
    List.concat_map
      (fun key -> placed key (definition_diagnostics pipeline key stage))
      (file_keys pipeline file)
  in
  by_span_and_code
    (match stage with
    | Resolve ->
        Option.value ~default:[] (Hashtbl.find_opt state.import_checks file) @ of_definitions ()
    | Package_checks ->
        List.concat_map
          (function
            | Package_checks.Placed diagnostics ->
                List.concat_map
                  (fun (diagnostic : Package_checks.placed) ->
                    placed diagnostic.key [ diagnostic.diagnostic ])
                  diagnostics
            | Problems _ | Packages _ -> [])
          (package_outcomes pipeline file.module_.package)
    | Interface | Infer | Patterns | Usage | Ownership -> of_definitions ())

let stages = [ Resolve; Interface; Infer; Patterns; Usage; Ownership; Package_checks ]
let check pipeline packages = drain pipeline ~through:Package_checks packages

let tables pipeline (key : Names.key) =
  drain pipeline ~through:Checked_bodies [ key.module_.package ];
  match Hashtbl.find_opt (owner pipeline key.module_.package).checked_bodies key with
  | Some (Value checked) -> Some checked.tables
  | Some (Failed _ | Blocked) | None -> None

let file_diagnostics pipeline (file : Path.file) =
  drain pipeline ~through:Package_checks [ file.module_.package ];
  without_duplicates
    ((parsed_file pipeline file).diagnostics
    @ List.concat_map (stage_diagnostics pipeline file) stages)

let manifest_problems pipeline package =
  drain pipeline ~through:Package_checks [ package ];
  List.concat_map
    (function Package_checks.Problems problems -> problems | Placed _ | Packages _ -> [])
    (package_outcomes pipeline package)

let code_packages pipeline package =
  drain pipeline ~through:Package_checks [ package ];
  match package_check pipeline package Code_packages with
  | Some (Value (Packages packages)) -> Some packages
  | Some (Value (Placed _ | Problems _) | Failed _ | Blocked) | None -> None

let state pipeline package =
  drain pipeline ~through:Recursion_groups [ package ];
  match Hashtbl.find_opt pipeline.states package with
  | Some state -> state
  | None ->
      Compiler_bug.bug ~stage:"Pipeline" "%s is not a package of the build"
        (Path.show_package package)

type proofs = { pipeline : t; keys : Names.key list }

let prove pipeline files =
  let packages =
    List.sort_uniq Path.compare_package
      (List.map (fun (file : Path.file) -> file.module_.package) files)
  in
  drain pipeline ~through:Recursion_groups packages;
  let names = names_lookups pipeline in
  let keys =
    List.concat_map
      (fun file ->
        List.filter (fun key -> Option.is_some (names.place key)) (file_keys pipeline file))
      files
  in
  List.iter
    (fun (key : Names.key) ->
      let part = Part.Proof key in
      if is_stale pipeline part || not (Hashtbl.mem (owner pipeline key.module_.package).proofs key)
      then begin
        unmark pipeline part;
        compute_part pipeline part
      end
      else own_template_checks pipeline key)
    keys;
  { pipeline; keys }

let proof proofs (key : Names.key) =
  Hashtbl.find_opt (owner proofs.pipeline key.module_.package).proofs key

let holes proofs path =
  let names = names_lookups proofs.pipeline in
  match Option.bind (names.key path) (proof proofs) with
  | Some (Value (Obligations { holes; _ })) ->
      List.filter_map
        (fun ((home : Names.key), (span : Syntax.span)) ->
          Option.map
            (fun ({ file; base } : Names.place) -> (file, base + span.start))
            (names.place home))
        holes
  | Some (Value (Unsupported _ | Not_proven_here) | Failed _ | Blocked) | None -> []

type verdicts = { lookups : Prover.Lookups.t; verdicts : (Names.key, Prover.verdict) Hashtbl.t }

let decide ?evaluator solver (proofs : proofs) =
  let lookups = proof_lookups proofs.pipeline ignore in
  let verdicts = Hashtbl.create (List.length proofs.keys) in
  List.iter
    (fun (key, verdict) -> Hashtbl.replace verdicts key verdict)
    (Prover.verdicts ?evaluator lookups solver
       (List.filter_map
          (fun key ->
            match proof proofs key with
            | Some (Value proof) -> Some (key, proof)
            | Some (Failed _ | Blocked) | None -> None)
          proofs.keys));
  { lookups; verdicts }

let verdict verdicts key = Option.value (Hashtbl.find_opt verdicts.verdicts key) ~default:[]
let states verdicts file = Prover.states verdicts.lookups ~verdict:(verdict verdicts) file
let diagnostics verdicts file = Prover.diagnostics verdicts.lookups ~verdict:(verdict verdicts) file

let parsed pipeline (file : Path.file) =
  drain pipeline ~through:Parse [ file.module_.package ];
  parsed_file pipeline file

let names pipeline packages =
  drain pipeline ~through:Namespaces packages;
  names_lookups pipeline

let resolved pipeline (key : Names.key) =
  drain pipeline ~through:Resolution [ key.module_.package ];
  let owner = owner pipeline key.module_.package in
  match
    List.filter
      (fun section ->
        match Hashtbl.find_opt owner.resolved_names (key, section) with
        | Some (Value _) -> true
        | Some (Failed _ | Blocked) | None -> false)
      Resolve.sections
  with
  | [] -> None
  | sections -> Resolve.whole ~sections (resolved pipeline ignore) key

let request pipeline packages ~through ~needs keys =
  drain pipeline ~through packages;
  List.iter
    (fun key ->
      if not (List.for_all (is_current pipeline) (needs key)) then
        Compiler_bug.bug ~stage:"Pipeline" "%s is requested, and no root of lowering reaches it"
          (Instance.to_string key))
    keys

let laid_out pipeline key =
  let part = Part.Ground_types key in
  part
  ::
  (if is_current pipeline part then
     match Instance_table.find_opt pipeline.ground_types key with
     | Some (Value { types; _ }) -> List.map (fun ty -> Part.Layout ty) types
     | Some (Failed _ | Blocked) | None -> []
   else [])

let requested table part key =
  match Instance_table.find_opt table key with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) ->
      Compiler_bug.bug ~stage:"Pipeline" "%s is requested from code with errors" (Part.show part)
  | None -> unchecked (Part.show part)

let layouts pipeline packages keys =
  request pipeline packages ~through:Lowered_code ~needs:(laid_out pipeline) keys;
  let ground_types = Type_table.create 256 in
  List.iter
    (fun key ->
      List.iter
        (fun ty -> Type_table.replace ground_types ty ())
        (requested pipeline.ground_types (Ground_types key) key).types)
    keys;
  fun ty ->
    if not (Type_table.mem ground_types ty) then
      Compiler_bug.bug ~stage:"Pipeline" "%s reads the layout of %s, which its ground types lack"
        (String.concat ", " (List.map Instance.to_string keys))
        (Ground.to_string ty);
    layout pipeline ignore ty

let interface_lookups pipeline packages =
  drain pipeline ~through:Signature_checks packages;
  interface_lookups pipeline ignore ~is_checked:true

let check_calls pipeline interface viewers key = function
  | Ok lowered ->
      List.iter
        (fun viewer ->
          Option.iter
            (fun graph ->
              Compile.check_calls interface
                ~successors:(fun path -> Option.join (Call_graph.successors graph path))
                key lowered)
            (Hashtbl.find_opt pipeline.graphs viewer))
        viewers
  | Error _ -> ()

let reached_todo_types pipeline key =
  let blocked = function Some Blocked -> true | Some (Value _ | Failed _) | None -> false in
  let is_blocked (part : Part.t) =
    match part with
    | Test_key key -> blocked (Instance_table.find_opt pipeline.test_keys key)
    | Lowered key -> blocked (Instance_table.find_opt pipeline.lowered key)
    | Layout ty -> blocked (Type_table.find_opt pipeline.layouts ty)
    | _ -> false
  in
  let visited = Part_table.create 16 in
  let rec visit todo_types (part : Part.t) =
    if Part_table.mem visited part then todo_types
    else begin
      Part_table.replace visited part ();
      match part with
      | Layout (Named { path; _ }) when (stored pipeline part).is_failed -> path :: todo_types
      | _ when is_blocked part ->
          List.fold_left visit todo_types
            (Option.value (Part_table.find_opt pipeline.reads part) ~default:[])
      | _ -> todo_types
    end
  in
  List.sort_uniq Path.compare (visit [] (Test_key key))

let lowering_requests pipeline packages : Compile.requests =
  let interface = interface_lookups pipeline packages in
  {
    settings = lowering_settings pipeline;
    source = source pipeline;
    interface;
    mir = mir_lookups pipeline ignore;
    lowered =
      (fun key ->
        request pipeline packages ~through:Lowered_code ~needs:(fun key -> [ Lowered key ]) [ key ];
        let lowered = requested pipeline.lowered (Lowered key) key in
        check_calls pipeline interface packages key lowered;
        lowered);
    test_key =
      (fun key ->
        request pipeline packages ~through:Test_keys ~needs:(fun key -> [ Test_key key ]) [ key ];
        requested pipeline.test_keys (Test_key key) key);
    reached_todo_types =
      (fun key ->
        request pipeline packages ~through:Test_keys ~needs:(fun key -> [ Test_key key ]) [ key ];
        reached_todo_types pipeline key);
    layouts = layouts pipeline packages;
  }

let main pipeline package =
  drain pipeline ~through:Namespaces [ package ];
  entry_point (names_lookups pipeline) package

let callers pipeline ~viewer path =
  drain pipeline ~through:Recursion_groups [ viewer ];
  match Hashtbl.find_opt pipeline.graphs viewer with
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
  type nonrec stage = stage =
    | Resolve
    | Interface
    | Infer
    | Patterns
    | Usage
    | Ownership
    | Package_checks

  let diagnostics stages pipeline (file : Path.file) =
    let through : Stage.t =
      if List.mem Package_checks stages then Package_checks
      else if List.exists (fun stage -> List.mem stage [ Patterns; Usage; Ownership ]) stages then
        Body_checks
      else if List.mem Infer stages then Checked_bodies
      else if List.mem Interface stages then Signature_checks
      else Import_checks
    in
    drain pipeline ~through [ file.module_.package ];
    List.concat_map (stage_diagnostics pipeline file) stages

  let checked_body pipeline (key : Names.key) =
    drain pipeline ~through:Checked_bodies [ key.module_.package ];
    match Hashtbl.find_opt (owner pipeline key.module_.package).checked_bodies key with
    | Some (Value checked) -> Some checked
    | Some (Failed _ | Blocked) | None -> None

  let derived pipeline path =
    drain pipeline ~through:Derived_forms [ Path.package path ];
    match Path_table.find_opt (owner pipeline (Path.package path)).derived_forms path with
    | Some (Value form) -> Some form
    | Some (Failed _ | Blocked) | None -> None

  let core_of_path pipeline path =
    drain pipeline ~through:Derived_forms [ Path.package path ];
    Option.bind (form_origin pipeline ignore path) (fun (origin, substitution) ->
        Option.map
          (fun form -> (form, substitution))
          (match origin with
          | Infer.Written key | Inherited key ->
              Option.map (fun (checked : Infer.checked) -> checked.form) (checked_body pipeline key)
          | Generated -> derived pipeline path))

  let proof_lookups pipeline = proof_lookups pipeline ignore

  let mir pipeline package =
    drain pipeline ~through:Mir [ package ];
    mir_lookups pipeline ignore

  let reads pipeline shown =
    match
      Part_table.fold
        (fun part reads found -> if Part.show part = shown then Some reads else found)
        pipeline.reads None
    with
    | Some reads -> List.sort compare (List.map Part.show reads)
    | None -> Compiler_bug.bug ~stage:"Pipeline" "%s is not computed" shown

  let differences hot cold =
    let parts = Part_table.create 1024 in
    List.iter
      (fun pipeline ->
        Part_table.iter (fun part _ -> Part_table.replace parts part ()) pipeline.reads;
        Hashtbl.iter
          (fun _ state ->
            Path_table.iter
              (fun path _ -> Part_table.replace parts (Recursion_group path) ())
              state.recursion_groups)
          pipeline.states)
      [ hot; cold ];
    let reads pipeline part =
      Option.map (List.sort compare) (Part_table.find_opt pipeline.reads part)
    in
    List.sort compare
      (Part_table.fold
         (fun part () differences ->
           if reads hot part <> reads cold part || not ((stored hot part).is_equal_in cold) then
             Part.show part :: differences
           else differences)
         parts [])

  type observed = { recomputed : string list; collected : string list }

  let observe pipeline run =
    let recomputed = ref [] and collected = ref [] in
    pipeline.observe <-
      (function
      | Computed part -> recomputed := Part.show part :: !recomputed
      | Collected part -> collected := Part.show part :: !collected);
    Fun.protect ~finally:(fun () -> pipeline.observe <- ignore) run;
    {
      recomputed = List.sort_uniq compare !recomputed;
      collected = List.sort_uniq compare !collected;
    }

  let root pipeline key =
    own_roots pipeline Packages
      (key :: Option.value (Part_table.find_opt pipeline.owned Packages) ~default:[])

  let ownership pipeline (key : Names.key) =
    match Hashtbl.find_opt (owner pipeline key.module_.package).ownership key with
    | Some part -> part
    | None -> unchecked (Part.show (Ownership key))
end
