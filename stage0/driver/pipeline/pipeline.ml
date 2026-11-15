module Names = Resolve.Names
module Environment = Interface.Environment

module Path_table = Hashtbl.Make (struct
  type t = Path.t

  let equal = Path.equal
  let hash path = Hashtbl.hash_param 64 256 path
end)

type 'a part = Value of 'a | Failed of Syntax.diagnostic list | Blocked

exception Reads_failed_part

type step =
  | Parse
  | Namespaces
  | Resolution
  | Constant_values
  | Headers
  | Lowered_interfaces
  | Derived_interfaces
  | Type_facts
  | Grants
  | Signature_checks
  | Type_checks
  | Mir_parts
  | Call_edges
  | Body_checks
  | Package_checks
  | Recursion_groups

type package_checks = {
  checks : Package_checks.placed list part list;
  code_packages : Path.package list part;
  manifest_problems : Package_checks.manifest_problem list part list;
}

type state = {
  name : Path.package;
  dependencies : Manifest.dependency list;
  modules : Path.module_ list;
  files : Path.file list;
  sources : (Path.file, Source.t) Hashtbl.t;
  filled : (step, unit) Hashtbl.t;
  parsed : (Path.file, Parsed.file) Hashtbl.t;
  mutable namespace : Names.namespace option;
  resolved_names : (Names.key * Resolve.section, Resolve.resolved part) Hashtbl.t;
  trait_headers : (Names.key, Resolve.trait_header part) Hashtbl.t;
  constant_values : Z.t option part Path_table.t;
  headers : (Names.key, Environment.header part) Hashtbl.t;
  interfaces : (Names.key, Environment.lowered_interface part) Hashtbl.t;
  derived_interfaces : Types.impl_interface part Path_table.t;
  type_facts : Environment.type_facts part Path_table.t;
  grants : (Path.package, Environment.grant) Hashtbl.t;
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
  mutable package_checks : package_checks option;
  file_diagnostics : (Path.file, Diagnostic.t list) Hashtbl.t;
  recursion_groups : Path.t list part Path_table.t;
  proofs : (Names.key, Prover.proof part) Hashtbl.t;
}

type t = { states : (Path.package, state) Hashtbl.t; absent : (Path.package, state) Hashtbl.t }

let fresh_state name ~dependencies (texts : (Path.file * string) list) =
  let sources = Hashtbl.create 64 in
  List.iter
    (fun ((file : Path.file), text) ->
      Hashtbl.replace sources file (Source.create ~path:(Path.show_file file) text))
    texts;
  let files = List.sort compare (List.map fst texts) in
  {
    name;
    dependencies;
    modules = List.sort_uniq compare (List.map (fun (file : Path.file) -> file.module_) files);
    files;
    sources;
    filled = Hashtbl.create 16;
    parsed = Hashtbl.create 64;
    namespace = None;
    resolved_names = Hashtbl.create 1024;
    trait_headers = Hashtbl.create 64;
    constant_values = Path_table.create 64;
    headers = Hashtbl.create 64;
    interfaces = Hashtbl.create 256;
    derived_interfaces = Path_table.create 16;
    type_facts = Path_table.create 64;
    grants = Hashtbl.create 4;
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
    package_checks = None;
    file_diagnostics = Hashtbl.create 16;
    recursion_groups = Path_table.create 64;
    proofs = Hashtbl.create 64;
  }

let create ?(loaded = []) (packages : Project.package list) =
  let states = Hashtbl.create 8 in
  List.iter (fun state -> Hashtbl.replace states state.name state) loaded;
  List.iter
    (fun (package : Project.package) ->
      Hashtbl.replace states package.name
        (fresh_state package.name ~dependencies:package.dependencies package.files))
    packages;
  { states; absent = Hashtbl.create 4 }

let owner pipeline package =
  match Hashtbl.find_opt pipeline.states package with
  | Some state -> state
  | None -> (
      match Hashtbl.find_opt pipeline.absent package with
      | Some state -> state
      | None ->
          let state = fresh_state package ~dependencies:[] [] in
          Hashtbl.replace pipeline.absent package state;
          state)

let is_filled pipeline step package = Hashtbl.mem (owner pipeline package).filled step

let fill pipeline step package compute =
  let state = owner pipeline package in
  if not (Hashtbl.mem state.filled step) then begin
    compute state;
    Hashtbl.replace state.filled step ()
  end

let unchecked name = Compiler_bug.bug ~stage:"Pipeline" "%s is not checked" name

let read_part select pipeline (key : Names.key) =
  match Hashtbl.find_opt (select (owner pipeline key.module_.package)) key with
  | Some (Value value) -> value
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> unchecked (Names.show_key key)

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

let visible_packages pipeline package =
  let seen = Hashtbl.create 8 in
  let rec visit package =
    if not (Hashtbl.mem seen package) then begin
      Hashtbl.replace seen package ();
      List.iter visit (dependency_names pipeline package)
    end
  in
  visit package;
  visit Path.standard_package;
  List.sort Path.compare_package
    (Hashtbl.fold (fun package () packages -> package :: packages) seen [])

let stored select step pipeline package key ~show =
  let state = owner pipeline package in
  match Hashtbl.find_opt (select state) key with
  | Some value -> Some value
  | None when Hashtbl.mem state.filled step -> None
  | None -> unchecked (show key)

let stored_at_path select step pipeline path =
  let state = owner pipeline (Path.package path) in
  match Path_table.find_opt (select state) path with
  | Some value -> Some value
  | None when Hashtbl.mem state.filled step -> None
  | None -> unchecked (Path.show path)

let stored_at_key select step pipeline (key : Names.key) =
  stored select step pipeline key.module_.package key ~show:Names.show_key

let namespace pipeline package =
  match (owner pipeline package).namespace with
  | Some namespace -> namespace
  | None -> unchecked (Path.show_package package)

let names_lookups pipeline =
  Names.of_namespaces ~namespace:(namespace pipeline)
    ~module_exists:(fun (module_ : Path.module_) ->
      module_ = Intrinsic.module_ || List.mem module_ (modules pipeline module_.package))
    ~split_module:
      (Path.split_module ~is_package:(fun name -> Option.is_some (package pipeline name)))
    ~dependency_names:(dependency_names pipeline)

let fill_parse pipeline package =
  fill pipeline Parse package (fun state ->
      List.iter
        (fun file -> Hashtbl.replace state.parsed file (Parsed.parse (source pipeline file)))
        state.files)

let parsed_file pipeline (file : Path.file) =
  match Hashtbl.find_opt (owner pipeline file.module_.package).parsed file with
  | Some parsed -> parsed
  | None -> unchecked (Path.show_file file)

let rec fill_namespaces pipeline package =
  List.iter
    (fun visible ->
      if visible <> package && not (is_filled pipeline Namespaces visible) then
        fill_namespaces pipeline visible)
    (visible_packages pipeline package);
  fill_parse pipeline package;
  fill pipeline Namespaces package (fun state ->
      state.namespace <-
        Some
          (Names.namespace (names_lookups pipeline) package
             (List.map
                (fun module_ ->
                  ( module_,
                    List.filter_map
                      (fun (file : Path.file) ->
                        if file.module_ = module_ then
                          let parsed = Hashtbl.find state.parsed file in
                          Some
                            (file, { Syntax.uses = parsed.uses; definitions = parsed.definitions })
                        else None)
                      state.files ))
                state.modules)))

let package_keys pipeline package =
  List.map Names.key_of ((names_lookups pipeline).package_declarations package)

let file_keys pipeline file = List.map Names.key_of ((names_lookups pipeline).declarations_in file)

let fill_resolution pipeline package =
  fill_namespaces pipeline package;
  fill pipeline Resolution package (fun state ->
      let names = names_lookups pipeline in
      List.iter
        (fun (declaration : Names.declaration) ->
          let key = Names.key_of declaration in
          let sections = Resolve.resolve names key in
          List.iter
            (fun section ->
              Hashtbl.replace state.resolved_names (key, section)
                (match List.assoc_opt section sections with
                | Some (Ok resolved) -> Value resolved
                | Some (Error diagnostics) -> Failed diagnostics
                | None -> Blocked))
            Resolve.sections;
          if declaration.kind = Trait then
            Hashtbl.replace state.trait_headers key
              (match (names.definition key, Hashtbl.find state.resolved_names (key, Interface)) with
              | Some definition, Value resolved -> (
                  match Resolve.trait_header definition resolved with
                  | Some header -> Value header
                  | None -> Blocked)
              | _ -> Blocked))
        (names.package_declarations package))

let resolved pipeline section (key : Names.key) =
  Option.map value
    (stored
       (fun owner -> owner.resolved_names)
       Resolution pipeline key.module_.package (key, section)
       ~show:(fun (key, _) -> Names.show_key key))

let interface_lookups pipeline : Interface.Lookups.t =
  let names = names_lookups pipeline in
  let lowered_interface key =
    Option.map value (stored_at_key (fun owner -> owner.interfaces) Lowered_interfaces pipeline key)
  in
  {
    names;
    resolved = resolved pipeline;
    trait_header =
      (fun path ->
        Option.bind (names.key path) (fun key ->
            Option.map value
              (stored_at_key (fun owner -> owner.trait_headers) Resolution pipeline key)));
    constant_value =
      (fun path ->
        Option.bind
          (stored_at_path (fun owner -> owner.constant_values) Constant_values pipeline path)
          value);
    header =
      (fun key ->
        Option.map value (stored_at_key (fun owner -> owner.headers) Headers pipeline key));
    lowered_interface;
    derived_interface =
      (fun path ->
        (match path with
        | Derived { type_; _ } ->
            Option.iter (fun key -> ignore (lowered_interface key)) (names.key type_)
        | _ -> ());
        Option.map value
          (stored_at_path (fun owner -> owner.derived_interfaces) Derived_interfaces pipeline path));
    type_facts =
      (fun path ->
        Option.map value (stored_at_path (fun owner -> owner.type_facts) Type_facts pipeline path));
    granted =
      (fun package dependency ->
        stored
          (fun owner -> owner.grants)
          Grants pipeline package dependency
          ~show:(fun dependency ->
            Path.show_package package ^ " to " ^ Path.show_package dependency));
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

let fill_type_facts pipeline package state =
  let lookups = interface_lookups pipeline in
  let type_interface path =
    match computed (Interface.Definition.type_interface lookups) path with
    | Value interface -> interface
    | Failed _ | Blocked -> None
  in
  let types =
    List.filter_map
      (fun (declaration : Names.declaration) ->
        match declaration.kind with
        | Type when declaration.ordinal = 0 -> Some declaration.path
        | _ -> None)
      (lookups.names.package_declarations package)
  in
  List.iter
    (fun component ->
      let interfaces = List.map (fun path -> (path, type_interface path)) component in
      let facts =
        if List.for_all (fun (_, interface) -> Option.is_some interface) interfaces then
          computed
            (Interface.Properties.component_facts lookups)
            (List.filter_map
               (fun (path, interface) -> Option.map (fun interface -> (path, interface)) interface)
               interfaces)
        else Blocked
      in
      match facts with
      | Value facts ->
          List.iter
            (fun (path, facts) -> Path_table.replace state.type_facts path (Value facts))
            facts
      | Failed _ | Blocked ->
          List.iter (fun path -> Path_table.replace state.type_facts path Blocked) component)
    (Path_components.of_graph
       ~successors:(fun path ->
         match type_interface path with
         | Some interface -> Interface.Properties.fields_named ~package interface
         | None -> [])
       types)

let rec fill_interfaces pipeline package =
  List.iter
    (fun visible ->
      if visible <> package && not (is_filled pipeline Signature_checks visible) then
        fill_interfaces pipeline visible)
    (visible_packages pipeline package);
  fill_resolution pipeline package;
  let each select compute =
    List.iter
      (fun (declaration : Names.declaration) ->
        if select declaration then compute (Names.key_of declaration))
      ((names_lookups pipeline).package_declarations package)
  in
  fill pipeline Constant_values package (fun state ->
      let lookups = interface_lookups pipeline in
      each
        (fun declaration ->
          declaration.ordinal = 0
          && (declaration.kind = Constant || declaration.kind = Member_constant))
        (fun key ->
          Path_table.replace state.constant_values key.path
            (computed (Interface.Constants.value_of lookups) key.path)));
  fill pipeline Headers package (fun state ->
      let lookups = interface_lookups pipeline in
      each
        (fun declaration ->
          declaration.kind = Trait || declaration.kind = Impl || declaration.kind = Capability)
        (fun key ->
          Hashtbl.replace state.headers key
            (match computed (Interface.Definition.header lookups) key with
            | Value (Some (Ok header)) -> Value header
            | Value (Some (Error (_ :: _ as diagnostics))) -> Failed diagnostics
            | Value (Some (Error [])) | Value None | Failed _ | Blocked -> Blocked)));
  fill pipeline Lowered_interfaces package (fun state ->
      let lookups = interface_lookups pipeline in
      let lower key =
        Hashtbl.replace state.interfaces key
          (match computed (Interface.Definition.lower lookups) key with
          | Value lowered -> interface_part lowered
          | Failed _ | Blocked -> Blocked)
      in
      each (fun _ -> true) lower);
  fill pipeline Derived_interfaces package (fun state ->
      let lookups = interface_lookups pipeline in
      List.iter
        (fun (_, (impl : Path.t)) ->
          match impl with
          | Derived { type_; trait } ->
              Path_table.replace state.derived_interfaces impl
                (match
                   computed
                     (fun trait -> Interface.Impls.derived_interface lookups ~type_ ~trait)
                     trait
                 with
                | Value (Some interface) -> Value interface
                | Value None | Failed _ | Blocked -> Blocked)
          | _ -> ())
        (lookups.names.impl_index package).impls);
  fill pipeline Type_facts package (fill_type_facts pipeline package);
  fill pipeline Grants package (fun state ->
      let lookups = interface_lookups pipeline in
      List.iter
        (fun (entry : Manifest.dependency) ->
          if not (Hashtbl.mem state.grants entry.package) then
            Hashtbl.replace state.grants entry.package
              (Interface.Grants.grant lookups ~package entry))
        state.dependencies);
  fill pipeline Signature_checks package (fun state ->
      let lookups = interface_lookups pipeline in
      let checked = ref [] in
      each
        (fun _ -> true)
        (fun key ->
          match Hashtbl.find state.interfaces key with
          | Value _ -> (
              match checked_part (fun key -> (Interface.Check.diagnostics lookups key, ())) key with
              | Value () -> ()
              | (Failed _ | Blocked) as part -> checked := (key, part) :: !checked)
          | Failed _ | Blocked -> ());
      List.iter (fun (key, part) -> Hashtbl.replace state.interfaces key part) !checked)

let impl_methods pipeline package =
  let names = names_lookups pipeline in
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
    (names.impl_index package).impls

let checked_body pipeline key = read_part (fun owner -> owner.checked_bodies) pipeline key
let checked_core pipeline key = (checked_body pipeline key).form

let infer_lookups pipeline : Infer.Lookups.t =
  {
    interface = interface_lookups pipeline;
    contract = read_part (fun owner -> owner.contracts) pipeline;
  }

let derived_paths pipeline package =
  List.filter
    (function Path.Method { owner = Derived _; _ } -> true | _ -> false)
    (impl_methods pipeline package)

let type_check run lookups key =
  match run lookups key with
  | Some (Ok checked) -> Some (Value checked)
  | Some (Error []) -> Some Blocked
  | Some (Error diagnostics) -> Some (Failed diagnostics)
  | None -> None
  | exception Reads_failed_part -> Some Blocked

let fill_type_checks pipeline package =
  fill_interfaces pipeline package;
  fill pipeline Type_checks package (fun state ->
      let lookups = infer_lookups pipeline in
      let keys = package_keys pipeline package in
      List.iter
        (fun key ->
          Option.iter
            (fun part ->
              Hashtbl.replace state.contracts key
                (match part with
                | Value (checked : Infer.checked) -> Value checked.form
                | (Failed _ | Blocked) as failed -> failed))
            (type_check Infer.contract lookups key))
        keys;
      List.iter
        (fun key ->
          Option.iter (Hashtbl.replace state.checked_bodies key) (type_check Infer.body lookups key))
        keys;
      List.iter
        (fun path ->
          match Infer.derived lookups path with
          | Some form -> Path_table.replace state.derived_forms path (Value form)
          | None -> ()
          | exception Reads_failed_part -> Path_table.replace state.derived_forms path Blocked)
        (derived_paths pipeline package))

let form_origin pipeline =
  Infer.form_origin (interface_lookups pipeline) ~is_derived:(fun path ->
      Path_table.mem (owner pipeline (Path.package path)).derived_forms path)

let fill_mir pipeline package =
  fill_type_checks pipeline package;
  fill pipeline Mir_parts package (fun state ->
      let lookups = interface_lookups pipeline in
      let type_interface = Interface.Definition.type_interface lookups in
      List.iter
        (fun (key : Names.key) ->
          Hashtbl.replace state.body_parts key
            (match Hashtbl.find_opt state.checked_bodies key with
            | Some (Value checked) ->
                let interface =
                  Option.map
                    (fun (lowered : Environment.lowered_interface) -> lowered.interface)
                    (lookups.lowered_interface key)
                in
                Value (Mir.body_part ?interface checked.form)
            | Some (Failed _ | Blocked) | None -> Blocked);
          Hashtbl.replace state.contract_parts key
            (match Hashtbl.find_opt state.contracts key with
            | Some (Value form) -> Value (Mir.contract_part ~type_interface key.path form)
            | Some (Failed _ | Blocked) | None -> Blocked))
        (package_keys pipeline package);
      List.iter
        (fun path ->
          Option.iter
            (fun form ->
              Path_table.replace state.generated_parts path
                (match form with
                | Value form ->
                    Value (Mir.body_part form, Mir.contract_part ~type_interface path form)
                | Failed _ | Blocked -> Blocked))
            (Path_table.find_opt state.derived_forms path))
        (derived_paths pipeline package))

let mir_lookups pipeline : Mir.lookups =
  {
    form_origin = form_origin pipeline;
    body_part = read_part (fun owner -> owner.body_parts) pipeline;
    contract_part = read_part (fun owner -> owner.contract_parts) pipeline;
    generated_parts =
      (fun path ->
        match Path_table.find_opt (owner pipeline (Path.package path)).generated_parts path with
        | Some (Value parts) -> parts
        | Some (Failed _ | Blocked) -> raise Reads_failed_part
        | None -> unchecked (Path.show path));
  }

let call_edge_lookups pipeline : Mir.Call_edges.lookups =
  { interface = interface_lookups pipeline; mir = mir_lookups pipeline }

let fill_call_edges pipeline package =
  List.iter (fill_mir pipeline) (visible_packages pipeline package);
  fill pipeline Call_edges package (fun state ->
      let lookups = call_edge_lookups pipeline in
      List.iter
        (fun path ->
          Path_table.replace state.call_edges path (computed (Mir.Call_edges.of_path lookups) path))
        (List.map
           (fun (declaration : Names.declaration) -> declaration.path)
           (lookups.interface.names.package_declarations package)
        @ impl_methods pipeline package))

let call_edge_part pipeline path =
  let package = Path.package path in
  match Path_table.find_opt (owner pipeline package).call_edges path with
  | Some part -> part
  | None when is_filled pipeline Call_edges package -> Value []
  | None -> unchecked (Path.show path)

let call_edges pipeline path = value (call_edge_part pipeline path)

let lowering_lookups pipeline packages : Compile.Lookups.t =
  List.iter
    (fun package -> List.iter (fill_call_edges pipeline) (visible_packages pipeline package))
    packages;
  {
    source = source pipeline;
    interface = interface_lookups pipeline;
    mir = mir_lookups pipeline;
    call_edges = call_edges pipeline;
  }

let patterns_lookups pipeline : Patterns.Lookups.t =
  { core = (fun key -> Some (checked_core pipeline key)); interface = interface_lookups pipeline }

let usage_lookups pipeline : Usage.Lookups.t =
  {
    names = names_lookups pipeline;
    resolved = resolved pipeline;
    tables = (fun key -> Some (checked_body pipeline key).tables);
  }

let ownership_lookups pipeline : Ownership.Lookups.t =
  {
    graph = (fun key -> Mir.graph (read_part (fun owner -> owner.body_parts) pipeline key));
    interface = interface_lookups pipeline;
  }

let used_packages pipeline (key : Names.key) =
  let { Infer.form; evidence_packages; _ } = checked_body pipeline key in
  match Resolve.whole (resolved pipeline) key with
  | Some resolved -> Package_checks.used_packages resolved ~evidence_packages form
  | None -> raise Reads_failed_part

let fill_body_checks pipeline package =
  List.iter (fill_type_checks pipeline) (visible_packages pipeline package);
  fill_mir pipeline package;
  fill pipeline Body_checks package (fun state ->
      let keys = package_keys pipeline package in
      let compute table check =
        List.iter (fun key -> Hashtbl.replace table key (checked_part check key)) keys
      in
      let patterns = patterns_lookups pipeline in
      compute state.patterns (fun key -> (Patterns.check patterns key, ()));
      let usage = usage_lookups pipeline in
      compute state.usage (fun key -> (Usage.check usage key, ()));
      let ownership = ownership_lookups pipeline in
      compute state.ownership (fun key ->
          match Ownership.check ownership key with
          | Some result -> (result.diagnostics, result.must_be_disjoint)
          | None -> ([], []));
      List.iter
        (fun key -> Hashtbl.replace state.used_packages key (computed (used_packages pipeline) key))
        keys)

let package_checks_lookups pipeline : Package_checks.Lookups.t =
  {
    dependencies = dependencies pipeline;
    interface = interface_lookups pipeline;
    core = (fun key -> Some (checked_core pipeline key));
    used_packages = read_part (fun owner -> owner.used_packages) pipeline;
  }

type stage = Resolve | Interface | Infer | Patterns | Usage | Ownership | Package_checks

let without_duplicates diagnostics =
  List.sort_uniq
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code, left.message) (right.span, right.code, right.message))
    diagnostics

let package_part pipeline package =
  match (owner pipeline package).package_checks with
  | Some part -> part
  | None -> unchecked (Path.show_package package)

let part_diagnostics select pipeline (key : Names.key) =
  match Hashtbl.find_opt (select (owner pipeline key.module_.package)) key with
  | Some (Failed diagnostics) -> diagnostics
  | Some (Value _ | Blocked) -> []
  | None -> unchecked (Names.show_key key)

let definition_diagnostics pipeline (key : Names.key) = function
  | Resolve ->
      List.concat_map
        (fun section ->
          match Hashtbl.find (owner pipeline key.module_.package).resolved_names (key, section) with
          | Failed diagnostics -> diagnostics
          | Value _ | Blocked -> [])
        Resolve.sections
  | Interface ->
      without_duplicates
        ((match Hashtbl.find_opt (owner pipeline key.module_.package).headers key with
           | Some (Failed diagnostics) -> diagnostics
           | Some (Value _ | Blocked) | None -> [])
        @ part_diagnostics (fun owner -> owner.interfaces) pipeline key)
  | Infer ->
      let failed table =
        match Hashtbl.find_opt table key with
        | Some (Failed diagnostics) -> diagnostics
        | Some (Value _ | Blocked) | None -> []
      in
      let owner = owner pipeline key.module_.package in
      failed owner.contracts @ failed owner.checked_bodies
  | Patterns -> part_diagnostics (fun owner -> owner.patterns) pipeline key
  | Usage -> part_diagnostics (fun owner -> owner.usage) pipeline key
  | Ownership -> part_diagnostics (fun owner -> owner.ownership) pipeline key
  | Package_checks -> []

let by_span_and_code diagnostics =
  List.sort
    (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))
    diagnostics

let used_imports pipeline file =
  let used =
    List.concat_map
      (fun key ->
        List.map
          (fun section ->
            match
              Hashtbl.find (owner pipeline key.Names.module_.package).resolved_names (key, section)
            with
            | Value resolved -> Some resolved.used_imports
            | Failed _ | Blocked -> None)
          Resolve.sections)
      (file_keys pipeline file)
  in
  if List.for_all Option.is_some used then Some (List.concat_map Option.get used) else None

let import_diagnostics pipeline (file : Path.file) =
  let parsed = parsed_file pipeline file in
  Resolve.file_diagnostics (names_lookups pipeline) file
    { uses = parsed.uses; definitions = parsed.definitions }
    ~text:(Source.text (source pipeline file))
    ~used:(used_imports pipeline file)

let stage_diagnostics pipeline (file : Path.file) stage =
  let names = names_lookups pipeline in
  let of_definitions () =
    List.concat_map
      (fun key ->
        match names.base key with
        | Some (_, base) ->
            List.map
              (Diagnostic.map_spans (Syntax.Span.to_source ~base))
              (definition_diagnostics pipeline key stage)
        | None -> [])
      (file_keys pipeline file)
  in
  by_span_and_code
    (match stage with
    | Resolve -> import_diagnostics pipeline file @ of_definitions ()
    | Package_checks ->
        List.filter_map
          (fun (placed : Package_checks.placed) ->
            if placed.file = file then Some placed.diagnostic else None)
          (List.concat_map
             (function Value placed -> placed | Failed _ | Blocked -> [])
             (package_part pipeline file.module_.package).checks)
    | Interface | Infer | Patterns | Usage | Ownership -> of_definitions ())

let stages = [ Resolve; Interface; Infer; Patterns; Usage; Ownership; Package_checks ]

let fill_package_checks pipeline package =
  fill_body_checks pipeline package;
  fill pipeline Package_checks package (fun state ->
      let lookups = package_checks_lookups pipeline in
      state.package_checks <-
        Some
          {
            checks =
              List.map (fun check -> computed check ()) (Package_checks.checks lookups package);
            code_packages = computed (Package_checks.code_packages lookups) package;
            manifest_problems =
              [
                computed (Package_checks.grant_problems lookups) package;
                computed (Package_checks.unused_dependencies lookups) package;
              ];
          };
      List.iter
        (fun file ->
          Hashtbl.replace state.file_diagnostics file
            (without_duplicates
               ((Hashtbl.find state.parsed file).diagnostics
               @ List.concat_map (stage_diagnostics pipeline file) stages)))
        state.files)

let check pipeline packages =
  List.iter
    (fun package ->
      fill_package_checks pipeline package;
      fill_call_edges pipeline package)
    packages

let tables pipeline (key : Names.key) =
  fill_type_checks pipeline key.module_.package;
  match Hashtbl.find_opt (owner pipeline key.module_.package).checked_bodies key with
  | Some (Value checked) -> Some checked.tables
  | Some (Failed _ | Blocked) | None -> None

let file_diagnostics pipeline (file : Path.file) =
  match Hashtbl.find_opt (owner pipeline file.module_.package).file_diagnostics file with
  | Some diagnostics -> diagnostics
  | None -> unchecked (Path.show_file file)

let manifest_problems pipeline package =
  List.concat_map
    (function Value problems -> problems | Failed _ | Blocked -> [])
    (package_part pipeline package).manifest_problems

let code_packages pipeline package =
  match (package_part pipeline package).code_packages with
  | Value packages -> Some packages
  | Failed _ | Blocked -> None

let recursion_groups pipeline ~visible package state =
  let lookups = call_edge_lookups pipeline in
  let successors = Path_table.create 256 in
  let successors_of path =
    match Path_table.find_opt successors path with
    | Some part -> part
    | None ->
        let part =
          match call_edge_part pipeline path with
          | (Failed _ | Blocked) as failed -> failed
          | Value callees ->
              computed
                (fun path -> callees @ Mir.Call_edges.implementations lookups ~visible path)
                path
        in
        Path_table.replace successors path part;
        part
  in
  let blocked = Path_table.create 16 in
  let is_blocked path =
    Path_table.mem blocked path
    ||
    match successors_of path with
    | Failed _ | Blocked -> true
    | Value callees -> List.exists (Path_table.mem blocked) callees
  in
  List.iter
    (fun component ->
      let is_component_blocked = List.exists is_blocked component in
      if is_component_blocked then
        List.iter (fun path -> Path_table.replace blocked path ()) component;
      let members =
        match component with
        | [ path ] -> (
            match successors_of path with
            | Value callees when List.exists (Path.equal path) callees -> component
            | Value _ | Failed _ | Blocked -> [])
        | members -> members
      in
      List.iter
        (fun path ->
          if Path.package path = package then
            Path_table.replace state.recursion_groups path
              (if is_component_blocked then Blocked else Value members))
        component)
    (Path_components.of_graph
       ~successors:(fun path ->
         match successors_of path with Value callees -> callees | Failed _ | Blocked -> [])
       (List.map
          (fun (declaration : Names.declaration) -> declaration.path)
          (lookups.interface.names.package_declarations package)))

let fill_recursion_groups pipeline package =
  let visible = visible_packages pipeline package in
  List.iter (fill_call_edges pipeline) visible;
  fill pipeline Recursion_groups package (recursion_groups pipeline ~visible package)

let state pipeline package =
  check pipeline [ package ];
  fill_recursion_groups pipeline package;
  match Hashtbl.find_opt pipeline.states package with
  | Some state -> state
  | None ->
      Compiler_bug.bug ~stage:"Pipeline" "%s is not a package of the build"
        (Path.show_package package)

let recursion_group pipeline path =
  match Path_table.find_opt (owner pipeline (Path.package path)).recursion_groups path with
  | Some (Value members) -> members
  | Some (Failed _ | Blocked) -> raise Reads_failed_part
  | None -> []

let proof_lookups pipeline : Prover.Lookups.t =
  {
    source = source pipeline;
    interface = interface_lookups pipeline;
    mir = mir_lookups pipeline;
    patterns = read_part (fun owner -> owner.patterns) pipeline;
    must_be_disjoint = read_part (fun owner -> owner.ownership) pipeline;
    recursion_group = recursion_group pipeline;
  }

type proofs = { pipeline : t; keys : Names.key list }

let prove pipeline files =
  List.iter
    (fun package ->
      fill_body_checks pipeline package;
      fill_recursion_groups pipeline package)
    (List.sort_uniq Path.compare_package
       (List.map (fun (file : Path.file) -> file.module_.package) files));
  let lookups = proof_lookups pipeline in
  let keys =
    List.concat_map
      (fun file ->
        List.filter
          (fun key -> Option.is_some (lookups.interface.names.base key))
          (file_keys pipeline file))
      files
  in
  List.iter
    (fun (key : Names.key) ->
      let owner = owner pipeline key.module_.package in
      if not (Hashtbl.mem owner.proofs key) then
        Hashtbl.replace owner.proofs key (computed (Prover.proof lookups) key))
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
          Option.map (fun (file, base) -> (file, base + span.start)) (names.base home))
        holes
  | Some (Value (Unsupported _ | Not_proven_here) | Failed _ | Blocked) | None -> []

type verdicts = { lookups : Prover.Lookups.t; verdicts : (Names.key, Prover.verdict) Hashtbl.t }

let decide ?evaluator solver (proofs : proofs) =
  let lookups = proof_lookups proofs.pipeline in
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
  fill_parse pipeline file.module_.package;
  parsed_file pipeline file

let names pipeline packages =
  List.iter (fill_namespaces pipeline) packages;
  names_lookups pipeline

let resolved pipeline (key : Names.key) =
  fill_resolution pipeline key.module_.package;
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
  | sections -> Resolve.whole ~sections (resolved pipeline) key

let interface_lookups pipeline packages =
  List.iter (fill_interfaces pipeline) packages;
  interface_lookups pipeline

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
    let package = file.module_.package in
    if List.mem Package_checks stages then fill_package_checks pipeline package
    else if List.exists (fun stage -> List.mem stage [ Patterns; Usage; Ownership ]) stages then
      fill_body_checks pipeline package
    else if List.mem Infer stages then fill_type_checks pipeline package
    else if List.mem Interface stages then fill_interfaces pipeline package
    else fill_resolution pipeline package;
    List.concat_map (stage_diagnostics pipeline file) stages

  let checked_body pipeline (key : Names.key) =
    fill_type_checks pipeline key.module_.package;
    match Hashtbl.find_opt (owner pipeline key.module_.package).checked_bodies key with
    | Some (Value checked) -> Some checked
    | Some (Failed _ | Blocked) | None -> None

  let derived pipeline path =
    fill_type_checks pipeline (Path.package path);
    match Path_table.find_opt (owner pipeline (Path.package path)).derived_forms path with
    | Some (Value form) -> Some form
    | Some (Failed _ | Blocked) | None -> None

  let core_of_path pipeline path =
    fill_type_checks pipeline (Path.package path);
    Option.bind (form_origin pipeline path) (fun (origin, substitution) ->
        Option.map
          (fun form -> (form, substitution))
          (match origin with
          | Infer.Written key | Inherited key ->
              Option.map (fun (checked : Infer.checked) -> checked.form) (checked_body pipeline key)
          | Generated -> derived pipeline path))

  let proof_lookups = proof_lookups

  let mir pipeline package =
    List.iter (fill_mir pipeline) (visible_packages pipeline package);
    mir_lookups pipeline

  let ownership pipeline (key : Names.key) =
    match Hashtbl.find_opt (owner pipeline key.module_.package).ownership key with
    | Some part -> part
    | None -> unchecked (Names.show_key key)
end
