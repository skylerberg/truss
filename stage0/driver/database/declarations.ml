let kinds : Resolve.Names.kind list =
  [
    Function;
    Type;
    Trait;
    Capability;
    Constant;
    Theorem;
    Method;
    Member_constant;
    Impl;
    Test;
    Law_proof;
  ]

let visibilities : Resolve.Names.visibility list = [ Private; Internal; Public; Public_opaque ]

let named_kinds : Resolve.Names.named list =
  [ Function; Type; Trait; Capability; Constant; Theorem ]

let rank values value =
  match List.find_index (fun candidate -> candidate = value) values with
  | Some position -> position
  | None -> Compiler_bug.raise_bug ~stage:"Database" "a value has no rank among its kind's values"

let decode_key bytes : Resolve.Names.key = Marshal.from_string bytes 0
let decode_file bytes : Path.file = Marshal.from_string bytes 0
let decode_kind rank : Resolve.Names.kind = List.nth kinds rank
let rank_kind kind = rank kinds kind

let decode_declaration (row : Store.definition) : Resolve.Names.declaration =
  {
    key = decode_key row.key;
    kind = decode_kind row.kind;
    visibility = List.nth visibilities row.visibility;
    generic = row.is_generic;
  }

let decode_entry (row : Store.entry) : Resolve.Names.entry =
  {
    name = row.name;
    kind = List.nth named_kinds row.kind;
    visibility = List.nth visibilities row.visibility;
    generic = row.is_generic;
  }

let encode_entry ~source ~(module_ : Path.module_) ~file_name position (entry : Resolve.Names.entry)
    : Store.entry =
  {
    file = source;
    position;
    module_ = Ids.of_module module_;
    file_name;
    name = entry.name;
    kind = rank named_kinds entry.kind;
    visibility = rank visibilities entry.visibility;
    is_generic = entry.generic;
  }

let written_origin = 0
let derived_impl_origin = 1
let inherited_method_origin = 2
let derived_method_origin = 3

type impl_entry = { declared_in : Path.module_; entry : (Path.t * Path.t) * Path.t }

let name_law_proofs ~package ~law ~type_ = Printf.sprintf "%s %s %d" package law type_

let make_lookups store ~(note : Kind.lookup -> int -> string -> unit) ~is_package
    ~list_dependency_names : Resolve.Names.lookups =
  let locate (package : Path.package) = Store.locate_schema store package in
  let look_up (lookup : Kind.lookup) (key : Resolve.Names.key) read =
    let id = Ids.of_key key in
    note lookup id "";
    read (locate key.module_.package) id
  in
  let require (key : Resolve.Names.key) = function
    | Some value -> value
    | None ->
        Compiler_bug.raise_bug ~stage:"Database" "%s is not declared" (Resolve.Names.show_key key)
  in
  let read_column lookup key find =
    look_up lookup key (fun schema id -> require key (find store schema ~definition:id))
  in
  let list_written schema selection =
    List.filter_map
      (fun (row : Store.definition) ->
        if row.origin = written_origin then Some (row, decode_declaration row) else None)
      (Store.list_definitions store schema selection)
  in
  let list_sorted schema selection =
    List.sort
      (fun (left : Resolve.Names.declaration) (right : Resolve.Names.declaration) ->
        Resolve.Namespace.compare_key left.key right.key)
      (List.map snd (list_written schema selection))
  in
  let list_members owner name =
    let owner_id = Ids.of_path owner in
    note Members owner_id name;
    List.sort Resolve.Namespace.compare_key
      (List.map decode_key
         (Store.list_member_keys store
            (locate (Path.locate_package owner))
            ~owner:owner_id ~member:name ~origin:written_origin))
  in
  let list_impl_entries package selection =
    List.map
      (fun (_, entry) -> entry.entry)
      (List.sort
         (fun ((left : Store.impl), left_entry) ((right : Store.impl), right_entry) ->
           compare (left_entry.declared_in, left.position) (right_entry.declared_in, right.position))
         (List.map
            (fun (impl : Store.impl) -> (impl, (Marshal.from_string impl.entry 0 : impl_entry)))
            (Store.list_impls store (locate package) ~package:(Path.show_package package) selection)))
  in
  {
    find =
      (fun module_ name ->
        let id = Ids.of_module module_ in
        note Entry id name;
        Option.map decode_entry (Store.find_entry store (locate module_.package) ~module_:id ~name));
    list_entries =
      (fun module_ ->
        note Entries (Ids.of_module module_) "";
        List.map decode_entry
          (Store.list_module_entries store (locate module_.package) ~module_:(Ids.of_module module_)));
    list_imports =
      (fun key ->
        look_up Imports key (fun schema id ->
            match (require key (Store.find_placement store schema ~id)).file with
            | Some file ->
                List.map
                  (fun (name, module_) -> (name, (Marshal.from_string module_ 0 : Path.module_)))
                  (Store.list_imports store schema ~file)
            | None -> []));
    module_exists =
      (fun module_ ->
        let id = Ids.of_module module_ in
        note Module id "";
        Store.has_module store (locate module_.package) ~module_:id);
    split_module =
      (fun parts ->
        note Packages 0 "";
        Path.split_module ~is_package parts);
    list_dependency_names =
      (fun package ->
        note Dependencies (Ids.of_package package) "";
        list_dependency_names package);
    find_key =
      (fun (path : Path.t) ->
        match path with
        | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ }
          ->
            let key : Resolve.Names.key = { module_; path; ordinal = 0 } in
            look_up Declaration key (fun schema id ->
                if module_ = Well_known.intrinsic_module then None
                else Option.map (fun _ -> key) (Store.find_declared store schema ~id))
        | Method { owner; name; _ } | Member_constant { owner; name } ->
            List.find_opt
              (fun (key : Resolve.Names.key) -> Path.equal key.path path)
              (list_members owner name)
        | Derived _ | Unresolved _ -> None);
    read_declaration =
      (fun key ->
        look_up Declaration key (fun schema id ->
            let ({ kind; visibility; is_generic } : Store.declared) =
              require key (Store.find_declared store schema ~id)
            in
            {
              Resolve.Names.key;
              kind = decode_kind kind;
              visibility = List.nth visibilities visibility;
              generic = is_generic;
            }));
    list_declarations =
      (fun module_ ->
        note Module_declarations (Ids.of_module module_) "";
        list_sorted (locate module_.package) (Of_module (Ids.of_module module_)));
    list_declarations_in =
      (fun file ->
        note File_declarations (Ids.of_file file) "";
        List.map snd (list_written (locate file.module_.package) (Of_file (Ids.of_file file))));
    list_package_declarations =
      (fun package ->
        note Package_declarations (Ids.of_package package) "";
        list_sorted (locate package) (Of_package (Path.show_package package)));
    read_definition = (fun key -> Marshal.from_string (read_column Tree key Store.find_tree) 0);
    read_text = (fun key -> read_column Text key Store.find_text);
    read_spans = (fun key -> Marshal.from_string (read_column Tree key Store.find_spans) 0);
    list_syntax_errors =
      (fun key -> Marshal.from_string (read_column Tree key Store.find_syntax_errors) 0);
    read_place =
      (fun key ->
        let file, base = read_column Place key Store.find_place in
        { file = decode_file file; base });
    find_container =
      (fun key ->
        look_up Container key (fun schema id ->
            Option.bind (require key (Store.find_placement store schema ~id)).container
              (fun container ->
                Option.map decode_key (Store.find_definition_key store schema ~id:container))));
    list_contained =
      (fun key ->
        look_up Contained key (fun schema id ->
            List.map
              (fun ((_, declaration) : _ * Resolve.Names.declaration) -> declaration.key)
              (list_written schema (Of_container id))));
    list_members;
    list_traits_declaring =
      (fun package name ->
        note Traits_declaring (Ids.of_package package) name;
        let traits =
          List.sort
            (fun (_, left) (_, right) -> compare left right)
            (List.map
               (fun (trait, file, position) ->
                 ((decode_key trait).path, (decode_file file, position)))
               (Store.list_containers_of_member store (locate package)
                  ~package:(Path.show_package package) ~member:name
                  ~container_kind:(rank kinds Trait)))
        in
        List.fold_left
          (fun distinct (trait, _) ->
            if List.exists (Path.equal trait) distinct then distinct else distinct @ [ trait ])
          [] traits);
    list_impls =
      (fun package ->
        note Impl_index (Ids.of_package package) "";
        list_impl_entries package Impls_of_package);
    list_impls_of_type =
      (fun package type_ ->
        let id = Ids.of_path type_ in
        note Impls_of_type id (Path.show_package package);
        List.map
          (fun ((trait, _), impl) -> (trait, impl))
          (list_impl_entries package (Impls_of_type id)));
    list_impls_of_trait =
      (fun package trait ->
        note Impls_of_trait (Ids.of_path trait) (Path.show_package package);
        List.map snd (list_impl_entries package (Impls_of_trait (Ids.of_path trait))));
    list_law_proofs =
      (fun package (name : Resolve.Names.law_proof_name) ->
        note Law_proofs (Ids.of_path name.trait)
          (name_law_proofs ~package:(Path.show_package package) ~law:name.law
             ~type_:(Ids.of_path name.type_head));
        List.filter_map
          (fun definition ->
            Option.map decode_key (Store.find_definition_key store (locate package) ~id:definition))
          (Store.list_law_proofs store (locate package) ~package:(Path.show_package package)
             ~trait:(Ids.of_path name.trait) ~law:name.law ~type_:(Ids.of_path name.type_head)));
  }

type change = { lookup : Kind.lookup; scope : int; name : string; is_spans_only : bool }

let list_replaced_lookups store ~before ~after : (Kind.lookup * int * string) list =
  let schemas = Option.to_list before @ Option.to_list after in
  let list_differing table columns map =
    List.concat_map map (Store.list_differing_rows store ~table ~columns ~before ~after)
  in
  let fail table =
    Compiler_bug.raise_bug ~stage:"Database" "a row of %s holds a column of another type" table
  in
  let read_optional table : Store.cell -> int option = function
    | Integer value -> Some value
    | Null -> None
    | Blob _ | Text _ -> fail table
  in
  list_differing "module" [ "id" ] (function
    | [| Integer id |] -> [ (Kind.Module, id, "") ]
    | _ -> fail "module")
  @ list_differing "file" [ "id"; "module" ] (function
    | [| Integer id; Integer module_ |] -> [ (Kind.Source, id, ""); (Files, module_, "") ]
    | _ -> fail "file")
  @ list_differing "entry" [ "module"; "name" ] (function
    | [| Integer module_; Text name |] -> [ (Kind.Entry, module_, name); (Entries, module_, "") ]
    | _ -> fail "entry")
  @ list_differing "definition"
      [ "id"; "package"; "module"; "kind"; "owner"; "member"; "container"; "file" ] (function
      | [|
          Integer id; Text package; Integer module_; Integer kind; owner; member; container; file;
        |] ->
          let package = Store.identify package in
          let name_members container_id =
            List.concat_map
              (fun schema ->
                List.filter_map
                  (fun (row : Store.definition) -> row.member)
                  (Store.list_definitions store schema (Of_container container_id)))
              schemas
          in
          List.map
            (fun (lookup : Kind.lookup) -> (lookup, id, ""))
            [ Declaration; Tree; Text; Place; Imports; Container ]
          @ [ (Kind.Module_declarations, module_, ""); (Package_declarations, package, "") ]
          @ List.map
              (fun container -> (Kind.Contained, container, ""))
              (Option.to_list (read_optional "definition" container))
          @ List.map
              (fun file -> (Kind.File_declarations, file, ""))
              (Option.to_list (read_optional "definition" file))
          @ (match (read_optional "definition" owner, member) with
            | Some owner, Text member ->
                [ (Kind.Members, owner, member); (Traits_declaring, package, member) ]
            | _ -> [])
          @
          if kind = rank kinds Trait then
            List.map (fun member -> (Kind.Traits_declaring, package, member)) (name_members id)
          else []
      | _ -> fail "definition")
  @ list_differing "syntax" [ "definition" ] (function
    | [| Integer definition |] -> [ (Kind.Tree, definition, "") ]
    | _ -> fail "syntax")
  @ list_differing "import" [ "file" ] (function
    | [| Integer file |] ->
        List.concat_map
          (fun schema ->
            List.map
              (fun (row : Store.definition) -> (Kind.Imports, row.id, ""))
              (Store.list_definitions store schema (Of_file file)))
          schemas
    | _ -> fail "import")
  @ list_differing "impl" [ "package"; "trait"; "type" ] (function
    | [| Text package; Integer trait; Integer type_ |] ->
        [
          (Kind.Impl_index, Store.identify package, "");
          (Impls_of_type, type_, package);
          (Impls_of_trait, trait, package);
        ]
    | _ -> fail "impl")
  @ list_differing "law_proof" [ "package"; "trait"; "law"; "type" ] (function
    | [| Text package; Integer trait; Text law; Integer type_ |] ->
        [ (Kind.Law_proofs, trait, name_law_proofs ~package ~law ~type_) ]
    | _ -> fail "law_proof")
  @ list_differing "dependency" [ "package" ] (function
    | [| Text package |] -> [ (Kind.Dependencies, Store.identify package, "") ]
    | _ -> fail "dependency")

type written = {
  changes : change list;
  added : Store.definition list;
  removed : Store.definition list;
}

let marshal value = Marshal.to_string value []

let is_equal_marshaled before after =
  String.equal before after
  || compare (Marshal.from_string before 0 : Obj.t) (Marshal.from_string after 0 : Obj.t) = 0

let encode_definition ~text (declared : Resolve.Namespace.declared_definition) :
    Store.definition * Store.syntax =
  let key = declared.declaration.key in
  let owner, member =
    match key.path with
    | Method { owner; name; _ } | Member_constant { owner; name } ->
        (Some (Ids.of_path owner), Some name)
    | Top _ | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _ -> (None, None)
  in
  let item = declared.item in
  ( {
      id = Ids.of_key key;
      key = Ids.encode key;
      package = Path.show_package key.module_.package;
      module_ = Ids.of_module key.module_;
      path = Ids.of_path key.path;
      ordinal = key.ordinal;
      name = Path.show key.path;
      owner;
      member;
      kind = rank kinds declared.declaration.kind;
      visibility = rank visibilities declared.declaration.visibility;
      is_generic = declared.declaration.generic;
      origin = written_origin;
      supplied_from = None;
      container = Option.map Ids.of_key declared.container;
      file = Some (Ids.of_file declared.file);
      position = Some declared.position;
      base = Some item.base;
      stop = Some item.stop;
      text_hash = Some (Store.identify (String.sub text item.base (item.stop - item.base)));
    },
    {
      tree = marshal item.value;
      spans = marshal item.positions.spans;
      syntax_errors = marshal item.positions.syntax_errors;
    } )

let encode_supplied ~origin ~(kind : Resolve.Names.kind) (key : Resolve.Names.key) ~supplied_from
    ~container : Store.definition =
  let owner, member =
    match key.path with
    | Method { owner; name; _ } | Member_constant { owner; name } ->
        (Some (Ids.of_path owner), Some name)
    | Top _ | Impl _ | Derived _ | Test _ | Law_proof _ | Unresolved _ -> (None, None)
  in
  {
    id = Ids.of_key key;
    key = Ids.encode key;
    package = Path.show_package key.module_.package;
    module_ = Ids.of_module key.module_;
    path = Ids.of_path key.path;
    ordinal = key.ordinal;
    name = Path.show key.path;
    owner;
    member;
    kind = rank kinds kind;
    visibility = rank visibilities Private;
    is_generic = false;
    origin;
    supplied_from = Some supplied_from;
    container;
    file = None;
    position = None;
    base = None;
    stop = None;
    text_hash = None;
  }

let count_syntax_errors bytes =
  List.length (Marshal.from_string bytes 0 : Source.Definition_span.t list)

let write_module store (module_ : Path.module_) ~(files : (Path.file * string) list)
    (declarations : Resolve.Namespace.module_declarations) =
  let package = module_.package in
  let package_name = Path.show_package package and module_id = Ids.of_module module_ in
  let lookups =
    make_lookups store
      ~note:(fun _ _ _ -> ())
      ~is_package:(fun _ -> false)
      ~list_dependency_names:(fun _ -> [])
  in
  let rows =
    List.map
      (fun (declared : Resolve.Namespace.declared_definition) ->
        encode_definition ~text:(List.assoc declared.file files) declared)
      declarations.definitions
  in
  let rows_before =
    List.filter
      (fun (row : Store.definition) -> row.origin = written_origin)
      (Store.list_definitions store Main (Of_module module_id))
  in
  let index identify rows =
    let by_id = Hashtbl.create 64 in
    List.iter (fun row -> Hashtbl.replace by_id (identify row) row) rows;
    Hashtbl.find_opt by_id
  in
  let find_before = index (fun (row : Store.definition) -> row.id) rows_before in
  let find_after = index (fun ((row : Store.definition), _) -> row.id) rows in
  let changes = ref [] in
  let add ?(is_spans_only = false) (lookup : Kind.lookup) scope name =
    changes := { lookup; scope; name; is_spans_only } :: !changes
  in
  let candidates = ref [] in
  let consider (lookup : Kind.lookup) scope name read =
    candidates := (lookup, scope, name, read) :: !candidates
  in
  let consider_lists (row : Store.definition) =
    let key = decode_key row.key in
    consider Module_declarations module_id "" (fun () ->
        Obj.repr (lookups.list_declarations module_));
    consider Package_declarations (Ids.of_package package) "" (fun () ->
        Obj.repr (lookups.list_package_declarations package));
    Option.iter
      (fun container ->
        consider Contained container "" (fun () ->
            Obj.repr
              (List.map
                 (fun (row : Store.definition) -> row.key)
                 (Store.list_definitions store Main (Of_container container)))))
      row.container;
    match (key.path, row.member) with
    | (Method { owner; name; _ } | Member_constant { owner; name }), Some member ->
        consider Members (Ids.of_path owner) name (fun () ->
            Obj.repr (lookups.list_members owner name));
        consider Traits_declaring (Ids.of_package package) member (fun () ->
            Obj.repr (lookups.list_traits_declaring package member))
    | _ -> ()
  in
  List.iter
    (fun ((file : Path.file), _) ->
      consider File_declarations (Ids.of_file file) "" (fun () ->
          Obj.repr (lookups.list_declarations_in file)))
    files;
  List.iter
    (fun (row : Store.definition) -> if Option.is_none (find_after row.id) then consider_lists row)
    rows_before;
  List.iter
    (fun ((row : Store.definition), _) ->
      match find_before row.id with
      | None -> consider_lists row
      | Some before ->
          if
            (before.kind, before.visibility, before.is_generic, before.container, before.position)
            <> (row.kind, row.visibility, row.is_generic, row.container, row.position)
          then begin
            consider_lists before;
            consider_lists row
          end)
    rows;
  let candidates =
    List.sort_uniq (fun (l, s, n, _) (l', s', n', _) -> compare (l, s, n) (l', s', n')) !candidates
  in
  let results_before = List.map (fun (_, _, _, read) -> read ()) candidates in
  let imports_before =
    List.map
      (fun ((file : Path.file), _) -> Store.list_imports store Main ~file:(Ids.of_file file))
      files
  in
  let add_all_of (row : Store.definition) =
    List.iter
      (fun (lookup : Kind.lookup) -> add lookup row.id "")
      [ Declaration; Tree; Text; Place; Imports; Container ]
  in
  List.iter
    (fun (row : Store.definition) ->
      if Option.is_none (find_after row.id) then begin
        add_all_of row;
        Store.remove_definition store ~id:row.id
      end)
    rows_before;
  List.iter
    (fun ((row : Store.definition), (syntax : Store.syntax)) ->
      match (find_before row.id, Store.find_syntax store Main ~definition:row.id) with
      | Some before, Some syntax_before ->
          if
            (before.kind, before.visibility, before.is_generic)
            <> (row.kind, row.visibility, row.is_generic)
          then add Declaration row.id "";
          if before.text_hash <> row.text_hash then add Text row.id "";
          if (before.file, before.base) <> (row.file, row.base) then add Place row.id "";
          if before.container <> row.container then add Container row.id "";
          if before <> row then Store.replace_definition store row;
          let is_tree_changed =
            (not (is_equal_marshaled syntax_before.tree syntax.tree))
            || count_syntax_errors syntax_before.syntax_errors
               <> count_syntax_errors syntax.syntax_errors
          in
          let is_spans_changed =
            (not (is_equal_marshaled syntax_before.spans syntax.spans))
            || not (is_equal_marshaled syntax_before.syntax_errors syntax.syntax_errors)
          in
          if is_tree_changed then add Tree row.id ""
          else if is_spans_changed then add ~is_spans_only:true Tree row.id "";
          if is_tree_changed || is_spans_changed then
            Store.replace_syntax store ~definition:row.id syntax
      | _ ->
          add_all_of row;
          Store.replace_definition store row;
          Store.replace_syntax store ~definition:row.id syntax)
    rows;
  List.iter2
    (fun ((file : Path.file), _) before ->
      let after =
        List.map
          (fun (name, imported) -> (name, Ids.encode (imported : Path.module_)))
          (Option.value ~default:[] (List.assoc_opt file declarations.imports))
      in
      if before <> after then begin
        Store.replace_imports store ~file:(Ids.of_file file) after;
        List.iter
          (fun (row : Store.definition) ->
            if row.file = Some (Ids.of_file file) then add Imports row.id "")
          (rows_before @ List.map fst rows)
      end)
    files imports_before;
  let identify_impl (impl : Store.impl) =
    (impl.definition, impl.position, impl.trait, impl.type_)
  in
  let impls_before =
    List.map identify_impl
      (Store.list_impls store Main ~package:package_name (Impls_of_module module_id))
  in
  let impls =
    List.mapi
      (fun position (((trait, type_), impl) as entry) : Store.impl ->
        {
          definition = Ids.of_path impl;
          module_ = module_id;
          position;
          trait = Ids.of_path trait;
          type_ = Ids.of_path type_;
          entry = marshal { declared_in = module_; entry };
        })
      declarations.impls
  in
  let impls_after = List.map identify_impl impls in
  if List.sort compare impls_before <> List.sort compare impls_after then begin
    Store.replace_module_impls store ~package:package_name ~module_:module_id impls;
    add Impl_index (Ids.of_package package) "";
    let list_differing select =
      let has_impl impls impl = List.exists (fun candidate -> candidate = impl) impls in
      List.sort_uniq Int.compare
        (List.filter_map
           (fun impl ->
             if has_impl impls_before impl && has_impl impls_after impl then None
             else Some (select impl))
           (impls_before @ impls_after))
    in
    List.iter
      (fun type_ -> add Impls_of_type type_ package_name)
      (list_differing (fun (_, _, _, type_) -> type_));
    List.iter
      (fun trait -> add Impls_of_trait trait package_name)
      (list_differing (fun (_, _, trait, _) -> trait))
  end;
  List.iter
    (fun (row : Store.law_proof) ->
      add Law_proofs row.trait (name_law_proofs ~package:package_name ~law:row.law ~type_:row.type_))
    (Store.replace_module_law_proofs store ~package:package_name ~module_:module_id
       (List.map
          (fun ((name : Resolve.Names.law_proof_name), key) : Store.law_proof ->
            {
              definition = Ids.of_key key;
              module_ = module_id;
              trait = Ids.of_path name.trait;
              law = name.law;
              type_ = Ids.of_path name.type_head;
            })
          declarations.law_proofs));
  List.iter2
    (fun (lookup, scope, name, read) before ->
      if compare before (read ()) <> 0 then add lookup scope name)
    candidates results_before;
  let supplied =
    List.filter_map
      (fun ((_, type_), impl) ->
        match impl with
        | Path.Derived _ ->
            Some
              (encode_supplied ~origin:derived_impl_origin ~kind:Impl
                 { module_; path = impl; ordinal = 0 }
                 ~supplied_from:(Ids.of_key { module_; path = type_; ordinal = 0 })
                 ~container:None)
        | _ -> None)
      declarations.impls
  in
  let supplied_before =
    List.filter
      (fun (row : Store.definition) -> row.origin = derived_impl_origin)
      (Store.list_definitions store Main (Of_module module_id))
  in
  let has_row rows (row : Store.definition) =
    List.exists (fun (candidate : Store.definition) -> candidate.id = row.id) rows
  in
  List.iter
    (fun (row : Store.definition) ->
      if not (has_row supplied row) then Store.remove_definition store ~id:row.id)
    supplied_before;
  List.iter
    (fun (row : Store.definition) ->
      if not (List.mem row supplied_before) then Store.replace_definition store row)
    supplied;
  let is_same_kind (before : Store.definition option) (row : Store.definition) =
    match before with Some before -> before.kind = row.kind | None -> false
  in
  {
    changes = !changes;
    added =
      List.filter_map
        (fun ((row : Store.definition), _) ->
          if is_same_kind (find_before row.id) row then None else Some row)
        rows
      @ List.filter (fun row -> not (has_row supplied_before row)) supplied;
    removed =
      List.filter
        (fun (row : Store.definition) ->
          not (is_same_kind (Option.map fst (find_after row.id)) row))
        rows_before
      @ List.filter (fun row -> not (has_row supplied row)) supplied_before;
  }
