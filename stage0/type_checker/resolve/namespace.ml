module Path_table = Hashtbl.Make (Path)

module File_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.file
end))

module Item_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.file * int
end))

module String_map = Map.Make (String)

let convert_visibility : Syntax.visibility option -> Names.visibility = function
  | None -> Private
  | Some Internal -> Internal
  | Some Public -> Public
  | Some Public_opaque -> Public_opaque

type impl_index = {
  impls : ((Path.t * Path.t) * Path.t) list;
  by_type : (Path.t * Path.t) list Path.Map.t;
  by_trait : Path.t list Path.Map.t;
}

let convert_intended : Syntax.intended_kind -> Names.named = function
  | Intended_function -> Function
  | Intended_constant -> Constant
  | Intended_type -> Type
  | Intended_trait -> Trait
  | Intended_capability -> Capability
  | Intended_theorem -> Theorem

let find_entry (definition : Syntax.definition) =
  let make_entry (name : Syntax.name) kind generic : Names.entry option =
    Some { name = name.text; kind; visibility = convert_visibility definition.visibility; generic }
  in
  match definition.kind with
  | Function { signature = { name = Plain_name name; generics; _ }; _ } ->
      make_entry name Function (generics <> [])
  | Type_definition { name; generics; _ } -> make_entry name Type (generics <> [])
  | Trait { name; generics; _ } -> make_entry name Trait (generics <> [])
  | Capability { name; _ } -> make_entry name Capability false
  | Constant { name = Plain_name name; _ } -> make_entry name Constant false
  | Theorem { name; generics; _ } -> make_entry name Theorem (generics <> [])
  | Definition_error { name = Some (Plain_name name); intended = Some intended } ->
      make_entry name (convert_intended intended) false
  | Function _ | Method_declaration _ | Constant _ | Impl _ | Test _ | Law_proof _
  | Definition_error _ ->
      None

let list_file_entries (top_levels : Syntax.top_level list) =
  List.filter_map
    (fun (top_level : Syntax.top_level) -> find_entry top_level.definition.value)
    top_levels

let builtin_entries =
  List.map
    (fun builtin : Names.entry ->
      {
        name = Language.Builtin_type.show builtin;
        kind = Type;
        visibility = Public;
        generic = Names.list_builtin_generics builtin <> [];
      })
    Language.Builtin_type.all
  @ List.map
      (fun operation : Names.entry ->
        {
          name = Intrinsic.show_operation operation;
          kind = Function;
          visibility = Public;
          generic = true;
        })
      Intrinsic.operations

let find_head_type (lookups : Names.lookups) ~(from : Path.module_) ~imports (path : Syntax.path) =
  match path.modules with
  | [] -> Names.Scope.find_bare_type lookups ~from path.last.text
  | first :: rest -> (
      match
        Names.Scope.lookup_module lookups ~from ~imports first.text
          (List.map (fun (name : Syntax.name) -> name.text) rest)
      with
      | Found_module module_ -> (
          match
            Names.Scope.lookup_in lookups ~from module_ path.last.text
              ~is_kind:Names.Scope.is_type_kind
          with
          | Visible (item, path) -> Some (item, path)
          | Hidden _ | Absent -> None)
      | Restricted_module | Ambiguous_module _ | No_module _ | No_package _ -> None)

let make_unresolved_path (file : Path.file) names : Path.t = Unresolved { file; names }

let resolve_type_path (lookups : Names.lookups) ~(file : Path.file) ~imports (path : Syntax.path) :
    Path.t =
  match find_head_type lookups ~from:file.module_ ~imports path with
  | Some (_, resolved) -> resolved
  | None ->
      make_unresolved_path file
        (List.map (fun (name : Syntax.name) -> name.text) (path.modules @ [ path.last ]))

let list_head_parameters (head : Syntax.type_head) =
  List.filter_map
    (fun (generic : Syntax.generic_parameter) ->
      match generic.kind with
      | Type_parameter (name, _) | Value_parameter (name, _) -> Some name.text
      | Generic_error -> None)
    head.generics

let resolve_count (lookups : Names.lookups) ~(file : Path.file) ~parameters (name : Syntax.name) :
    Path.argument =
  if List.mem name.text parameters then Parameter name.text
  else
    match lookups.find file.module_ name.text with
    | Some { kind = Constant; _ } -> Constant (Names.Scope.make_top_path file.module_ name.text)
    | _ -> Constant (make_unresolved_path file [ name.text ])

let rec resolve_reference (lookups : Names.lookups) ~file ~imports ~spell ~parameters ~self
    (written : Syntax.path_type) : Path.reference =
  let resolve_local_argument = resolve_argument lookups ~file ~imports ~spell ~parameters ~self in
  {
    path = resolve_type_path lookups ~file ~imports written.path;
    arguments =
      List.filter_map
        (function
          | Syntax.Type_argument type_ -> Some (resolve_local_argument type_)
          | Count (value, _) -> Some (Path.Count value)
          | Count_name name -> Some (resolve_count lookups ~file ~parameters name)
          | Constraint _ -> None)
        written.arguments;
    associated =
      List.sort compare
        (List.filter_map
           (function
             | Syntax.Constraint (name, type_) -> Some (name.text, resolve_local_argument type_)
             | Type_argument _ | Count _ | Count_name _ -> None)
           written.arguments);
  }

and resolve_argument (lookups : Names.lookups) ~file ~imports ~spell ~parameters ~self
    (type_ : Syntax.type_expression) : Path.argument =
  match type_.kind with
  | Path_type { path = { modules = []; last }; arguments = []; _ }
    when List.mem last.text parameters ->
      Parameter last.text
  | Path_type written ->
      Named (resolve_reference lookups ~file ~imports ~spell ~parameters ~self written)
  | Any_type written ->
      Any (resolve_reference lookups ~file ~imports ~spell ~parameters ~self written)
  | Self_type None ->
      Named
        {
          path = self;
          arguments = List.map (fun name -> Path.Parameter name) parameters;
          associated = [];
        }
  | Self_type (Some _) | Associated _ | Function_type _ | Type_error ->
      Named { path = make_unresolved_path file [ spell type_.id ]; arguments = []; associated = [] }

let resolve_header (lookups : Names.lookups) ~file ~imports ~spell (trait_ : Syntax.path_type)
    (head : Syntax.type_head) =
  let for_type = resolve_type_path lookups ~file ~imports head.path in
  ( resolve_reference lookups ~file ~imports ~spell ~parameters:(list_head_parameters head)
      ~self:for_type trait_,
    for_type )

let restrict_visibility (left : Names.visibility) (right : Names.visibility) : Names.visibility =
  match (left, right) with
  | Private, _ | _, Private -> Private
  | Internal, _ | _, Internal -> Internal
  | (Public | Public_opaque), (Public | Public_opaque) -> Public

let rec list_reference_paths (reference : Path.reference) =
  reference.path :: List.concat_map list_argument_paths reference.arguments

and list_argument_paths : Path.argument -> Path.t list = function
  | Named reference | Any reference -> list_reference_paths reference
  | Constant path -> [ path ]
  | Parameter _ | Count _ -> []

let derive_header_visibility (lookups : Names.lookups) (trait : Path.reference) for_type =
  List.fold_left
    (fun visibility (path : Path.t) ->
      match path with
      | Top { module_; name } -> (
          match lookups.find module_ name with
          | Some entry -> restrict_visibility visibility entry.visibility
          | None -> visibility)
      | _ -> visibility)
    Public
    (for_type :: list_reference_paths trait)

type written = {
  declaration : Names.declaration;
  file : Path.file;
  index : int;
  container : int option;
  item : Syntax.definition Syntax.item;
  text : string;
}

let list_file_declarations (lookups : Names.lookups) (file : Path.file) ~imports ~text
    (top_levels : Syntax.top_level list) =
  let module_ = file.module_ in
  let resolve_owner (head : Syntax.type_head) =
    resolve_type_path lookups ~file ~imports head.path
  in
  let resolve_local_header (item : Syntax.definition Syntax.item) =
    let spell id =
      let span : Source.Definition_span.t = item.positions.spans.(id) in
      String.sub text (item.base + span.start) (span.stop - span.start)
    in
    resolve_header lookups ~file ~imports ~spell
  in
  let make_written index ?container ~visibility (item : Syntax.definition Syntax.item) path kind
      generic =
    Some
      {
        declaration = { key = { module_; path; ordinal = 0 }; kind; visibility; generic };
        file;
        index;
        container;
        item;
        text = String.sub text item.base (item.stop - item.base);
      }
  in
  let declare_method index ~container ~(owner : Names.declaration) ~is_capability
      (item : Syntax.definition Syntax.item) =
    let declare = make_written index ~container ~visibility:owner.visibility item in
    let owner = owner.key.path in
    match item.value.kind with
    | Function { signature; _ } | Method_declaration signature ->
        let name = (Names.extract_signature_name signature).text in
        declare
          (if is_capability then Path.make_capability_method owner name
           else Method { owner; name; receiver = Names.classify_receiver signature.parameters })
          Method (signature.generics <> [])
    | Definition_error { name = Some (Plain_name name | Member_name (_, name)); _ } ->
        declare (Method { owner; name = name.text; receiver = Static }) Method false
    | _ -> None
  in
  let declare_top_level index (item : Syntax.definition Syntax.item) =
    let declare = make_written index ~visibility:(convert_visibility item.value.visibility) item in
    match item.value.kind with
    | Function { signature = { name = Member_name (head, name); generics; parameters; _ }; _ } ->
        declare
          (Method
             {
               owner = resolve_owner head;
               name = name.text;
               receiver = Names.classify_receiver parameters;
             })
          Method (generics <> [])
    | Constant { name = Member_name (head, name); _ } ->
        declare
          (Member_constant { owner = resolve_owner head; name = name.text })
          Member_constant false
    | Impl { trait_; type_; _ } ->
        let trait, for_type = resolve_local_header item trait_ type_ in
        make_written index
          ~visibility:(derive_header_visibility lookups trait for_type)
          item
          (Impl { module_; trait; for_type })
          Impl (type_.generics <> [])
    | Test { name; _ } ->
        let text =
          name.first.value
          ^ String.concat "" (List.map (fun (_, (text : Syntax.text)) -> text.value) name.rest)
        in
        declare (Test { module_; name = text }) Test false
    | Law_proof { trait_; law; type_; _ } ->
        let trait, for_type = resolve_local_header item trait_ type_ in
        make_written index
          ~visibility:(derive_header_visibility lookups trait for_type)
          item
          (Law_proof { module_; trait; law = law.text; for_type })
          Law_proof false
    | Definition_error { name = Some (Member_name (head, name)); intended } ->
        let owner = resolve_owner head in
        if intended = Some Intended_constant then
          declare (Member_constant { owner; name = name.text }) Member_constant false
        else declare (Method { owner; name = name.text; receiver = Static }) Method false
    | Function _ | Type_definition _ | Trait _ | Capability _ | Constant _ | Theorem _
    | Method_declaration _ | Definition_error _ ->
        Option.bind (find_entry item.value) (fun (entry : Names.entry) ->
            make_written index ~visibility:entry.visibility item
              (Names.Scope.make_top_path module_ entry.name)
              (Names.convert_named entry.kind) entry.generic)
  in
  let _, declared =
    List.fold_left
      (fun (index, declared) (top_level : Syntax.top_level) ->
        let container = declare_top_level index top_level.definition in
        let owner =
          match (top_level.definition.value.kind, container) with
          | (Trait _ | Impl _), Some container -> Some (container.declaration, false)
          | Capability _, Some container -> Some (container.declaration, true)
          | _ -> None
        in
        let methods =
          match owner with
          | Some (owner, is_capability) ->
              List.mapi
                (fun offset method_item ->
                  declare_method
                    (index + 1 + offset)
                    ~container:index ~owner ~is_capability method_item)
                top_level.methods
          | None -> []
        in
        (index + 1 + List.length top_level.methods, List.rev_append methods (container :: declared)))
      (0, []) top_levels
  in
  List.filter_map Fun.id (List.rev declared)

module Module_map = Map.Make (struct
  type t = Path.module_

  let compare = compare
end)

module File_map = Map.Make (struct
  type t = Path.file

  let compare = compare
end)

let compare_key (left : Names.key) (right : Names.key) =
  match compare left.module_ right.module_ with
  | 0 -> (
      match Path.compare left.path right.path with
      | 0 -> Int.compare left.ordinal right.ordinal
      | order -> order)
  | order -> order

module Key_map = Map.Make (struct
  type t = Names.key

  let compare = compare_key
end)

module Member_map = Map.Make (struct
  type t = Path.t * string

  let compare (left_owner, left_name) (right_owner, right_name) =
    match Path.compare left_owner right_owner with
    | 0 -> String.compare left_name right_name
    | order -> order
end)

module Law_proof_map = Map.Make (struct
  type t = Names.law_proof_name

  let compare (left : Names.law_proof_name) (right : Names.law_proof_name) =
    match Path.compare left.trait right.trait with
    | 0 -> (
        match String.compare left.law right.law with
        | 0 -> Path.compare left.type_head right.type_head
        | order -> order)
    | order -> order
end)

type declared = {
  declaration : Names.declaration;
  item : Syntax.definition Syntax.item;
  text : string;
  place : Names.place;
  imports : (string * Path.module_) list;
  container : Names.key option;
  contained : Names.key list;
}

type module_names = {
  entries : Names.entry list;
  entries_by_name : Names.entry String_map.t;
  module_declarations : Names.declaration list;
}

type t = {
  modules : module_names Module_map.t;
  files : Names.declaration list File_map.t;
  declarations : Names.declaration list;
  declared : declared Key_map.t;
  members : Names.key list Member_map.t;
  traits : Path.t list String_map.t;
  impls : impl_index;
  law_proofs : Names.key list Law_proof_map.t;
}

let make_module_names entries =
  {
    entries;
    entries_by_name =
      List.fold_left
        (fun by_name (entry : Names.entry) ->
          if String_map.mem entry.name by_name then by_name
          else String_map.add entry.name entry by_name)
        String_map.empty entries;
    module_declarations = [];
  }

let number_written (written : written list) =
  let counts = Path_table.create 16 in
  List.map
    (fun (written : written) ->
      let path = written.declaration.key.path in
      let ordinal = Option.value ~default:0 (Path_table.find_opt counts path) in
      Path_table.replace counts path (ordinal + 1);
      {
        written with
        declaration = { written.declaration with key = { written.declaration.key with ordinal } };
      })
    written

let is_head_kind (lookups : Names.lookups) (path : Path.t) ~(kinds : Names.named list) =
  match Names.find_kind lookups path with
  | Some kind when List.mem kind kinds -> (
      match Well_known.find_builtin_type path with Some (Never | Integer) -> false | _ -> true)
  | _ -> false

let resolve_head (lookups : Names.lookups) ~from ~imports (path : Syntax.path) ~kinds =
  match find_head_type lookups ~from ~imports path with
  | Some (_, path) when is_head_kind lookups path ~kinds -> Some path
  | _ -> None

let list_impl_entries (lookups : Names.lookups) ~imports (declaration : Names.declaration)
    (definition : Syntax.definition) =
  match (declaration.key.path, definition.kind) with
  | Impl { trait = { path = trait; _ }; for_type; _ }, _ ->
      if
        is_head_kind lookups trait ~kinds:[ Trait; Capability ]
        && is_head_kind lookups for_type ~kinds:[ Type ]
      then [ ((trait, for_type), declaration.key.path) ]
      else []
  | _, Type_definition { clauses; _ } ->
      let resolve_local_head = resolve_head lookups ~from:declaration.key.module_ ~imports in
      List.concat_map
        (fun (clause : Syntax.type_clause) ->
          match clause.kind with
          | Derives traits ->
              List.filter_map
                (fun (trait : Syntax.path_type) ->
                  match resolve_local_head trait.path ~kinds:[ Trait ] with
                  | Some trait when Names.is_derivable trait ->
                      Some
                        ( (trait, declaration.key.path),
                          (Derived { type_ = declaration.key.path; trait } : Path.t) )
                  | _ -> None)
                traits
          | Type_invariant _ | Potential _ -> [])
        clauses
  | _ -> []

let find_law_proof_entry (lookups : Names.lookups) (declaration : Names.declaration) =
  match declaration.key.path with
  | Law_proof { trait = { path = trait; _ }; law; for_type; _ }
    when is_head_kind lookups trait ~kinds:[ Trait ]
         && is_head_kind lookups for_type ~kinds:[ Type ] ->
      Some ({ trait; law; type_head = for_type } : Names.law_proof_name)
  | _ -> None

let build (lookups : Names.lookups) package
    (modules : (Path.module_ * (Path.file * Syntax.file * string) list) list) =
  let modules_map =
    List.fold_left
      (fun map (module_, files) ->
        Module_map.add module_
          (make_module_names
             (List.concat_map
                (fun (_, (file : Syntax.file), _) -> list_file_entries file.definitions)
                files))
          map)
      (if Well_known.intrinsic_module.package = package then
         Module_map.singleton Well_known.intrinsic_module (make_module_names builtin_entries)
       else Module_map.empty)
      modules
  in
  let find_pass_name (module_ : Path.module_) name =
    if module_.package = package then
      Option.bind (Module_map.find_opt module_ modules_map) (fun names ->
          String_map.find_opt name names.entries_by_name)
    else lookups.find module_ name
  in
  let pass_module_exists (module_ : Path.module_) =
    if module_.package = package then Module_map.mem module_ modules_map
    else lookups.module_exists module_
  in
  let list_imports (file : Path.file) (uses : Syntax.path Syntax.item list) =
    List.map
      (fun (item : Syntax.path Syntax.item) ->
        let used = Names.resolve_used_module lookups ~from:file.module_ item.value in
        (Names.Scope.extract_last_name used, used))
      uses
  in
  let imports =
    List.fold_left
      (fun map (_, files) ->
        List.fold_left
          (fun map ((file : Path.file), (parsed : Syntax.file), _) ->
            File_map.add file (list_imports file parsed.uses) map)
          map files)
      File_map.empty modules
  in
  let list_file_imports file = Option.value ~default:[] (File_map.find_opt file imports) in
  let pass_lookups = { lookups with find = find_pass_name; module_exists = pass_module_exists } in
  let module_declarations =
    List.map
      (fun (module_, files) ->
        ( module_,
          number_written
            (List.concat_map
               (fun ((file : Path.file), (parsed : Syntax.file), text) ->
                 list_file_declarations pass_lookups file ~imports:(list_file_imports file) ~text
                   parsed.definitions)
               files) ))
      modules
  in
  let written = List.concat_map snd module_declarations in
  let sort_declarations declarations =
    List.sort
      (fun (left : Names.declaration) (right : Names.declaration) -> compare_key left.key right.key)
      (List.map (fun (written : written) -> written.declaration) declarations)
  in
  let declarations = sort_declarations written in
  let by_file = File_table.create 16 in
  List.iter
    (fun (written : written) ->
      File_table.replace by_file written.file
        (written :: Option.value ~default:[] (File_table.find_opt by_file written.file)))
    written;
  let list_in_file file = List.rev (Option.value ~default:[] (File_table.find_opt by_file file)) in
  let key_of_written (written : written) = written.declaration.key in
  let at_index = Item_table.create 64 and in_container = Item_table.create 64 in
  List.iter
    (fun (written : written) ->
      Item_table.replace at_index (written.file, written.index) written;
      Option.iter
        (fun container -> Item_table.add in_container (written.file, container) written)
        written.container)
    written;
  let declared =
    List.fold_left
      (fun map (written : written) ->
        Key_map.add (key_of_written written)
          {
            declaration = written.declaration;
            item = written.item;
            text = written.text;
            place = { file = written.file; base = written.item.base };
            imports = list_file_imports written.file;
            container =
              Option.map key_of_written
                (Option.bind written.container (fun index ->
                     Item_table.find_opt at_index (written.file, index)));
            contained =
              List.rev_map key_of_written
                (Item_table.find_all in_container (written.file, written.index));
          }
          map)
      Key_map.empty written
  in
  let members =
    Member_map.map List.rev
      (List.fold_left
         (fun index (declaration : Names.declaration) ->
           match declaration.key.path with
           | (Method { owner; name; _ } | Member_constant { owner; name })
             when declaration.key.ordinal = 0 ->
               Member_map.update (owner, name)
                 (fun keys -> Some (declaration.key :: Option.value ~default:[] keys))
                 index
           | _ -> index)
         Member_map.empty declarations)
  in
  let traits =
    let trait_at =
      List.filter_map
        (fun (written : written) ->
          if written.declaration.kind = Trait && written.declaration.key.ordinal = 0 then
            Some ((written.file, written.index), written.declaration.key.path)
          else None)
        written
    in
    List.fold_left
      (fun index (written : written) ->
        match (written.declaration.key.path, written.container) with
        | Method { name; _ }, Some container -> (
            match List.assoc_opt (written.file, container) trait_at with
            | Some trait ->
                String_map.update name
                  (fun traits ->
                    let traits = Option.value ~default:[] traits in
                    Some
                      (if List.exists (Path.equal trait) traits then traits else traits @ [ trait ]))
                  index
            | None -> index)
        | _ -> index)
      String_map.empty written
  in
  let first_written =
    List.filter (fun (written : written) -> written.declaration.key.ordinal = 0) written
  in
  let impl_entries =
    List.concat_map
      (fun (written : written) ->
        list_impl_entries pass_lookups ~imports:(list_file_imports written.file) written.declaration
          written.item.value)
      first_written
  in
  {
    modules =
      List.fold_left
        (fun map (module_, module_declarations) ->
          Module_map.update module_
            (Option.map (fun names ->
                 { names with module_declarations = sort_declarations module_declarations }))
            map)
        modules_map module_declarations;
    files =
      File_map.mapi
        (fun file _ ->
          List.map (fun (written : written) -> written.declaration) (list_in_file file))
        imports;
    declarations;
    declared;
    members;
    traits;
    impls =
      {
        impls = impl_entries;
        by_type =
          List.fold_right
            (fun ((trait, type_), impl) by_type ->
              Path.Map.update type_
                (fun impls -> Some ((trait, impl) :: Option.value ~default:[] impls))
                by_type)
            impl_entries Path.Map.empty;
        by_trait =
          List.fold_right
            (fun ((trait, _), impl) by_trait ->
              Path.Map.update trait
                (fun impls -> Some (impl :: Option.value ~default:[] impls))
                by_trait)
            impl_entries Path.Map.empty;
      };
    law_proofs =
      Law_proof_map.map List.rev
        (List.fold_left
           (fun index (written : written) ->
             match find_law_proof_entry pass_lookups written.declaration with
             | Some name ->
                 Law_proof_map.update name
                   (fun keys -> Some (key_of_written written :: Option.value ~default:[] keys))
                   index
             | None -> index)
           Law_proof_map.empty first_written);
  }

let empty =
  {
    modules = Module_map.empty;
    files = File_map.empty;
    declarations = [];
    declared = Key_map.empty;
    members = Member_map.empty;
    traits = String_map.empty;
    impls = { impls = []; by_type = Path.Map.empty; by_trait = Path.Map.empty };
    law_proofs = Law_proof_map.empty;
  }

type change =
  | Module of Path.module_
  | Entry of Path.module_ * string
  | Entries of Path.module_
  | Imports of Names.key
  | Declaration of Names.key
  | Tree of Names.key
  | Positions of Names.key
  | Text of Names.key
  | Place of Names.key
  | Container of Names.key
  | Contained of Names.key
  | Module_declarations of Path.module_
  | File_declarations of Path.file
  | Package_declarations
  | Members of Path.t * string
  | Traits_declaring of string
  | Impl_index
  | Impls_of_type of Path.t
  | Impls_of_trait of Path.t
  | Law_proofs of Names.law_proof_name

let differs before after = compare before after <> 0

let pair_entries merge before after =
  merge (fun _ before after -> Some (before, after)) before after

let list_changes before after =
  let entries_of = Option.fold ~none:String_map.empty ~some:(fun names -> names.entries_by_name) in
  let modules =
    Module_map.fold
      (fun module_ ((before : module_names option), (after : module_names option)) changes ->
        let select_before_and_after select = (Option.map select before, Option.map select after) in
        let entries_before, entries_after = select_before_and_after (fun names -> names.entries) in
        let declarations_before, declarations_after =
          select_before_and_after (fun names -> names.module_declarations)
        in
        (if Option.is_some before <> Option.is_some after then [ Module module_ ] else [])
        @ (if differs entries_before entries_after then [ Entries module_ ] else [])
        @ (if differs declarations_before declarations_after then [ Module_declarations module_ ]
           else [])
        @ String_map.fold
            (fun name (before, after) changes ->
              if differs before after then Entry (module_, name) :: changes else changes)
            (pair_entries String_map.merge (entries_of before) (entries_of after))
            []
        @ changes)
      (pair_entries Module_map.merge before.modules after.modules)
      []
  in
  let files =
    File_map.fold
      (fun file (before, after) changes ->
        if differs before after then File_declarations file :: changes else changes)
      (pair_entries File_map.merge before.files after.files)
      []
  in
  let declared =
    Key_map.fold
      (fun key ((before : declared option), (after : declared option)) changes ->
        (match (before, after) with
          | Some before, Some after ->
              let list_changed change select =
                if differs (select before) (select after) then [ change ] else []
              in
              list_changed (Declaration key) (fun declared -> declared.declaration)
              @ (if
                   differs before.item.value after.item.value
                   || List.compare_lengths before.item.positions.syntax_errors
                        after.item.positions.syntax_errors
                      <> 0
                 then [ Tree key ]
                 else if differs before.item.positions after.item.positions then [ Positions key ]
                 else [])
              @ list_changed (Text key) (fun declared -> declared.text)
              @ list_changed (Place key) (fun declared -> declared.place)
              @ list_changed (Imports key) (fun declared -> declared.imports)
              @ list_changed (Container key) (fun declared -> declared.container)
              @ list_changed (Contained key) (fun declared -> declared.contained)
          | Some _, None | None, Some _ ->
              [
                Declaration key;
                Tree key;
                Text key;
                Place key;
                Imports key;
                Container key;
                Contained key;
              ]
          | None, None -> [])
        @ changes)
      (pair_entries Key_map.merge before.declared after.declared)
      []
  in
  let members =
    Member_map.fold
      (fun (owner, name) (before, after) changes ->
        if differs before after then Members (owner, name) :: changes else changes)
      (pair_entries Member_map.merge before.members after.members)
      []
  in
  let traits =
    String_map.fold
      (fun name (before, after) changes ->
        if differs before after then Traits_declaring name :: changes else changes)
      (pair_entries String_map.merge before.traits after.traits)
      []
  in
  let law_proofs =
    Law_proof_map.fold
      (fun name (before, after) changes ->
        if differs before after then Law_proofs name :: changes else changes)
      (pair_entries Law_proof_map.merge before.law_proofs after.law_proofs)
      []
  in
  let list_changed_impls change select =
    Path.Map.fold
      (fun path (before, after) changes ->
        if differs before after then change path :: changes else changes)
      (pair_entries Path.Map.merge (select before.impls) (select after.impls))
      []
  in
  modules @ files
  @ (if differs before.declarations after.declarations then [ Package_declarations ] else [])
  @ declared @ members @ traits
  @ (if differs before.impls.impls after.impls.impls then [ Impl_index ] else [])
  @ list_changed_impls (fun type_ -> Impls_of_type type_) (fun impls -> impls.by_type)
  @ list_changed_impls (fun trait -> Impls_of_trait trait) (fun impls -> impls.by_trait)
  @ law_proofs

let make_lookups ~(read_namespace : Path.package -> t) ~split_module ~list_dependency_names :
    Names.lookups =
  let of_module (module_ : Path.module_) =
    Module_map.find_opt module_ (read_namespace module_.package).modules
  in
  let of_file (file : Path.file) =
    File_map.find_opt file (read_namespace file.module_.package).files
  in
  let find_declared (key : Names.key) =
    Key_map.find_opt key (read_namespace key.module_.package).declared
  in
  let read_declared key =
    match find_declared key with
    | Some declared -> declared
    | None -> Compiler_bug.raise_bug ~stage:"Namespace" "%s is not declared" (Names.show_key key)
  in
  let list_members owner name =
    Option.value ~default:[]
      (Member_map.find_opt (owner, name) (read_namespace (Path.locate_package owner)).members)
  in
  {
    find =
      (fun module_ name ->
        Option.bind (of_module module_) (fun names ->
            String_map.find_opt name names.entries_by_name));
    list_entries =
      (fun module_ -> match of_module module_ with Some names -> names.entries | None -> []);
    list_imports = (fun key -> (read_declared key).imports);
    module_exists = (fun module_ -> Option.is_some (of_module module_));
    split_module;
    list_dependency_names;
    find_key =
      (fun (path : Path.t) ->
        match path with
        | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ }
          ->
            if module_ = Well_known.intrinsic_module then None
            else
              Option.map
                (fun (declared : declared) -> declared.declaration.key)
                (find_declared { module_; path; ordinal = 0 })
        | Method { owner; name; _ } | Member_constant { owner; name } ->
            List.find_opt
              (fun (key : Names.key) -> Path.equal key.path path)
              (list_members owner name)
        | Derived _ | Unresolved _ -> None);
    read_declaration = (fun key -> (read_declared key).declaration);
    list_declarations =
      (fun module_ ->
        match of_module module_ with Some names -> names.module_declarations | None -> []);
    list_declarations_in = (fun file -> Option.value ~default:[] (of_file file));
    list_package_declarations = (fun package -> (read_namespace package).declarations);
    read_definition = (fun key -> (read_declared key).item.value);
    read_text = (fun key -> (read_declared key).text);
    read_spans = (fun key -> (read_declared key).item.positions.spans);
    list_syntax_errors = (fun key -> (read_declared key).item.positions.syntax_errors);
    read_place = (fun key -> (read_declared key).place);
    find_container = (fun key -> (read_declared key).container);
    list_contained = (fun key -> (read_declared key).contained);
    list_members;
    list_traits_declaring =
      (fun package name ->
        Option.value ~default:[] (String_map.find_opt name (read_namespace package).traits));
    list_impls = (fun package -> (read_namespace package).impls.impls);
    list_impls_of_type =
      (fun package type_ ->
        Option.value ~default:[] (Path.Map.find_opt type_ (read_namespace package).impls.by_type));
    list_impls_of_trait =
      (fun package trait ->
        Option.value ~default:[] (Path.Map.find_opt trait (read_namespace package).impls.by_trait));
    list_law_proofs =
      (fun package name ->
        Option.value ~default:[] (Law_proof_map.find_opt name (read_namespace package).law_proofs));
  }
