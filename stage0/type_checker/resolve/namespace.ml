module Path_table = Hashtbl.Make (Path)

module Item_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.file * int
end))

let convert_visibility : Syntax.visibility option -> Names.visibility = function
  | None -> Private
  | Some Internal -> Internal
  | Some Public -> Public
  | Some Public_opaque -> Public_opaque

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
        Names.Scope.lookup_module lookups
          ~visible_packages:(Names.list_visible_packages lookups from.package)
          ~from ~imports first.text
          (List.map (fun (name : Syntax.name) -> name.text) rest)
      with
      | Found_module { module_; _ } -> (
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
  | Named reference -> list_reference_paths reference
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

let compare_key (left : Names.key) (right : Names.key) =
  match compare left.module_ right.module_ with
  | 0 -> (
      match Path.compare left.path right.path with
      | 0 -> Int.compare left.ordinal right.ordinal
      | order -> order)
  | order -> order

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

let find_impl_heads (lookups : Names.lookups) (impl : Path.t) =
  match impl with
  | Impl { trait = { path = trait; _ }; for_type; _ }
    when is_head_kind lookups trait ~kinds:[ Trait; Capability ]
         && is_head_kind lookups for_type ~kinds:[ Type ] ->
      Some (trait, for_type)
  | _ -> None

let list_impl_entries (lookups : Names.lookups) ~imports (declaration : Names.declaration)
    (definition : Syntax.definition) =
  match (declaration.key.path, definition.kind) with
  | Impl _, _ ->
      List.map
        (fun heads -> (heads, declaration.key.path))
        (Option.to_list (find_impl_heads lookups declaration.key.path))
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

type declared_definition = {
  declaration : Names.declaration;
  file : Path.file;
  position : int;
  container : Names.key option;
  item : Syntax.definition Syntax.item;
}

type module_declarations = {
  definitions : declared_definition list;
  imports : (Path.file * (string * Path.module_) list) list;
  impls : ((Path.t * Path.t) * Path.t) list;
  law_proofs : (Names.law_proof_name * Names.key) list;
}

let list_entries (file : Syntax.file) = list_file_entries file.definitions

let declare (lookups : Names.lookups) (files : (Path.file * Syntax.file * string) list) =
  let imports =
    List.map
      (fun ((file : Path.file), (parsed : Syntax.file), _) ->
        ( file,
          List.map
            (fun (item : Syntax.path Syntax.item) ->
              let used = Names.resolve_used_module lookups ~from:file.module_ item.value in
              (Names.Scope.extract_last_name used, used))
            parsed.uses ))
      files
  in
  let list_file_imports file = Option.value ~default:[] (List.assoc_opt file imports) in
  let written =
    number_written
      (List.concat_map
         (fun ((file : Path.file), (parsed : Syntax.file), text) ->
           list_file_declarations lookups file ~imports:(list_file_imports file) ~text
             parsed.definitions)
         files)
  in
  let at_index = Item_table.create 64 in
  List.iter
    (fun (written : written) -> Item_table.replace at_index (written.file, written.index) written)
    written;
  let first_written =
    List.filter (fun (written : written) -> written.declaration.key.ordinal = 0) written
  in
  {
    definitions =
      List.map
        (fun (written : written) ->
          {
            declaration = written.declaration;
            file = written.file;
            position = written.index;
            container =
              Option.map
                (fun (container : written) -> container.declaration.key)
                (Option.bind written.container (fun index ->
                     Item_table.find_opt at_index (written.file, index)));
            item = written.item;
          })
        written;
    imports;
    impls =
      List.concat_map
        (fun (written : written) ->
          list_impl_entries lookups ~imports:(list_file_imports written.file) written.declaration
            written.item.value)
        first_written;
    law_proofs =
      List.filter_map
        (fun (written : written) ->
          Option.map
            (fun name -> (name, written.declaration.key))
            (find_law_proof_entry lookups written.declaration))
        first_written;
  }
