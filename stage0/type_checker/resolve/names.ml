module Path_table = Hashtbl.Make (Path)

module File_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.file
end))

module Item_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Path.file * int
end))

type kind =
  | Function
  | Type
  | Trait
  | Capability
  | Constant
  | Theorem
  | Method
  | Member_constant
  | Impl
  | Test
  | Law_proof

type named = Function | Type | Trait | Capability | Constant | Theorem

let kind_of_named : named -> kind = function
  | Function -> Function
  | Type -> Type
  | Trait -> Trait
  | Capability -> Capability
  | Constant -> Constant
  | Theorem -> Theorem

let show_kind : kind -> string = function
  | Function -> "a function"
  | Type -> "a type"
  | Trait -> "a trait"
  | Capability -> "a capability"
  | Constant -> "a constant"
  | Theorem -> "a theorem"
  | Method -> "a method"
  | Member_constant -> "a constant"
  | Impl -> "an `impl`"
  | Test -> "a test"
  | Law_proof -> "a law's proof"

type declaration = {
  module_ : Path.module_;
  path : Path.t;
  ordinal : int;
  kind : kind;
  visibility : Syntax.visibility;
  generic : bool;
}

type key = { module_ : Path.module_; path : Path.t; ordinal : int }

let make_key (declaration : declaration) =
  { module_ = declaration.module_; path = declaration.path; ordinal = declaration.ordinal }

type place = { file : Path.file; base : int }

let show_key key =
  if key.ordinal = 0 then Path.show key.path
  else Printf.sprintf "%s#%d" (Path.show key.path) key.ordinal

let extract_signature_name (signature : Syntax.signature) =
  match signature.name with Plain_name name | Member_name (_, name) -> name

let classify_receiver (parameters : Syntax.parameter list) : Path.receiver =
  match parameters with
  | { kind = Self_parameter None; _ } :: _ -> Read
  | { kind = Self_parameter (Some Mut); _ } :: _ -> Mut
  | { kind = Self_parameter (Some Own); _ } :: _ -> Own
  | _ -> Static

let extract_last_name (module_ : Path.module_) =
  match List.rev (Path.list_module_parts module_) with last :: _ -> last | [] -> ""

type entry = { name : string; kind : named; visibility : Syntax.visibility; generic : bool }

module String_map = Map.Make (String)

let is_type_kind : named -> bool = function
  | Type | Trait | Capability -> true
  | Function | Constant | Theorem -> false

let is_value_kind kind = not (is_type_kind kind)
let is_public = function Syntax.Public | Public_opaque -> true | Private | Internal -> false

let is_visible ~(from : Path.module_) (module_ : Path.module_) visibility =
  module_ = from || is_public visibility || (visibility = Internal && module_.package = from.package)

type impl_index = {
  impls : ((Path.t * Path.t) * Path.t) list;
  by_type : (Path.t * Path.t) list Path.Map.t;
  by_trait : Path.t list Path.Map.t;
}

type law_proof_name = { trait : Path.t; law : string; type_head : Path.t }

type lookups = {
  find : Path.module_ -> string -> entry option;
  entries : Path.module_ -> entry list;
  imports : key -> (string * Path.module_) list;
  module_exists : Path.module_ -> bool;
  split_module : string list -> Path.module_ option;
  dependency_names : Path.package -> Path.package list;
  key : Path.t -> key option;
  declaration : key -> declaration;
  declarations : Path.module_ -> declaration list;
  declarations_in : Path.file -> declaration list;
  package_declarations : Path.package -> declaration list;
  definition : key -> Syntax.definition;
  text : key -> string;
  spans : key -> Source.Definition_span.t array;
  recovered : key -> Source.Definition_span.t list;
  place : key -> place;
  container : key -> key option;
  contained : key -> key list;
  members : Path.t -> string -> key list;
  traits_declaring : Path.package -> string -> Path.t list;
  impls : Path.package -> ((Path.t * Path.t) * Path.t) list;
  impls_of_type : Path.package -> Path.t -> (Path.t * Path.t) list;
  impls_of_trait : Path.package -> Path.t -> Path.t list;
  law_proofs : Path.package -> law_proof_name -> key list;
}

let list_visible_packages lookups package =
  List.sort_uniq compare (package :: Path.standard_package :: lookups.dependency_names package)

let list_transitive_dependencies lookups package =
  let rec close seen = function
    | [] -> seen
    | name :: rest when List.mem name seen -> close seen rest
    | name :: rest -> close (name :: seen) (lookups.dependency_names name @ rest)
  in
  let standard = if package = Path.standard_package then [] else [ Path.standard_package ] in
  List.filter (fun name -> name <> package) (close [] (standard @ lookups.dependency_names package))

let resolve_full_module lookups ~(from : Path.module_) first rest : Path.module_ =
  let known = list_visible_packages lookups from.package in
  match Path.split_module ~is_package:(fun package -> List.mem package known) (first :: rest) with
  | Some module_ -> module_
  | None -> { package = { owner = None; name = first }; modules = rest }

let resolve_used_module lookups ~from (path : Syntax.path) =
  let texts = List.map (fun (name : Syntax.name) -> name.text) in
  match path.modules with
  | [] -> resolve_full_module lookups ~from path.last.text []
  | first :: rest -> resolve_full_module lookups ~from first.text (texts rest @ [ path.last.text ])

let is_visible_module lookups ~(from : Path.module_) (module_ : Path.module_) =
  module_ = Intrinsic.module_
  || List.mem module_.package (list_visible_packages lookups from.package)
     && lookups.module_exists module_

type module_lookup =
  | Found_module of Path.module_ * [ `Import of string | `Package ]
  | Ambiguous_module of Path.module_ * Path.module_
  | No_module of string

let lookup_module lookups ~(from : Path.module_) ~imports first rest =
  let imported =
    Option.map
      (fun (module_ : Path.module_) : Path.module_ ->
        { module_ with modules = module_.modules @ rest })
      (List.assoc_opt first imports)
  in
  let package = resolve_full_module lookups ~from first rest in
  let exists module_ = is_visible_module lookups ~from module_ in
  match imported with
  | Some imported when exists imported && exists package && imported <> package ->
      Ambiguous_module (imported, package)
  | Some imported when exists imported -> Found_module (imported, `Import first)
  | _ when exists package -> Found_module (package, `Package)
  | _ -> No_module (String.concat "::" (first :: rest))

let make_top_path module_ name : Path.t = Top { module_; name }

let find_recovery_report (lookups : lookups) key part =
  Parts.find_recovered_report ~spans:(lookups.spans key) ~recovered:(lookups.recovered key)
    (lookups.definition key) part

let is_broken lookups key part = Option.is_some (find_recovery_report lookups key part)

let find_definition lookups path =
  Option.map (fun key -> (key, lookups.definition key)) (lookups.key path)

let find_law_parameters lookups (trait : Path.t) law =
  match find_definition lookups trait with
  | Some (_, { kind = Trait { members; _ }; _ }) ->
      List.find_map
        (fun (member : Syntax.trait_member Syntax.node) ->
          match member.kind with
          | Law written_law when written_law.name.text = law ->
              Some
                (List.filter_map
                   (fun (parameter : Syntax.parameter) ->
                     match parameter.kind with
                     | Named_parameter { name; _ } -> Some name.text
                     | Self_parameter _ | Parameter_error -> None)
                   written_law.parameters)
          | _ -> None)
        members
  | _ -> None

type generic_kind = Type_kind | Value_kind | Capability_kind

let list_generic_kinds (generics : Syntax.generic_parameter list) =
  List.filter_map
    (fun (generic : Syntax.generic_parameter) ->
      match generic.kind with
      | Type_parameter (name, _) -> Some (name.text, Type_kind)
      | Value_parameter (name, _) -> Some (name.text, Value_kind)
      | Capability_parameter name -> Some (name.text, Capability_kind)
      | Generic_error -> None)
    generics

let find_generics lookups (path : Path.t) =
  match Intrinsic.builtin_of_path path with
  | Some Array -> Some [ ("Element", Type_kind); ("count", Value_kind) ]
  | Some (Storage | View) -> Some [ ("Element", Type_kind) ]
  | Some Shared -> Some [ ("Value", Type_kind) ]
  | Some _ -> Some []
  | None -> (
      match find_definition lookups path with
      | Some (key, definition) -> (
          if is_broken lookups key Header then None
          else
            match definition.kind with
            | Type_definition { generics; _ } | Trait { generics; _ } ->
                Some (list_generic_kinds generics)
            | Capability _ -> Some []
            | _ -> None)
      | None -> None)

let find_kind lookups (path : Path.t) =
  match path with
  | Top { module_; name } ->
      Option.map (fun (entry : entry) -> entry.kind) (lookups.find module_ name)
  | _ -> None

let named_of_intended : Syntax.intended_kind -> named = function
  | Intended_function -> Function
  | Intended_constant -> Constant
  | Intended_type -> Type
  | Intended_trait -> Trait
  | Intended_capability -> Capability
  | Intended_theorem -> Theorem

let list_file_entries (top_levels : Syntax.top_level list) =
  List.concat_map
    (fun (top_level : Syntax.top_level) ->
      let definition = top_level.definition.value in
      let plain name kind generic =
        [ { name; kind; visibility = definition.visibility; generic } ]
      in
      match definition.kind with
      | Function { signature = { name = Plain_name name; generics; _ }; _ } ->
          plain name.text Function (generics <> [])
      | Type_definition { name; generics; _ } -> plain name.text Type (generics <> [])
      | Trait { name; generics; _ } -> plain name.text Trait (generics <> [])
      | Capability { name; _ } -> plain name.text Capability false
      | Constant { name = Plain_name name; _ } -> plain name.text Constant false
      | Theorem { name; generics; _ } -> plain name.text Theorem (generics <> [])
      | Definition_error { name = Some (Plain_name name); intended = Some intended } ->
          plain name.text (named_of_intended intended) false
      | Function _ | Method_declaration _ | Constant _ | Impl _ | Test _ | Law_proof _
      | Definition_error _ ->
          [])
    top_levels

let builtin_entries =
  List.map
    (fun builtin ->
      {
        name = Intrinsic.show_builtin builtin;
        kind = Type;
        visibility = Public;
        generic = (match builtin with Array | Storage | View | Shared -> true | _ -> false);
      })
    Intrinsic.builtins
  @ List.map
      (fun operation ->
        {
          name = Intrinsic.show_operation operation;
          kind = Function;
          visibility = Public;
          generic = true;
        })
      Intrinsic.operations

type name_lookup = Found_name of entry * Path.t | Hidden_name of entry | No_name

let find_in lookups ~(from : Path.module_) module_ name ~is_kind =
  match lookups.find module_ name with
  | Some item when is_kind item.kind ->
      if is_visible ~from module_ item.visibility then Found_name (item, make_top_path module_ name)
      else Hidden_name item
  | _ -> No_name

let find_bare_type lookups ~(from : Path.module_) name =
  match lookups.find from name with
  | Some item when is_type_kind item.kind -> Some (item, make_top_path from name)
  | _ -> (
      match Prelude.find_type name with
      | Some module_ -> (
          match lookups.find module_ name with
          | Some item when is_type_kind item.kind -> Some (item, make_top_path module_ name)
          | _ -> None)
      | None -> None)

let find_head_type lookups ~(from : Path.module_) ~imports (path : Syntax.path) =
  match path.modules with
  | [] -> find_bare_type lookups ~from path.last.text
  | first :: rest -> (
      match
        lookup_module lookups ~from ~imports first.text
          (List.map (fun (name : Syntax.name) -> name.text) rest)
      with
      | Found_module (module_, _) -> (
          match find_in lookups ~from module_ path.last.text ~is_kind:is_type_kind with
          | Found_name (item, path) -> Some (item, path)
          | Hidden_name _ | No_name -> None)
      | Ambiguous_module _ | No_module _ -> None)

let make_unresolved_path (file : Path.file) names : Path.t = Unresolved { file; names }

let resolve_type_path lookups ~(file : Path.file) ~imports (path : Syntax.path) : Path.t =
  match find_head_type lookups ~from:file.module_ ~imports path with
  | Some (_, resolved) -> resolved
  | None ->
      make_unresolved_path file
        (List.map (fun (name : Syntax.name) -> name.text) (path.modules @ [ path.last ]))

let list_head_parameters (head : Syntax.type_head) =
  List.filter_map
    (fun (generic : Syntax.generic_parameter) ->
      match generic.kind with
      | Type_parameter (name, _) | Value_parameter (name, _) | Capability_parameter name ->
          Some name.text
      | Generic_error -> None)
    head.generics

let resolve_count lookups ~(file : Path.file) ~parameters (name : Syntax.name) : Path.argument =
  if List.mem name.text parameters then Parameter name.text
  else
    match lookups.find file.module_ name.text with
    | Some { kind = Constant; _ } -> Constant (make_top_path file.module_ name.text)
    | _ -> Constant (make_unresolved_path file [ name.text ])

let rec resolve_reference lookups ~file ~imports ~parameters ~self (written : Syntax.path_type) :
    Path.reference =
  let argument = resolve_argument lookups ~file ~imports ~parameters ~self in
  {
    path = resolve_type_path lookups ~file ~imports written.path;
    arguments =
      List.filter_map
        (function
          | Syntax.Type_argument type_ -> Some (argument type_)
          | Count (value, _) -> Some (Path.Count value)
          | Count_name name -> Some (resolve_count lookups ~file ~parameters name)
          | Constraint _ -> None)
        written.arguments;
    associated =
      List.sort compare
        (List.filter_map
           (function
             | Syntax.Constraint (name, type_) -> Some (name.text, argument type_)
             | Type_argument _ | Count _ | Count_name _ -> None)
           written.arguments);
  }

and resolve_argument lookups ~file ~imports ~parameters ~self (type_ : Syntax.type_expression) :
    Path.argument =
  let rejected names : Path.argument =
    Named { path = make_unresolved_path file names; arguments = []; associated = [] }
  in
  match type_.kind with
  | Path_type { path = { modules = []; last }; arguments = []; _ }
    when List.mem last.text parameters ->
      Parameter last.text
  | Path_type written -> Named (resolve_reference lookups ~file ~imports ~parameters ~self written)
  | Any_type written -> Any (resolve_reference lookups ~file ~imports ~parameters ~self written)
  | Self_type None ->
      Named
        {
          path = self;
          arguments = List.map (fun name -> Path.Parameter name) parameters;
          associated = [];
        }
  | Self_type (Some name) -> rejected [ "Self"; name.text ]
  | Associated (base, name) -> rejected [ base.text; name.text ]
  | Function_type _ -> rejected [ "fn" ]
  | Type_error -> rejected []

let resolve_header lookups ~file ~imports (trait_ : Syntax.path_type) (head : Syntax.type_head) =
  let for_type = resolve_type_path lookups ~file ~imports head.path in
  ( resolve_reference lookups ~file ~imports ~parameters:(list_head_parameters head) ~self:for_type
      trait_,
    for_type )

type written = {
  declaration : declaration;
  file : Path.file;
  index : int;
  container : int option;
  item : Syntax.definition Syntax.item;
  text : string;
}

let list_file_declarations lookups (file : Path.file) ~imports ~text
    (top_levels : Syntax.top_level list) =
  let module_ = file.module_ in
  let owner (head : Syntax.type_head) = resolve_type_path lookups ~file ~imports head.path in
  let header = resolve_header lookups ~file ~imports in
  let written index ?container (item : Syntax.definition Syntax.item) path kind generic =
    Some
      {
        declaration =
          { module_; path; ordinal = 0; kind; visibility = item.value.visibility; generic };
        file;
        index;
        container;
        item;
        text = String.sub text item.base (item.stop - item.base);
      }
  in
  let method_declaration index ~container ~owner:(owner, static)
      (item : Syntax.definition Syntax.item) =
    let declare = written index ~container item in
    match item.value.kind with
    | Function { signature; _ } | Method_declaration signature ->
        declare
          (Method
             {
               owner;
               name = (extract_signature_name signature).text;
               receiver = (if static then Static else classify_receiver signature.parameters);
             })
          Method (signature.generics <> [])
    | Definition_error { name = Some (Plain_name name | Member_name (_, name)); _ } ->
        declare (Method { owner; name = name.text; receiver = Static }) Method false
    | _ -> None
  in
  let top_level_declaration index (item : Syntax.definition Syntax.item) =
    let declare = written index item in
    match item.value.kind with
    | Function { signature = { name = Plain_name name; generics; _ }; _ } ->
        declare (make_top_path module_ name.text) Function (generics <> [])
    | Function { signature = { name = Member_name (head, name); generics; parameters; _ }; _ } ->
        declare
          (Method { owner = owner head; name = name.text; receiver = classify_receiver parameters })
          Method (generics <> [])
    | Type_definition { name; generics; _ } ->
        declare (make_top_path module_ name.text) Type (generics <> [])
    | Trait { name; generics; _ } -> declare (make_top_path module_ name.text) Trait (generics <> [])
    | Capability { name; _ } -> declare (make_top_path module_ name.text) Capability false
    | Constant { name = Plain_name name; _ } ->
        declare (make_top_path module_ name.text) Constant false
    | Constant { name = Member_name (head, name); _ } ->
        declare (Member_constant { owner = owner head; name = name.text }) Member_constant false
    | Theorem { name; generics; _ } ->
        declare (make_top_path module_ name.text) Theorem (generics <> [])
    | Impl { trait_; type_; _ } ->
        let trait, for_type = header trait_ type_ in
        declare (Impl { module_; trait; for_type }) Impl (type_.generics <> [])
    | Test { name; _ } ->
        let text =
          name.first.value
          ^ String.concat "" (List.map (fun (_, (text : Syntax.text)) -> text.value) name.rest)
        in
        declare (Test { module_; name = text }) Test false
    | Law_proof { trait_; law; type_; _ } ->
        let trait, for_type = header trait_ type_ in
        declare (Law_proof { module_; trait; law = law.text; for_type }) Law_proof false
    | Definition_error { name = Some (Plain_name name); intended = Some intended } ->
        declare (make_top_path module_ name.text) (kind_of_named (named_of_intended intended)) false
    | Definition_error { name = Some (Member_name (head, name)); intended } ->
        let owner = owner head in
        if intended = Some Intended_constant then
          declare (Member_constant { owner; name = name.text }) Member_constant false
        else declare (Method { owner; name = name.text; receiver = Static }) Method false
    | Method_declaration _
    | Definition_error { name = None; _ }
    | Definition_error { intended = None; _ } ->
        None
  in
  let _, declared =
    List.fold_left
      (fun (index, declared) (top_level : Syntax.top_level) ->
        let container = top_level_declaration index top_level.definition in
        let owner =
          match (top_level.definition.value.kind, container) with
          | (Trait _ | Impl _), Some container -> Some (container.declaration.path, false)
          | Capability _, Some container -> Some (container.declaration.path, true)
          | _ -> None
        in
        let methods =
          match owner with
          | Some owner ->
              List.mapi
                (fun offset method_item ->
                  method_declaration (index + 1 + offset) ~container:index ~owner method_item)
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

let compare_key (left : key) (right : key) =
  match compare left.module_ right.module_ with
  | 0 -> (
      match Path.compare left.path right.path with
      | 0 -> Int.compare left.ordinal right.ordinal
      | order -> order)
  | order -> order

module Key_map = Map.Make (struct
  type t = key

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
  type t = law_proof_name

  let compare (left : law_proof_name) (right : law_proof_name) =
    match Path.compare left.trait right.trait with
    | 0 -> (
        match String.compare left.law right.law with
        | 0 -> Path.compare left.type_head right.type_head
        | order -> order)
    | order -> order
end)

type declared = {
  declaration : declaration;
  item : Syntax.definition Syntax.item;
  text : string;
  place : place;
  imports : (string * Path.module_) list;
  container : key option;
  contained : key list;
}

type module_names = {
  entries : entry list;
  index : entry String_map.t;
  module_declarations : declaration list;
}

type namespace = {
  modules : module_names Module_map.t;
  files : declaration list File_map.t;
  declarations : declaration list;
  declared : declared Key_map.t;
  members : key list Member_map.t;
  traits : Path.t list String_map.t;
  impls : impl_index;
  law_proofs : key list Law_proof_map.t;
}

let make_module_names entries =
  {
    entries;
    index =
      List.fold_left
        (fun index (entry : entry) ->
          if String_map.mem entry.name index then index else String_map.add entry.name entry index)
        String_map.empty entries;
    module_declarations = [];
  }

let number_written (written : written list) =
  let counts = Path_table.create 16 in
  List.map
    (fun (written : written) ->
      let path = written.declaration.path in
      let ordinal = Option.value ~default:0 (Path_table.find_opt counts path) in
      Path_table.replace counts path (ordinal + 1);
      { written with declaration = { written.declaration with ordinal } })
    written

let is_derivable (trait : Path.t) =
  match Well_known.of_path trait with
  | Some (Equal | Hash | Ordered | Default | Serialize | Deserialize) -> true
  | _ -> false

let is_head_kind lookups (path : Path.t) ~(kinds : named list) =
  match find_kind lookups path with
  | Some kind when List.mem kind kinds -> (
      match Intrinsic.builtin_of_path path with Some (Never | Integer) -> false | _ -> true)
  | _ -> false

let resolve_head lookups ~from ~imports (path : Syntax.path) ~kinds =
  match find_head_type lookups ~from ~imports path with
  | Some (_, path) when is_head_kind lookups path ~kinds -> Some path
  | _ -> None

let list_impl_entries lookups ~imports (declaration : declaration) (definition : Syntax.definition)
    =
  match (declaration.path, definition.kind) with
  | Impl { trait = { path = trait; _ }; for_type; _ }, _ ->
      if
        is_head_kind lookups trait ~kinds:[ Trait; Capability ]
        && is_head_kind lookups for_type ~kinds:[ Type ]
      then [ ((trait, for_type), declaration.path) ]
      else []
  | _, Type_definition { clauses; _ } ->
      let resolved_head = resolve_head lookups ~from:declaration.module_ ~imports in
      List.concat_map
        (fun (clause : Syntax.type_clause) ->
          match clause.kind with
          | Derives traits ->
              List.filter_map
                (fun (trait : Syntax.path_type) ->
                  match resolved_head trait.path ~kinds:[ Trait ] with
                  | Some trait when is_derivable trait ->
                      Some
                        ( (trait, declaration.path),
                          (Derived { type_ = declaration.path; trait } : Path.t) )
                  | _ -> None)
                traits
          | Type_invariant _ | Potential _ -> [])
        clauses
  | _ -> []

let find_law_proof_entry lookups (declaration : declaration) =
  match declaration.path with
  | Law_proof { trait = { path = trait; _ }; law; for_type; _ }
    when is_head_kind lookups trait ~kinds:[ Trait ]
         && is_head_kind lookups for_type ~kinds:[ Type ] ->
      Some { trait; law; type_head = for_type }
  | _ -> None

let build_namespace lookups package
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
      (if Intrinsic.module_.package = package then
         Module_map.singleton Intrinsic.module_ (make_module_names builtin_entries)
       else Module_map.empty)
      modules
  in
  let own_find (module_ : Path.module_) name =
    if module_.package = package then
      Option.bind (Module_map.find_opt module_ modules_map) (fun names ->
          String_map.find_opt name names.index)
    else lookups.find module_ name
  in
  let own_module_exists (module_ : Path.module_) =
    if module_.package = package then Module_map.mem module_ modules_map
    else lookups.module_exists module_
  in
  let imports_of (file : Path.file) (uses : Syntax.path Syntax.item list) =
    List.map
      (fun (item : Syntax.path Syntax.item) ->
        let used = resolve_used_module lookups ~from:file.module_ item.value in
        (extract_last_name used, used))
      uses
  in
  let imports =
    List.fold_left
      (fun map (_, files) ->
        List.fold_left
          (fun map ((file : Path.file), (parsed : Syntax.file), _) ->
            File_map.add file (imports_of file parsed.uses) map)
          map files)
      File_map.empty modules
  in
  let file_imports file = Option.value ~default:[] (File_map.find_opt file imports) in
  let pass_lookups = { lookups with find = own_find; module_exists = own_module_exists } in
  let module_declarations =
    List.map
      (fun (module_, files) ->
        ( module_,
          number_written
            (List.concat_map
               (fun ((file : Path.file), (parsed : Syntax.file), text) ->
                 list_file_declarations pass_lookups file ~imports:(file_imports file) ~text
                   parsed.definitions)
               files) ))
      modules
  in
  let written = List.concat_map snd module_declarations in
  let by_key declarations =
    List.sort
      (fun (left : declaration) (right : declaration) ->
        compare_key (make_key left) (make_key right))
      (List.map (fun (written : written) -> written.declaration) declarations)
  in
  let declarations = by_key written in
  let by_file = File_table.create 16 in
  List.iter
    (fun (written : written) ->
      File_table.replace by_file written.file
        (written :: Option.value ~default:[] (File_table.find_opt by_file written.file)))
    written;
  let in_file file = List.rev (Option.value ~default:[] (File_table.find_opt by_file file)) in
  let key_of_written (written : written) = make_key written.declaration in
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
            imports = file_imports written.file;
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
         (fun index (declaration : declaration) ->
           match declaration.path with
           | (Method { owner; name; _ } | Member_constant { owner; name })
             when declaration.ordinal = 0 ->
               Member_map.update (owner, name)
                 (fun keys -> Some (make_key declaration :: Option.value ~default:[] keys))
                 index
           | _ -> index)
         Member_map.empty declarations)
  in
  let traits =
    let trait_at =
      List.filter_map
        (fun (written : written) ->
          if written.declaration.kind = Trait && written.declaration.ordinal = 0 then
            Some ((written.file, written.index), written.declaration.path)
          else None)
        written
    in
    List.fold_left
      (fun index (written : written) ->
        match (written.declaration.path, written.container) with
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
    List.filter (fun (written : written) -> written.declaration.ordinal = 0) written
  in
  let impl_entries =
    List.concat_map
      (fun (written : written) ->
        list_impl_entries pass_lookups ~imports:(file_imports written.file) written.declaration
          written.item.value)
      first_written
  in
  {
    modules =
      List.fold_left
        (fun map (module_, module_declarations) ->
          Module_map.update module_
            (Option.map (fun names ->
                 { names with module_declarations = by_key module_declarations }))
            map)
        modules_map module_declarations;
    files =
      File_map.mapi
        (fun file _ -> List.map (fun (written : written) -> written.declaration) (in_file file))
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

let empty_namespace =
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
  | Entry of Path.module_ * string
  | Entries of Path.module_
  | Imports of key
  | Declaration of key
  | Tree of key
  | Positions of key
  | Text of key
  | Place of key
  | Container of key
  | Contained of key
  | Module_declarations of Path.module_
  | File_declarations of Path.file
  | Package_declarations
  | Members of Path.t * string
  | Traits_declaring of string
  | Impl_index
  | Impls_of_type of Path.t
  | Impls_of_trait of Path.t
  | Law_proofs of law_proof_name

let differs before after = compare before after <> 0

let pair_entries merge before after =
  merge (fun _ before after -> Some (before, after)) before after

let list_changes before after =
  let entries_of = Option.fold ~none:String_map.empty ~some:(fun names -> names.index) in
  let modules =
    Module_map.fold
      (fun module_ ((before : module_names option), (after : module_names option)) changes ->
        let before_and_after select = (Option.map select before, Option.map select after) in
        let entries_before, entries_after = before_and_after (fun names -> names.entries) in
        let declarations_before, declarations_after =
          before_and_after (fun names -> names.module_declarations)
        in
        (if differs entries_before entries_after then [ Entries module_ ] else [])
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
              let changed change select =
                if differs (select before) (select after) then [ change ] else []
              in
              changed (Declaration key) (fun declared -> declared.declaration)
              @ (if
                   differs before.item.value after.item.value
                   || List.compare_lengths before.item.positions.recovered
                        after.item.positions.recovered
                      <> 0
                 then [ Tree key ]
                 else if differs before.item.positions after.item.positions then [ Positions key ]
                 else [])
              @ changed (Text key) (fun declared -> declared.text)
              @ changed (Place key) (fun declared -> declared.place)
              @ changed (Imports key) (fun declared -> declared.imports)
              @ changed (Container key) (fun declared -> declared.container)
              @ changed (Contained key) (fun declared -> declared.contained)
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
  let impls change select =
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
  @ impls (fun type_ -> Impls_of_type type_) (fun impls -> impls.by_type)
  @ impls (fun trait -> Impls_of_trait trait) (fun impls -> impls.by_trait)
  @ law_proofs

let of_namespaces ~(namespace : Path.package -> namespace) ~module_exists ~split_module
    ~dependency_names : lookups =
  let of_module (module_ : Path.module_) =
    Module_map.find_opt module_ (namespace module_.package).modules
  in
  let of_file (file : Path.file) = File_map.find_opt file (namespace file.module_.package).files in
  let declared (key : key) = Key_map.find_opt key (namespace key.module_.package).declared in
  let read_declared key =
    match declared key with
    | Some declared -> declared
    | None -> Compiler_bug.raise_bug ~stage:"Names" "%s is not declared" (show_key key)
  in
  let members owner name =
    Option.value ~default:[]
      (Member_map.find_opt (owner, name) (namespace (Path.locate_package owner)).members)
  in
  {
    find =
      (fun module_ name ->
        Option.bind (of_module module_) (fun names -> String_map.find_opt name names.index));
    entries =
      (fun module_ -> match of_module module_ with Some names -> names.entries | None -> []);
    imports = (fun key -> (read_declared key).imports);
    module_exists;
    split_module;
    dependency_names;
    key =
      (fun (path : Path.t) ->
        match path with
        | Top { module_; _ } | Impl { module_; _ } | Test { module_; _ } | Law_proof { module_; _ }
          ->
            if module_ = Intrinsic.module_ then None
            else
              Option.map
                (fun declared -> make_key declared.declaration)
                (declared { module_; path; ordinal = 0 })
        | Method { owner; name; _ } | Member_constant { owner; name } ->
            List.find_opt (fun (key : key) -> Path.equal key.path path) (members owner name)
        | Derived _ | Unresolved _ -> None);
    declaration = (fun key -> (read_declared key).declaration);
    declarations =
      (fun module_ ->
        match of_module module_ with Some names -> names.module_declarations | None -> []);
    declarations_in = (fun file -> Option.value ~default:[] (of_file file));
    package_declarations = (fun package -> (namespace package).declarations);
    definition = (fun key -> (read_declared key).item.value);
    text = (fun key -> (read_declared key).text);
    spans = (fun key -> (read_declared key).item.positions.spans);
    recovered = (fun key -> (read_declared key).item.positions.recovered);
    place = (fun key -> (read_declared key).place);
    container = (fun key -> (read_declared key).container);
    contained = (fun key -> (read_declared key).contained);
    members;
    traits_declaring =
      (fun package name ->
        Option.value ~default:[] (String_map.find_opt name (namespace package).traits));
    impls = (fun package -> (namespace package).impls.impls);
    impls_of_type =
      (fun package type_ ->
        Option.value ~default:[] (Path.Map.find_opt type_ (namespace package).impls.by_type));
    impls_of_trait =
      (fun package trait ->
        Option.value ~default:[] (Path.Map.find_opt trait (namespace package).impls.by_trait));
    law_proofs =
      (fun package name ->
        Option.value ~default:[] (Law_proof_map.find_opt name (namespace package).law_proofs));
  }
