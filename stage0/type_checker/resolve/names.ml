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

let convert_named : named -> kind = function
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

let is_constant : kind -> bool = function
  | Constant | Member_constant -> true
  | Function | Type | Trait | Capability | Theorem | Method | Impl | Test | Law_proof -> false

type visibility = Private | Internal | Public | Public_opaque
type key = { module_ : Path.module_; path : Path.t; ordinal : int }
type declaration = { key : key; kind : kind; visibility : visibility; generic : bool }
type place = { file : Path.file; base : int }

let show_key key =
  if key.ordinal = 0 then Path.show key.path
  else Printf.sprintf "%s#%d" (Path.show key.path) key.ordinal

let extract_signature_name (signature : Syntax.signature) =
  match signature.name with Plain_name name | Member_name (_, name) -> name

let classify_receiver (parameters : Syntax.parameter list) : Path.receiver =
  match parameters with
  | { kind = Self_parameter None; _ } :: _ -> Instance Read
  | { kind = Self_parameter (Some Mut); _ } :: _ -> Instance Mut
  | { kind = Self_parameter (Some Own); _ } :: _ -> Instance Own
  | _ -> Static

type entry = { name : string; kind : named; visibility : visibility; generic : bool }

let is_public = function Public | Public_opaque -> true | Private | Internal -> false

let is_visible_to_package ~(package : Path.package) (module_ : Path.module_) visibility =
  module_.package = package || is_public visibility

type law_proof_name = { trait : Path.t; law : string; type_head : Path.t }

type lookups = {
  find : Path.module_ -> string -> entry option;
  list_entries : Path.module_ -> entry list;
  list_imports : key -> (string * Path.module_) list;
  module_exists : Path.module_ -> bool;
  split_module : string list -> Path.module_ option;
  list_dependency_names : Path.package -> Path.package list;
  find_key : Path.t -> key option;
  read_declaration : key -> declaration;
  list_declarations : Path.module_ -> declaration list;
  list_declarations_in : Path.file -> declaration list;
  list_package_declarations : Path.package -> declaration list;
  read_definition : key -> Syntax.definition;
  read_text : key -> string;
  read_spans : key -> Source.Definition_span.t array;
  list_syntax_errors : key -> Source.Definition_span.t list;
  read_place : key -> place;
  find_container : key -> key option;
  list_contained : key -> key list;
  list_members : Path.t -> string -> key list;
  list_traits_declaring : Path.package -> string -> Path.t list;
  list_impls_of_type : Path.package -> Path.t -> (Path.t * Path.t) list;
  list_impls_of_trait : Path.package -> Path.t -> Path.t list;
  list_law_proofs : Path.package -> law_proof_name -> key list;
}

let list_visible_packages lookups package =
  List.sort_uniq compare (package :: Path.standard_package :: lookups.list_dependency_names package)

let list_package_roots visible_packages =
  List.sort_uniq compare
    (List.map (fun package -> List.hd (Path.list_package_parts package)) visible_packages)

let list_transitive_dependencies lookups package =
  let rec close seen = function
    | [] -> seen
    | name :: rest when List.mem name seen -> close seen rest
    | name :: rest -> close (name :: seen) (lookups.list_dependency_names name @ rest)
  in
  let standard = if package = Path.standard_package then [] else [ Path.standard_package ] in
  List.filter
    (fun name -> name <> package)
    (close [] (standard @ lookups.list_dependency_names package))

let split_full_module ~visible_packages first rest : Path.module_ =
  match
    Path.split_module ~is_package:(fun package -> List.mem package visible_packages) (first :: rest)
  with
  | Some module_ -> module_
  | None -> { package = { owner = None; name = first }; modules = rest }

let resolve_used_module lookups ~(from : Path.module_) (path : Syntax.path) =
  let visible_packages = list_visible_packages lookups from.package in
  let list_texts = List.map (fun (name : Syntax.name) -> name.text) in
  match path.modules with
  | [] -> split_full_module ~visible_packages path.last.text []
  | first :: rest ->
      split_full_module ~visible_packages first.text (list_texts rest @ [ path.last.text ])

let is_visible_package lookups ~(from : Path.module_) package =
  List.mem package (list_visible_packages lookups from.package)

let is_visible_module lookups ~from (module_ : Path.module_) =
  is_visible_package lookups ~from module_.package && lookups.module_exists module_

let find_syntax_error (lookups : lookups) key part =
  Parts.find_syntax_error ~spans:(lookups.read_spans key)
    ~syntax_errors:(lookups.list_syntax_errors key) (lookups.read_definition key) part

let is_broken lookups key part = Option.is_some (find_syntax_error lookups key part)

let find_definition lookups path =
  Option.map (fun key -> (key, lookups.read_definition key)) (lookups.find_key path)

let extract_header_id (definition : Syntax.definition) =
  match definition.kind with
  | Impl { trait_; _ } -> trait_.id
  | Type_definition { name; _ } -> name.id
  | _ -> definition.id

let read_header_id lookups key = extract_header_id (lookups.read_definition key)

let locate_definition lookups key =
  Source.Definition_span.locate (lookups.read_spans key) (lookups.read_definition key).id

type generic_kind = Type_kind | Value_kind

let list_generic_kinds (generics : Syntax.generic_parameter list) =
  List.filter_map
    (fun (generic : Syntax.generic_parameter) ->
      match generic.kind with
      | Type_parameter (name, _) -> Some (name.text, Type_kind)
      | Value_parameter (name, _) -> Some (name.text, Value_kind)
      | Generic_error -> None)
    generics

let list_builtin_generics : Language.Builtin_type.t -> (string * generic_kind) list = function
  | Array -> [ ("Element", Type_kind); ("count", Value_kind) ]
  | Storage | View -> [ ("Element", Type_kind) ]
  | Shared -> [ ("Value", Type_kind) ]
  | Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64 | Float32 | Float64 | Bool
  | Character | Unit | Never | Integer | Handle ->
      []

let find_generics lookups (path : Path.t) =
  match Well_known.find_builtin_type path with
  | Some builtin -> Some (list_builtin_generics builtin)
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

type 'visible lookup = Visible of 'visible | Hidden of (Path.t * visibility) | Absent

module Scope = struct
  let extract_last_name (module_ : Path.module_) =
    match List.rev (Path.list_module_parts module_) with last :: _ -> last | [] -> ""

  let is_type_kind : named -> bool = function
    | Type | Trait | Capability -> true
    | Function | Constant | Theorem -> false

  let is_value_kind kind = not (is_type_kind kind)

  let is_visible ~(from : Path.module_) (module_ : Path.module_) visibility =
    module_ = from || is_public visibility
    || (visibility = Internal && module_.package = from.package)

  let is_restricted_module ~(from : Path.module_) (module_ : Path.module_) =
    module_ = Well_known.intrinsic_module && from.package <> Path.standard_package

  let restricted_module_message = "Only the `standard` package can use `standard.intrinsic`."

  let describe_path_start (module_ : Path.module_) =
    Printf.sprintf
      "Every path starts with a package name, even inside the package. This file's module is `%s`."
      (Path.show_module module_)

  type module_lookup =
    | Found_module of { module_ : Path.module_; imported : Path.module_ option }
    | Restricted_module
    | Ambiguous_module of Path.module_ * Path.module_
    | No_module of string
    | No_package of string

  let lookup_module lookups ~visible_packages ~(from : Path.module_) ~imports first rest =
    let imported = List.assoc_opt first imports in
    let through_import =
      Option.map
        (fun (module_ : Path.module_) : Path.module_ ->
          { module_ with modules = module_.modules @ rest })
        imported
    in
    let package = split_full_module ~visible_packages first rest in
    let exists (module_ : Path.module_) =
      List.mem module_.package visible_packages && lookups.module_exists module_
    in
    match through_import with
    | Some module_ when exists module_ && exists package && module_ <> package ->
        Ambiguous_module (module_, package)
    | Some module_ when exists module_ -> Found_module { module_; imported }
    | _ when exists package ->
        if is_restricted_module ~from package then Restricted_module
        else Found_module { module_ = package; imported = None }
    | None when not (List.mem package.package visible_packages) ->
        No_package (String.concat "." (first :: rest))
    | _ -> No_module (String.concat "." (first :: rest))

  let make_top_path module_ name : Path.t = Top { module_; name }

  let lookup_in lookups ~(from : Path.module_) module_ name ~is_kind =
    match lookups.find module_ name with
    | Some item when is_kind item.kind ->
        let path = make_top_path module_ name in
        if is_visible ~from module_ item.visibility then Visible (item, path)
        else Hidden (path, item.visibility)
    | _ -> Absent

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
end

let lookup_member lookups ~(from : Path.module_) member =
  match lookups.find_key member with
  | Some key ->
      let declaration = lookups.read_declaration key in
      if Scope.is_visible ~from declaration.key.module_ declaration.visibility then Visible member
      else Hidden (member, declaration.visibility)
  | None -> Absent

let list_member_lookups lookups ~(from : Path.module_) owner name =
  List.fold_left
    (fun members (key : key) ->
      if
        List.exists
          (function
            | Visible member | Hidden (member, _) -> Path.equal member key.path | Absent -> false)
          members
      then members
      else
        let declaration = lookups.read_declaration key in
        members
        @ [
            (if Scope.is_visible ~from declaration.key.module_ declaration.visibility then
               Visible key.path
             else Hidden (key.path, declaration.visibility));
          ])
    [] (lookups.list_members owner name)

let choose_member members (member : Path.t) =
  Option.value ~default:Absent
    (List.find_opt
       (function Visible path | Hidden (path, _) -> Path.equal path member | Absent -> false)
       members)

let map_visible convert = function
  | Visible visible -> Visible (convert visible)
  | Hidden hidden -> Hidden hidden
  | Absent -> Absent

let find_hidden lookups =
  List.find_map (function Hidden hidden -> Some hidden | Visible _ | Absent -> None) lookups

let choose_visible lookups =
  match List.find_opt (function Visible _ -> true | Hidden _ | Absent -> false) lookups with
  | Some visible -> visible
  | None -> ( match find_hidden lookups with Some hidden -> Hidden hidden | None -> Absent)

let collect_visible lookups =
  match
    List.filter_map (function Visible visible -> Some visible | Hidden _ | Absent -> None) lookups
  with
  | _ :: _ as visible -> Visible visible
  | [] -> ( match find_hidden lookups with Some hidden -> Hidden hidden | None -> Absent)

let describe_hidden hidden (visibility : visibility) =
  Printf.sprintf "`%s` is %s, so it cannot be used here." (Path.show hidden)
    (match visibility with
    | Private -> "private to its module"
    | Internal -> "internal to its package"
    | Public | Public_opaque ->
        Compiler_bug.raise_bug ~stage:"Names" "%s is public, so it is not hidden" (Path.show hidden))

let list_declaring_trait_lookups lookups ~visible_packages ~(from : Path.module_) name =
  List.concat_map
    (fun package ->
      List.map
        (fun (trait : Path.t) ->
          match trait with
          | Top { module_; name = trait_name } ->
              map_visible snd
                (Scope.lookup_in lookups ~from module_ trait_name ~is_kind:(fun (kind : named) ->
                     kind = Trait))
          | _ ->
              Compiler_bug.raise_bug ~stage:"Names" "the trait %s is not a top-level definition"
                (Path.show trait))
        (lookups.list_traits_declaring package name))
    visible_packages

let list_members_visible_to_package lookups ~(package : Path.package) owner name =
  List.filter
    (fun key ->
      let declaration = lookups.read_declaration key in
      is_visible_to_package ~package declaration.key.module_ declaration.visibility)
    (lookups.list_members owner name)

let derived_methods : Well_known.method_ list =
  [
    Equal_equal;
    Hash_hash;
    Ordered_compare;
    Default_default;
    Serialize_serialize;
    Deserialize_deserialize;
  ]

let is_derivable (trait : Path.t) =
  List.exists
    (fun method_ -> Well_known.is (Well_known.locate_method method_).owner trait)
    derived_methods
