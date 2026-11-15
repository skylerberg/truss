open Syntax

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

let kind_name : kind -> string = function
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
  visibility : visibility;
  generic : bool;
}

type key = { module_ : Path.module_; path : Path.t; ordinal : int }

let key_of (declaration : declaration) =
  { module_ = declaration.module_; path = declaration.path; ordinal = declaration.ordinal }

type place = { file : Path.file; base : int }

let show_key key =
  if key.ordinal = 0 then Path.show key.path
  else Printf.sprintf "%s#%d" (Path.show key.path) key.ordinal

let spell_path = Syntax_print.path

let rec spell_type (type_ : type_expression) =
  match type_.kind with
  | Path_type path -> spell_path_type path
  | Self_type None -> "Self"
  | Self_type (Some name) -> "Self." ^ name.text
  | Associated (base, name) -> base.text ^ "." ^ name.text
  | Any_type path -> "any " ^ spell_path_type path
  | Function_type { inputs; output; _ } ->
      Printf.sprintf "fn(%s)%s"
        (String.concat ", "
           (List.map (fun (input : function_input) -> spell_type input.type_) inputs))
        (match output with Some output -> " -> " ^ spell_type output | None -> "")
  | Type_error -> "?"

and spell_path_type (path : path_type) =
  match path.arguments with
  | [] -> spell_path path.path
  | arguments ->
      Printf.sprintf "%s[%s]" (spell_path path.path)
        (String.concat ", " (List.map spell_argument arguments))

and spell_argument = function
  | Type_argument type_ -> spell_type type_
  | Count (value, _) -> Z.to_string value
  | Count_name name -> name.text
  | Constraint (name, type_) -> name.text ^ " = " ^ spell_type type_

let spell_head (head : type_head) : Path.type_head =
  {
    type_name = spell_path head.path;
    generics =
      List.filter_map
        (fun (generic : generic_parameter) ->
          match generic.kind with
          | Type_parameter (name, _) | Value_parameter (name, _) | Capability_parameter name ->
              Some name.text
          | Generic_error -> None)
        head.generics;
  }

let signature_name (signature : signature) =
  match signature.name with Plain_name name | Member_name (_, name) -> name

let receiver (parameters : parameter list) : Path.receiver =
  match parameters with
  | { kind = Self_parameter None; _ } :: _ -> Read
  | { kind = Self_parameter (Some Mut); _ } :: _ -> Mut
  | { kind = Self_parameter (Some Own); _ } :: _ -> Own
  | _ -> Static

let last_name (module_ : Path.module_) =
  match List.rev (Path.module_parts module_) with last :: _ -> last | [] -> ""

type entry = { name : string; kind : named; visibility : visibility; generic : bool }

module String_map = Map.Make (String)

let is_type_kind : named -> bool = function
  | Type | Trait | Capability -> true
  | Function | Constant | Theorem -> false

let is_value_kind kind = not (is_type_kind kind)
let is_public = function Public | Public_opaque -> true | Private | Internal -> false

let visible ~(from : Path.module_) (module_ : Path.module_) visibility =
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
  declaration : key -> declaration option;
  declarations : Path.module_ -> declaration list;
  declarations_in : Path.file -> declaration list;
  package_declarations : Path.package -> declaration list;
  definition : key -> definition option;
  text : key -> string option;
  spans : key -> Source.Definition_span.t array option;
  place : key -> place option;
  container : key -> key option;
  contained : key -> key list;
  members : Path.t -> string -> key list;
  traits_declaring : Path.package -> string -> Path.t list;
  impls : Path.package -> ((Path.t * Path.t) * Path.t) list;
  impls_of_type : Path.package -> Path.t -> (Path.t * Path.t) list;
  impls_of_trait : Path.package -> Path.t -> Path.t list;
  law_proofs : Path.package -> law_proof_name -> key list;
}

let packages lookups (module_ : Path.module_) =
  List.sort_uniq compare
    (module_.package :: Path.standard_package :: lookups.dependency_names module_.package)

let full_module lookups ~(from : Path.module_) (names : string list) : Path.module_ =
  let known = packages lookups from in
  match Path.split_module ~is_package:(fun package -> List.mem package known) names with
  | Some module_ -> module_
  | None -> (
      match names with
      | name :: modules -> { package = { owner = None; name }; modules }
      | [] -> { package = { owner = None; name = "" }; modules = [] })

let used_module lookups ~from (path : path) =
  full_module lookups ~from
    (List.map (fun (name : name) -> name.text) path.modules @ [ path.last.text ])

let is_visible_module lookups ~from (module_ : Path.module_) =
  module_ = Intrinsic.module_
  || (List.mem module_.package (packages lookups from) && lookups.module_exists module_)

type module_lookup =
  | Found_module of Path.module_ * [ `Import of string | `Package ]
  | Ambiguous_module of Path.module_ * Path.module_
  | No_module of string

let lookup_module lookups ~(from : Path.module_) ~imports (names : string list) =
  match names with
  | [] -> No_module ""
  | first :: rest -> (
      let imported =
        Option.map
          (fun (module_ : Path.module_) : Path.module_ ->
            { module_ with modules = module_.modules @ rest })
          (List.assoc_opt first imports)
      in
      let package = Some (full_module lookups ~from names) in
      let exists module_ = is_visible_module lookups ~from module_ in
      match (imported, package) with
      | Some imported, Some package when exists imported && exists package && imported <> package ->
          Ambiguous_module (imported, package)
      | Some imported, _ when exists imported -> Found_module (imported, `Import first)
      | _, Some package when exists package -> Found_module (package, `Package)
      | _ -> No_module (String.concat "::" names))

let top module_ name : Path.t = Top { module_; name }

let definition_of_path lookups path =
  match lookups.key path with
  | Some key -> Option.map (fun tree -> (key, tree)) (lookups.definition key)
  | None -> None

let law_parameters lookups (trait : Path.t) law =
  match definition_of_path lookups trait with
  | Some (_, { kind = Trait { members; _ }; _ }) ->
      List.find_map
        (fun (member : trait_member node) ->
          match member.kind with
          | Law written_law when written_law.name.text = law ->
              Some
                (List.filter_map
                   (fun (parameter : parameter) ->
                     match parameter.kind with
                     | Named_parameter { name; _ } -> Some name.text
                     | Self_parameter _ | Parameter_error -> None)
                   written_law.parameters)
          | _ -> None)
        members
  | _ -> None

type generic_kind = Type_kind | Value_kind | Capability_kind

let generic_kinds (generics : generic_parameter list) =
  List.filter_map
    (fun (generic : generic_parameter) ->
      match generic.kind with
      | Type_parameter (name, _) -> Some (name.text, Type_kind)
      | Value_parameter (name, _) -> Some (name.text, Value_kind)
      | Capability_parameter name -> Some (name.text, Capability_kind)
      | Generic_error -> None)
    generics

let generics_of lookups (path : Path.t) =
  match Intrinsic.builtin_of_path path with
  | Some Array -> Some [ ("Element", Type_kind); ("count", Value_kind) ]
  | Some (Storage | View) -> Some [ ("Element", Type_kind) ]
  | Some Shared -> Some [ ("Value", Type_kind) ]
  | Some _ -> Some []
  | None -> (
      match definition_of_path lookups path with
      | Some (_, definition) -> (
          if Parts.broken definition Header then None
          else
            match definition.kind with
            | Type_definition { generics; _ } | Trait { generics; _ } ->
                Some (generic_kinds generics)
            | Capability _ -> Some []
            | _ -> None)
      | None -> None)

let kind_of lookups (path : Path.t) =
  match path with
  | Top { module_; name } ->
      Option.map (fun (entry : entry) -> entry.kind) (lookups.find module_ name)
  | _ -> None

let named_of_intended : intended_kind -> named = function
  | Intended_function -> Function
  | Intended_constant -> Constant
  | Intended_type -> Type
  | Intended_trait -> Trait
  | Intended_capability -> Capability
  | Intended_theorem -> Theorem

let file_entries (top_levels : Syntax.top_level list) =
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
        name = Intrinsic.builtin_name builtin;
        kind = Type;
        visibility = Public;
        generic = (match builtin with Array | Storage | View | Shared -> true | _ -> false);
      })
    Intrinsic.builtins
  @ List.map
      (fun operation ->
        {
          name = Intrinsic.operation_name operation;
          kind = Function;
          visibility = Public;
          generic = true;
        })
      Intrinsic.operations

let head_type lookups ~(from : Path.module_) ~imports (path : path) =
  let visible_type module_ name =
    match lookups.find module_ name with
    | Some item when is_type_kind item.kind && visible ~from module_ item.visibility ->
        Some (item.kind, top module_ name)
    | _ -> None
  in
  match path.modules with
  | [] -> (
      match visible_type from path.last.text with
      | Some found -> Some found
      | None -> (
          match Prelude.find_type path.last.text with
          | Some module_ -> visible_type module_ path.last.text
          | None -> None))
  | modules -> (
      match
        lookup_module lookups ~from ~imports
          (List.map (fun (name : Syntax.name) -> name.text) modules)
      with
      | Found_module (module_, _) -> visible_type module_ path.last.text
      | Ambiguous_module _ | No_module _ -> None)

let owner lookups ~(from : Path.module_) ~imports (head : type_head) =
  match head_type lookups ~from ~imports head.path with
  | Some (_, path) -> path
  | None -> top from (spell_path head.path)

type written = {
  declaration : declaration;
  file : Path.file;
  index : int;
  container : int option;
  item : definition Syntax.item;
  text : string;
}

let file_declarations lookups (file : Path.file) ~imports ~text (top_levels : Syntax.top_level list)
    =
  let module_ = file.module_ in
  let owner = owner lookups ~from:module_ ~imports in
  let written index ?container (item : definition Syntax.item) path kind generic =
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
  let method_declaration index ~container ~owner:(owner, static) (item : definition Syntax.item) =
    let declare = written index ~container item in
    match item.value.kind with
    | Function { signature; _ } | Method_declaration signature ->
        declare
          (Method
             {
               owner;
               name = (signature_name signature).text;
               receiver = (if static then Static else receiver signature.parameters);
             })
          Method (signature.generics <> [])
    | Definition_error { name = Some (Plain_name name | Member_name (_, name)); _ } ->
        declare (Method { owner; name = name.text; receiver = Static }) Method false
    | _ -> None
  in
  let top_level_declaration index (item : definition Syntax.item) =
    let declare = written index item in
    match item.value.kind with
    | Function { signature = { name = Plain_name name; generics; _ }; _ } ->
        declare (top module_ name.text) Function (generics <> [])
    | Function { signature = { name = Member_name (head, name); generics; parameters; _ }; _ } ->
        declare
          (Method { owner = owner head; name = name.text; receiver = receiver parameters })
          Method (generics <> [])
    | Type_definition { name; generics; _ } -> declare (top module_ name.text) Type (generics <> [])
    | Trait { name; generics; _ } -> declare (top module_ name.text) Trait (generics <> [])
    | Capability { name; _ } -> declare (top module_ name.text) Capability false
    | Constant { name = Plain_name name; _ } -> declare (top module_ name.text) Constant false
    | Constant { name = Member_name (head, name); _ } ->
        declare (Member_constant { owner = owner head; name = name.text }) Member_constant false
    | Theorem { name; generics; _ } -> declare (top module_ name.text) Theorem (generics <> [])
    | Impl { trait_; type_; _ } ->
        declare
          (Impl { module_; trait = spell_path_type trait_; for_type = spell_head type_ })
          Impl (type_.generics <> [])
    | Test { name; _ } ->
        let text =
          name.first.value
          ^ String.concat "" (List.map (fun (_, (text : text)) -> text.value) name.rest)
        in
        declare (Test { module_; name = text }) Test false
    | Law_proof { trait_; law; type_; _ } ->
        declare
          (Law_proof
             {
               module_;
               trait = spell_path_type trait_;
               law = law.text;
               for_type = spell_head type_;
             })
          Law_proof false
    | Definition_error { name = Some (Plain_name name); intended = Some intended } ->
        declare (top module_ name.text) (kind_of_named (named_of_intended intended)) false
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
  item : definition Syntax.item;
  text : string;
  place : place;
  imports : (string * Path.module_) list;
  spans : Source.Definition_span.t array;
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

let module_names entries =
  {
    entries;
    index =
      List.fold_left
        (fun index (entry : entry) ->
          if String_map.mem entry.name index then index else String_map.add entry.name entry index)
        String_map.empty entries;
    module_declarations = [];
  }

let numbered (written : written list) =
  let counts = Hashtbl.create 16 in
  List.map
    (fun (written : written) ->
      let path = written.declaration.path in
      let ordinal = Option.value ~default:0 (Hashtbl.find_opt counts path) in
      Hashtbl.replace counts path (ordinal + 1);
      { written with declaration = { written.declaration with ordinal } })
    written

let derivable (trait : Path.t) =
  match Well_known.of_path trait with
  | Some (Equal | Hash | Ordered | Default | Serialize | Deserialize) -> true
  | _ -> false

let resolved_head lookups ~from ~imports (path : path) ~(kinds : named list) =
  match head_type lookups ~from ~imports path with
  | Some (kind, path) when List.mem kind kinds -> (
      match Intrinsic.builtin_of_path path with Some (Never | Integer) -> None | _ -> Some path)
  | _ -> None

let impl_entries lookups ~imports (declaration : declaration) (definition : definition) =
  let resolved_head = resolved_head lookups ~from:declaration.module_ ~imports in
  match definition.kind with
  | Impl { trait_; type_; _ } -> (
      match
        ( resolved_head trait_.path ~kinds:[ Trait; Capability ],
          resolved_head type_.path ~kinds:[ Type ] )
      with
      | Some trait, Some type_ -> [ ((trait, type_), declaration.path) ]
      | _ -> [])
  | Type_definition { clauses; _ } ->
      List.concat_map
        (fun (clause : type_clause) ->
          match clause.kind with
          | Derives traits ->
              List.filter_map
                (fun (trait : path_type) ->
                  match resolved_head trait.path ~kinds:[ Trait ] with
                  | Some trait when derivable trait ->
                      Some
                        ( (trait, declaration.path),
                          (Derived { type_ = declaration.path; trait } : Path.t) )
                  | _ -> None)
                traits
          | Type_invariant _ | Potential _ -> [])
        clauses
  | _ -> []

let law_proof_entry lookups ~imports (declaration : declaration) (definition : definition) =
  let resolved_head = resolved_head lookups ~from:declaration.module_ ~imports in
  match definition.kind with
  | Law_proof { trait_; law; type_; _ } -> (
      match
        (resolved_head trait_.path ~kinds:[ Trait ], resolved_head type_.path ~kinds:[ Type ])
      with
      | Some trait, Some type_head -> Some { trait; law = law.text; type_head }
      | _ -> None)
  | _ -> None

let namespace lookups package
    (modules : (Path.module_ * (Path.file * Syntax.file * string) list) list) =
  let modules_map =
    List.fold_left
      (fun map (module_, files) ->
        Module_map.add module_
          (module_names
             (List.concat_map
                (fun (_, (file : Syntax.file), _) -> file_entries file.definitions)
                files))
          map)
      (if Intrinsic.module_.package = package then
         Module_map.singleton Intrinsic.module_ (module_names builtin_entries)
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
  let imports_of (file : Path.file) (uses : path Syntax.item list) =
    List.map
      (fun (item : path Syntax.item) ->
        let used = used_module lookups ~from:file.module_ item.value in
        (last_name used, used))
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
          numbered
            (List.concat_map
               (fun ((file : Path.file), (parsed : Syntax.file), text) ->
                 file_declarations pass_lookups file ~imports:(file_imports file) ~text
                   parsed.definitions)
               files) ))
      modules
  in
  let written = List.concat_map snd module_declarations in
  let by_key declarations =
    List.sort
      (fun (left : declaration) (right : declaration) -> compare_key (key_of left) (key_of right))
      (List.map (fun (written : written) -> written.declaration) declarations)
  in
  let declarations = by_key written in
  let by_file = Hashtbl.create 16 in
  List.iter
    (fun (written : written) ->
      Hashtbl.replace by_file written.file
        (written :: Option.value ~default:[] (Hashtbl.find_opt by_file written.file)))
    written;
  let in_file file = List.rev (Option.value ~default:[] (Hashtbl.find_opt by_file file)) in
  let key_of_written (written : written) = key_of written.declaration in
  let at_index = Hashtbl.create 64 and in_container = Hashtbl.create 64 in
  List.iter
    (fun (written : written) ->
      Hashtbl.replace at_index (written.file, written.index) written;
      Option.iter
        (fun container -> Hashtbl.add in_container (written.file, container) written)
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
            spans = Syntax_walk.spans written.item.value;
            container =
              Option.map key_of_written
                (Option.bind written.container (fun index ->
                     Hashtbl.find_opt at_index (written.file, index)));
            contained =
              List.rev_map key_of_written
                (Hashtbl.find_all in_container (written.file, written.index));
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
                 (fun keys -> Some (key_of declaration :: Option.value ~default:[] keys))
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
        impl_entries pass_lookups ~imports:(file_imports written.file) written.declaration
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
             match
               law_proof_entry pass_lookups ~imports:(file_imports written.file) written.declaration
                 written.item.value
             with
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
let pairs merge before after = merge (fun _ before after -> Some (before, after)) before after

let changes before after =
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
            (pairs String_map.merge (entries_of before) (entries_of after))
            []
        @ changes)
      (pairs Module_map.merge before.modules after.modules)
      []
  in
  let files =
    File_map.fold
      (fun file (before, after) changes ->
        if differs before after then File_declarations file :: changes else changes)
      (pairs File_map.merge before.files after.files)
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
              @ (if not (differs before.item.value after.item.value) then []
                 else if
                   differs
                     (Syntax_walk.without_positions before.item.value)
                     (Syntax_walk.without_positions after.item.value)
                 then [ Tree key ]
                 else [ Positions key ])
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
      (pairs Key_map.merge before.declared after.declared)
      []
  in
  let members =
    Member_map.fold
      (fun (owner, name) (before, after) changes ->
        if differs before after then Members (owner, name) :: changes else changes)
      (pairs Member_map.merge before.members after.members)
      []
  in
  let traits =
    String_map.fold
      (fun name (before, after) changes ->
        if differs before after then Traits_declaring name :: changes else changes)
      (pairs String_map.merge before.traits after.traits)
      []
  in
  let law_proofs =
    Law_proof_map.fold
      (fun name (before, after) changes ->
        if differs before after then Law_proofs name :: changes else changes)
      (pairs Law_proof_map.merge before.law_proofs after.law_proofs)
      []
  in
  let impls change select =
    Path.Map.fold
      (fun path (before, after) changes ->
        if differs before after then change path :: changes else changes)
      (pairs Path.Map.merge (select before.impls) (select after.impls))
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
  let members owner name =
    Option.value ~default:[]
      (Member_map.find_opt (owner, name) (namespace (Path.package owner)).members)
  in
  {
    find =
      (fun module_ name ->
        Option.bind (of_module module_) (fun names -> String_map.find_opt name names.index));
    entries =
      (fun module_ -> match of_module module_ with Some names -> names.entries | None -> []);
    imports = (fun key -> match declared key with Some declared -> declared.imports | None -> []);
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
                (fun declared -> key_of declared.declaration)
                (declared { module_; path; ordinal = 0 })
        | Method { owner; name; _ } | Member_constant { owner; name } ->
            List.find_opt (fun (key : key) -> Path.equal key.path path) (members owner name)
        | Derived _ -> None);
    declaration = (fun key -> Option.map (fun declared -> declared.declaration) (declared key));
    declarations =
      (fun module_ ->
        match of_module module_ with Some names -> names.module_declarations | None -> []);
    declarations_in = (fun file -> Option.value ~default:[] (of_file file));
    package_declarations = (fun package -> (namespace package).declarations);
    definition = (fun key -> Option.map (fun declared -> declared.item.value) (declared key));
    text = (fun key -> Option.map (fun (declared : declared) -> declared.text) (declared key));
    spans = (fun key -> Option.map (fun declared -> declared.spans) (declared key));
    place = (fun key -> Option.map (fun declared -> declared.place) (declared key));
    container = (fun key -> Option.bind (declared key) (fun declared -> declared.container));
    contained =
      (fun key -> match declared key with Some declared -> declared.contained | None -> []);
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
