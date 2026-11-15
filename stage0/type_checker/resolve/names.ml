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
  file : Path.file;
  path : Path.t;
  ordinal : int;
  index : int;
  container : int option;
  kind : kind;
  visibility : visibility;
  generic : bool;
}

type key = { module_ : Path.module_; path : Path.t; ordinal : int }

let key_of (declaration : declaration) =
  { module_ = declaration.file.module_; path = declaration.path; ordinal = declaration.ordinal }

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

let packages database (module_ : Path.module_) =
  List.sort_uniq compare
    (module_.package :: Path.standard_package
    :: Query.demand database Packages.dependency_names module_.package)

let full_module database ~(from : Path.module_) (names : string list) : Path.module_ =
  let known = packages database from in
  let is_package (package : Path.package) = package.owner = None || List.mem package known in
  match Path.split_module ~is_package names with
  | Some module_ -> module_
  | None -> { package = { owner = None; name = "" }; modules = [] }

let used_module database ~from (path : path) =
  full_module database ~from
    (List.map (fun (name : name) -> name.text) path.modules @ [ path.last.text ])

let last_name (module_ : Path.module_) =
  match List.rev (Path.module_parts module_) with last :: _ -> last | [] -> ""

let imports =
  Query.query ~name:"imports" ~phase:Phases.syntax ~saved:true ~show:Path.show_file
    (fun database (file : Path.file) ->
      List.map
        (fun (item : path Syntax.item) ->
          let used = used_module database ~from:file.module_ item.value in
          (last_name used, used))
        (Query.demand database Parsed.file file).uses)

let module_exists database (module_ : Path.module_) =
  module_ = Intrinsic.module_ || Query.demand database Packages.module_exists module_

let top module_ name : Path.t = Top { module_; name }

type entry = { name : string; kind : named; visibility : visibility; generic : bool }

let named_of_intended : intended_kind -> named = function
  | Intended_function -> Function
  | Intended_constant -> Constant
  | Intended_type -> Type
  | Intended_trait -> Trait
  | Intended_capability -> Capability
  | Intended_theorem -> Theorem

let plain_items (definitions : definition Syntax.item list) =
  List.concat_map
    (fun (item : definition Syntax.item) ->
      let definition = item.value in
      let plain name kind generic =
        [ { name; kind; visibility = definition.visibility; generic } ]
      in
      match definition.kind with
      | _ when Option.is_some item.container_index -> []
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
    definitions

let builtin_items () =
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

let file_entries =
  Query.query ~name:"file_entries" ~phase:Phases.syntax ~show:Path.show_file (fun database file ->
      plain_items (Query.demand database Parsed.file file).definitions)

let entries =
  Query.query ~name:"entries" ~phase:Phases.syntax ~show:Path.show_module (fun database module_ ->
      if module_ = Intrinsic.module_ then builtin_items ()
      else
        List.concat_map
          (Query.demand database file_entries)
          (Query.demand database Packages.files module_))

module String_map = Map.Make (String)

let entry_index =
  Query.query ~name:"entry_index" ~phase:Phases.declarations ~show:Path.show_module
    (fun database module_ ->
      List.fold_left
        (fun index (entry : entry) ->
          if String_map.mem entry.name index then index else String_map.add entry.name entry index)
        String_map.empty
        (Query.demand database entries module_))

let find =
  Query.query ~name:"find" ~phase:Phases.declarations ~saved:true
    ~show:(fun ((module_ : Path.module_), name) -> Path.show_module module_ ^ "::" ^ name)
    (fun database (module_, name) ->
      if module_exists database module_ then
        String_map.find_opt name (Query.demand database entry_index module_)
      else None)

let is_type_kind : named -> bool = function
  | Type | Trait | Capability -> true
  | Function | Constant | Theorem -> false

let is_value_kind kind = not (is_type_kind kind)
let is_public = function Public | Public_opaque -> true | Private | Internal -> false

let visible ~(from : Path.module_) (module_ : Path.module_) visibility =
  module_ = from || is_public visibility || (visibility = Internal && module_.package = from.package)

type module_lookup =
  | Found_module of Path.module_ * [ `Import of string | `Package ]
  | Ambiguous_module of Path.module_ * Path.module_
  | No_module of string

let lookup_module database ~(from : Path.file) (names : string list) =
  match names with
  | [] -> No_module ""
  | first :: rest -> (
      let imported =
        Option.map
          (fun (module_ : Path.module_) : Path.module_ ->
            { module_ with modules = module_.modules @ rest })
          (List.assoc_opt first (Query.demand database imports from))
      in
      let package =
        let module_ = full_module database ~from:from.module_ names in
        if List.mem module_.package (packages database from.module_) then Some module_ else None
      in
      let exists module_ = module_exists database module_ in
      match (imported, package) with
      | Some imported, Some package when exists imported && exists package && imported <> package ->
          Ambiguous_module (imported, package)
      | Some imported, _ when exists imported -> Found_module (imported, `Import first)
      | _, Some package when exists package -> Found_module (package, `Package)
      | _ -> No_module (String.concat "::" names))

let head_type database ~(from : Path.file) (path : path) =
  let visible_type module_ name =
    match Query.demand database find (module_, name) with
    | Some item when is_type_kind item.kind && visible ~from:from.module_ module_ item.visibility ->
        Some (top module_ name)
    | _ -> None
  in
  match path.modules with
  | [] -> (
      match visible_type from.module_ path.last.text with
      | Some path -> Some path
      | None -> (
          match Prelude.find_type path.last.text with
          | Some module_ -> visible_type module_ path.last.text
          | None -> None))
  | modules -> (
      match
        lookup_module database ~from (List.map (fun (name : Syntax.name) -> name.text) modules)
      with
      | Found_module (module_, _) -> visible_type module_ path.last.text
      | Ambiguous_module _ | No_module _ -> None)

let owner database ~(from : Path.file) (head : type_head) =
  match head_type database ~from head.path with
  | Some path -> path
  | None -> top from.module_ (spell_path head.path)

let impl_types =
  Query.query ~name:"impl_types" ~phase:Phases.declarations ~saved:true ~show:Path.show_module
    (fun database module_ ->
      List.concat_map
        (fun (file : Path.file) ->
          List.filter_map
            (fun (item : definition Syntax.item) ->
              match item.value.kind with
              | Impl { trait_; type_; _ } ->
                  Some
                    ( head_type database ~from:file type_.path,
                      (Impl { module_; trait = spell_path_type trait_; for_type = spell_head type_ }
                        : Path.t) )
              | _ -> None)
            (Query.demand database Parsed.file file).definitions)
        (Query.demand database Packages.files module_))

let file_declarations =
  Query.query ~name:"file_declarations" ~phase:Phases.declarations ~show:Path.show_file
    (fun database (file : Path.file) ->
      let module_ = file.module_ in
      let containers = Hashtbl.create 8 in
      let declare index (item : definition Syntax.item) path kind generic =
        (match item.value.kind with
        | Trait _ | Impl _ -> Hashtbl.replace containers index (path, false)
        | Capability _ -> Hashtbl.replace containers index (path, true)
        | _ -> ());
        Some
          {
            file;
            path;
            ordinal = 0;
            index;
            container = item.container_index;
            kind;
            visibility = item.value.visibility;
            generic;
          }
      in
      List.filter_map Fun.id
        (List.mapi
           (fun index (item : definition Syntax.item) ->
             let definition = item.value in
             let declare = declare index item in
             match
               (definition.kind, Option.bind item.container_index (Hashtbl.find_opt containers))
             with
             | (Function { signature; _ } | Method_declaration signature), Some (owner, static) ->
                 declare
                   (Method
                      {
                        owner;
                        name = (signature_name signature).text;
                        receiver = (if static then Static else receiver signature.parameters);
                      })
                   Method (signature.generics <> [])
             | ( Definition_error { name = Some (Plain_name name | Member_name (_, name)); _ },
                 Some (owner, _) ) ->
                 declare (Method { owner; name = name.text; receiver = Static }) Method false
             | _, Some _ -> None
             | kind, None -> (
                 match kind with
                 | Function { signature = { name = Plain_name name; generics; _ }; _ } ->
                     declare (top module_ name.text) Function (generics <> [])
                 | Function
                     { signature = { name = Member_name (head, name); generics; parameters; _ }; _ }
                   ->
                     declare
                       (Method
                          {
                            owner = owner database ~from:file head;
                            name = name.text;
                            receiver = receiver parameters;
                          })
                       Method (generics <> [])
                 | Type_definition { name; generics; _ } ->
                     declare (top module_ name.text) Type (generics <> [])
                 | Trait { name; generics; _ } ->
                     declare (top module_ name.text) Trait (generics <> [])
                 | Capability { name; _ } -> declare (top module_ name.text) Capability false
                 | Constant { name = Plain_name name; _ } ->
                     declare (top module_ name.text) Constant false
                 | Constant { name = Member_name (head, name); _ } ->
                     declare
                       (Member_constant { owner = owner database ~from:file head; name = name.text })
                       Member_constant false
                 | Theorem { name; generics; _ } ->
                     declare (top module_ name.text) Theorem (generics <> [])
                 | Impl { trait_; type_; _ } ->
                     declare
                       (Impl
                          { module_; trait = spell_path_type trait_; for_type = spell_head type_ })
                       Impl (type_.generics <> [])
                 | Test { name; _ } ->
                     let text =
                       name.first.value
                       ^ String.concat ""
                           (List.map (fun (_, (text : text)) -> text.value) name.rest)
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
                     declare (top module_ name.text)
                       (kind_of_named (named_of_intended intended))
                       false
                 | Definition_error { name = Some (Member_name (head, name)); intended } ->
                     let owner = owner database ~from:file head in
                     if intended = Some Intended_constant then
                       declare (Member_constant { owner; name = name.text }) Member_constant false
                     else
                       declare (Method { owner; name = name.text; receiver = Static }) Method false
                 | Method_declaration _
                 | Definition_error { name = None; _ }
                 | Definition_error { intended = None; _ } ->
                     None))
           (Query.demand database Parsed.file file).definitions))

let declarations =
  Query.query ~name:"declarations" ~phase:Phases.declarations ~show:Path.show_module ~saved:true
    (fun database module_ ->
      let counts = Hashtbl.create 16 in
      List.concat_map
        (fun file ->
          List.map
            (fun (declaration : declaration) ->
              let ordinal = Option.value ~default:0 (Hashtbl.find_opt counts declaration.path) in
              Hashtbl.replace counts declaration.path (ordinal + 1);
              { declaration with ordinal })
            (Query.demand database file_declarations file))
        (Query.demand database Packages.files module_))

let declarations_in =
  Query.query ~name:"declarations_in" ~phase:Phases.declarations ~show:Path.show_file
    (fun database (file : Path.file) ->
      List.filter
        (fun (declaration : declaration) -> declaration.file = file)
        (Query.demand database declarations file.module_))

module Member_map = Map.Make (struct
  type t = Path.t * string

  let compare (left_owner, left_name) (right_owner, right_name) =
    match Path.compare left_owner right_owner with
    | 0 -> String.compare left_name right_name
    | order -> order
end)

let package_declarations =
  Query.query ~name:"package_declarations" ~phase:Phases.declarations ~show:Path.show_package
    (fun database package ->
      List.concat_map
        (fun module_ -> Query.demand database declarations module_)
        (Query.demand database Packages.modules package))

let member_index =
  Query.query ~name:"member_index" ~phase:Phases.declarations ~show:Path.show_package
    (fun database package ->
      List.fold_left
        (fun index (declaration : declaration) ->
          match declaration.path with
          | (Method { owner; name; _ } | Member_constant { owner; name })
            when declaration.ordinal = 0 ->
              Member_map.update (owner, name)
                (fun keys -> Some (key_of declaration :: Option.value ~default:[] keys))
                index
          | _ -> index)
        Member_map.empty
        (Query.demand database package_declarations package)
      |> Member_map.map List.rev)

let trait_index =
  Query.query ~name:"trait_index" ~phase:Phases.declarations ~show:Path.show_package
    (fun database package ->
      let declared = Query.demand database package_declarations package in
      let traits =
        List.filter_map
          (fun (declaration : declaration) ->
            if declaration.kind = Trait && declaration.ordinal = 0 then
              Some ((declaration.file, declaration.index), declaration.path)
            else None)
          declared
      in
      List.fold_left
        (fun index (declaration : declaration) ->
          match (declaration.path, declaration.container) with
          | Method { name; _ }, Some container -> (
              match List.assoc_opt (declaration.file, container) traits with
              | Some trait ->
                  String_map.update name
                    (fun traits ->
                      let traits = Option.value ~default:[] traits in
                      Some
                        (if List.exists (Path.equal trait) traits then traits
                         else traits @ [ trait ]))
                    index
              | None -> index)
          | _ -> index)
        String_map.empty declared)

let traits_declaring =
  Query.query ~name:"traits_declaring" ~phase:Phases.declarations ~saved:true
    ~show:(fun (package, name) -> Path.show_package package ^ " " ^ name)
    (fun database (package, name) ->
      Option.value ~default:[]
        (String_map.find_opt name (Query.demand database trait_index package)))

let members =
  Query.query ~name:"members" ~phase:Phases.declarations ~saved:true
    ~show:(fun (owner, name) -> Path.show owner ^ "." ^ name)
    (fun database ((owner : Path.t), name) ->
      Option.value ~default:[]
        (Member_map.find_opt (owner, name)
           (Query.demand database member_index (Path.package owner))))

module Declaration_map = Map.Make (struct
  type t = Path.t * int

  let compare (left_path, left_ordinal) (right_path, right_ordinal) =
    match Path.compare left_path right_path with
    | 0 -> Int.compare left_ordinal right_ordinal
    | order -> order
end)

let declaration_index =
  Query.query ~name:"declaration_index" ~phase:Phases.declarations ~show:Path.show_module
    (fun database module_ ->
      List.fold_left
        (fun index (declaration : declaration) ->
          Declaration_map.add (declaration.path, declaration.ordinal) declaration index)
        Declaration_map.empty
        (Query.demand database declarations module_))

let items =
  Query.query ~name:"items" ~phase:Phases.syntax ~show:Path.show_file (fun database file ->
      Array.of_list (Query.demand database Parsed.file file).definitions)

let locate =
  Query.query ~name:"locate" ~phase:Phases.declarations ~show:show_key (fun database key ->
      Declaration_map.find_opt (key.path, key.ordinal)
        (Query.demand database declaration_index key.module_))

let file_of =
  Query.query ~name:"file_of" ~phase:Phases.declarations ~show:show_key (fun database key ->
      Option.map
        (fun (declaration : declaration) -> declaration.file)
        (Query.demand database locate key))

let container =
  Query.query ~name:"container" ~phase:Phases.declarations ~show:show_key (fun database key ->
      match Query.demand database locate key with
      | Some { file; container = Some index; _ } ->
          Option.map key_of
            (List.find_opt
               (fun (declaration : declaration) -> declaration.index = index)
               (Query.demand database declarations_in file))
      | _ -> None)

let contained =
  Query.query ~name:"contained" ~phase:Phases.declarations ~show:show_key (fun database key ->
      match Query.demand database locate key with
      | Some { file; index; _ } ->
          List.filter_map
            (fun (declaration : declaration) ->
              if declaration.container = Some index then Some (key_of declaration) else None)
            (Query.demand database declarations_in file)
      | None -> [])

let definition =
  Query.query ~name:"definition" ~phase:Phases.declarations ~show:show_key ~saved:true
    ~about:(fun key -> Some { path = key.path; part = Some "tree" })
    (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some declaration ->
          Some (Query.demand database items declaration.file).(declaration.index).value)

let law_parameters =
  Query.query ~name:"law_parameters" ~phase:Phases.declarations
    ~show:(fun ((trait : Path.t), law) -> Path.show trait ^ "." ^ law)
    (fun database ((trait : Path.t), law) ->
      match trait with
      | Top { module_; _ } when module_exists database module_ -> (
          let declaration =
            Declaration_map.find_opt (trait, 0) (Query.demand database declaration_index module_)
          in
          match
            Option.bind declaration (fun trait_declaration ->
                Query.demand database definition (key_of trait_declaration))
          with
          | Some { kind = Trait { members; _ }; _ } ->
              List.find_map
                (fun (member : trait_member line) ->
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
          | _ -> None)
      | _ -> None)

let spans =
  Query.query ~name:"spans" ~phase:Phases.declarations ~show:show_key (fun database key ->
      Option.map Syntax_walk.spans (Query.demand database definition key))

let base =
  Query.query ~name:"base" ~phase:Phases.declarations ~show:show_key ~saved:true
    (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some declaration ->
          Some
            ( declaration.file,
              (Query.demand database items declaration.file).(declaration.index).base ))

let per_definition database file of_definition =
  List.concat_map
    (fun declaration ->
      let key = key_of declaration in
      match Query.demand database base key with
      | Some (_, base) ->
          List.map (Diagnostic.map_spans (Syntax.Span.to_source ~base)) (of_definition key)
      | None -> [])
    (Query.demand database declarations_in file)
  |> List.sort (fun (left : _ Diagnostic.diagnostic) (right : _ Diagnostic.diagnostic) ->
      compare (left.span, left.code) (right.span, right.code))

let text =
  Query.query ~name:"text" ~phase:Phases.declarations ~show:show_key (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some declaration ->
          Some (Query.demand database items declaration.file).(declaration.index).text)
