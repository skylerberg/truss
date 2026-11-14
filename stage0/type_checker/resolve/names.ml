(* The declarations of each module, and looking a definition up by name. A
   module is a directory, and its files share one namespace. Every lookup
   across definitions is a query keyed by location and name, so a change
   re-runs only the lookups that it can affect: adding a definition named
   [count] to a file re-runs the lookups of [count] in its module. *)

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

(* The kinds of definition that a name can resolve to: every kind that has a
   name of its own, which excludes a method, a member constant, an [impl], a
   test, and a law's proof. *)
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

(* A definition, as its file declares it. [ordinal] counts the earlier
   definitions in the module with the same path, in the order of its files.
   Only the first, with ordinal 0, is the referent of the path; the others
   are reported as duplicates. [index] is its position among its file's
   definitions, which no other file's edit changes. [container] is the
   position of the enclosing trait, [impl], or capability, when the
   definition is a method of one. *)
type declaration = {
  file : Path.file;  (** Where it is written. *)
  path : Path.t;
  ordinal : int;
  index : int;
  container : int option;
  kind : kind;
  visibility : visibility;
  generic : bool;
}

(* The key of a definition: its path, its module, and its ordinal. The path
   alone does not determine the module of a method, because a method can be
   in any module of its type's package. The key does not name the file, so
   moving a definition to another file of its module keeps its key. *)
type key = { module_ : Path.module_; path : Path.t; ordinal : int }

let key_of (declaration : declaration) =
  { module_ = declaration.file.module_; path = declaration.path; ordinal = declaration.ordinal }

let show_key key =
  if key.ordinal = 0 then Path.show key.path
  else Printf.sprintf "%s#%d" (Path.show key.path) key.ordinal

(* Spelling types as written, for naming [impl]s and law proofs. *)
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
        (String.concat ", " (List.map (fun (_, input) -> spell_type input) inputs))
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

(* A function's own name, which comes after the type head when it is
   written on a type. *)
let signature_name (signature : signature) =
  match signature.name with Plain_name name | Member_name (_, name) -> name

let receiver (parameters : parameter list) : Path.receiver =
  match parameters with
  | { kind = Self_parameter None; _ } :: _ -> Read
  | { kind = Self_parameter (Some Mut); _ } :: _ -> Mut
  | { kind = Self_parameter (Some Own); _ } :: _ -> Own
  | _ -> Static

(* The packages a module can name at the start of a path: its own, the
   standard library, and its dependencies. *)
let packages database (module_ : Path.module_) =
  let dependencies =
    List.map
      (fun (dependency : Manifest.dependency) -> dependency.package)
      (Query.demand database Packages.dependencies module_.package)
  in
  List.sort_uniq compare (module_.package :: Path.standard_package :: dependencies)

(* The module that a full path denotes, written in a file of [from]. The
   path starts with a package's name, which takes two segments when the
   package has an owner, followed by the module's segments.
   [standard::file_system] is the package [standard] and the module
   [file_system], and [acme::geometry::vector] is the package
   [acme::geometry] and the module [vector]. *)
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

(* The modules a file imports, by the name code writes them with. Each file
   has its own imports. *)
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

(* The plain names a file defines, before any type head is resolved, so
   that resolving a method's head can read them. An entry carries nothing
   about where its definition is, so that moving a definition within its
   module changes no lookup of it. *)
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
      (* A method written inside a trait, an [impl], or a capability is
         reached through that one, not by its name. *)
      | _ when Option.is_some item.container -> []
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

(* A module's entries, file by file. An edit to a body leaves its file's
   entries as they were, so it reaches no lookup. *)
let entries =
  Query.query ~name:"entries" ~phase:Phases.syntax ~show:Path.show_module (fun database module_ ->
      if module_ = Intrinsic.module_ then builtin_items ()
      else
        List.concat_map
          (Query.demand database file_entries)
          (Query.demand database Packages.files module_))

module String_map = Map.Make (String)

(* A module's entries by name, the first of each name, so that each lookup
   by name is a logarithmic one rather than a pass over the module. *)
let entry_index =
  Query.query ~name:"entry_index" ~phase:Phases.declarations ~show:Path.show_module
    (fun database module_ ->
      List.fold_left
        (fun index (entry : entry) ->
          if String_map.mem entry.name index then index else String_map.add entry.name entry index)
        String_map.empty
        (Query.demand database entries module_))

(* The first definition with that name in the module. *)
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

(* Whether code in [from] can see a definition of [module_] with this
   visibility. A private definition is visible to every file of its module. *)
let visible ~(from : Path.module_) (module_ : Path.module_) visibility =
  module_ = from || is_public visibility || (visibility = Internal && module_.package = from.package)

type module_lookup =
  | Found_module of Path.module_ * [ `Import of string | `Package ]
  | Ambiguous_module of Path.module_ * Path.module_
  | No_module of string

(* The module that the segments before [::] denote, from the file [from]:
   the first segment is the last name of a module that the file imports, or
   a package. *)
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

(* The type a method's or constant's head names, from the file it is
   written in, or [None]. *)
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

(* A head that names no type still gets a path, so the definition is
   checked and its error reported once; no other code can name it, since a
   real type of that name in this module would have been found. *)
let owner database ~(from : Path.file) (head : type_head) =
  match head_type database ~from head.path with
  | Some path -> path
  | None -> top from.module_ (spell_path head.path)

(* Each [impl] of a module, with the type its head names, from the head as
   written: what an [impl]'s interface resolves its type to, read without
   lowering the interface. *)
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

(* A file's declarations, each with ordinal 0; [declarations] numbers them
   across the module. *)
let file_declarations =
  Query.query ~name:"file_declarations" ~phase:Phases.declarations ~show:Path.show_file
    (fun database (file : Path.file) ->
      let module_ = file.module_ in
      (* The traits, [impl]s, and capabilities so far, by index: the path of
         each, and whether its methods take no [self], as a capability's do
         not. *)
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
            container = item.container;
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
             match (definition.kind, Option.bind item.container (Hashtbl.find_opt containers)) with
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
                 (* A method without a body is written only inside a trait or a
                capability. *)
                 | Method_declaration _
                 | Definition_error { name = None; _ }
                 | Definition_error { intended = None; _ } ->
                     None))
           (Query.demand database Parsed.file file).definitions))

(* A module's declarations, file by file, each numbered among the earlier
   ones with its path. *)
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

(* The declarations written in one file, numbered as [declarations]
   numbers them. *)
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

(* All declarations of a package, module by module. Each index of the
   package is built from this list in one pass. *)
let package_declarations =
  Query.query ~name:"package_declarations" ~phase:Phases.declarations ~show:Path.show_package
    (fun database package ->
      List.concat_map
        (fun module_ -> Query.demand database declarations module_)
        (Query.demand database Packages.modules package))

(* A package's methods and member constants by owner and name. *)
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

(* A package's traits by the names of the methods written inside them, in
   the order they are declared. A method written inside a trait is declared
   as that trait's, so this reads no trait's interface. *)
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

(* The methods and constants written under a type, with one name, from
   every file of the type's package, where they must be. Their keys carry
   nothing about where in a file they are, so moving one changes nothing
   that looked it up. *)
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

(* A module's declarations by path and ordinal. *)
let declaration_index =
  Query.query ~name:"declaration_index" ~phase:Phases.declarations ~show:Path.show_module
    (fun database module_ ->
      List.fold_left
        (fun index (declaration : declaration) ->
          Declaration_map.add (declaration.path, declaration.ordinal) declaration index)
        Declaration_map.empty
        (Query.demand database declarations module_))

(* A file's definitions, by their index in the file. *)
let items =
  Query.query ~name:"items" ~phase:Phases.syntax ~show:Path.show_file (fun database file ->
      Array.of_list (Query.demand database Parsed.file file).definitions)

(* Where a definition is: its declaration, which names its file and its
   place in it. *)
let locate =
  Query.query ~name:"locate" ~phase:Phases.declarations ~show:show_key (fun database key ->
      Declaration_map.find_opt (key.path, key.ordinal)
        (Query.demand database declaration_index key.module_))

(* The file a definition is written in. A definition that moves within its
   file keeps it, so reading it depends on nothing about the position. *)
let file_of =
  Query.query ~name:"file_of" ~phase:Phases.declarations ~show:show_key (fun database key ->
      Option.map
        (fun (declaration : declaration) -> declaration.file)
        (Query.demand database locate key))

(* The trait, the [impl], or the capability a method is written inside. *)
let container =
  Query.query ~name:"container" ~phase:Phases.declarations ~show:show_key (fun database key ->
      match Query.demand database locate key with
      | Some { file; container = Some index; _ } ->
          Option.map key_of
            (List.find_opt
               (fun (declaration : declaration) -> declaration.index = index)
               (Query.demand database declarations_in file))
      | _ -> None)

(* The methods written inside a trait, an [impl], or a capability, in the
   order they are written. *)
let contained =
  Query.query ~name:"contained" ~phase:Phases.declarations ~show:show_key (fun database key ->
      match Query.demand database locate key with
      | Some { file; index; _ } ->
          List.filter_map
            (fun (declaration : declaration) ->
              if declaration.container = Some index then Some (key_of declaration) else None)
            (Query.demand database declarations_in file)
      | None -> [])

(* A definition's tree, with positions relative to the definition. A
   definition that only moved then has the same tree, and invalidates no
   result that reads it. *)
let definition =
  Query.query ~name:"definition" ~phase:Phases.declarations ~show:show_key ~saved:true
    ~about:(fun key -> Some { path = key.path; part = Some "tree" })
    (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some declaration ->
          Some (Query.demand database items declaration.file).(declaration.index).value)

(* The names of the parameters of a trait's law, in order. The body of a
   proof of the law names them. *)
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

(* The span of each node of a definition, relative to the definition, by
   node id. The core form holds no positions, so reformatting a definition
   invalidates no result that reads its form. Code that displays a node's
   source text demands this query. *)
let spans =
  Query.query ~name:"spans" ~phase:Phases.declarations ~show:show_key (fun database key ->
      Option.map Syntax_walk.spans (Query.demand database definition key))

(* The file a definition is written in, and where it starts in it, for
   showing its diagnostics. *)
let base =
  Query.query ~name:"base" ~phase:Phases.declarations ~show:show_key ~saved:true
    (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some declaration ->
          Some
            ( declaration.file,
              (Query.demand database items declaration.file).(declaration.index).base ))

(* A stage's diagnostics for a file, in order. [of_definition] returns the
   diagnostics of each definition in the definition's own offsets, and this
   converts them to the file's offsets. *)
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
