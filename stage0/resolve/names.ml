(* What each file defines, and finding a definition by name.

   Every lookup across definitions is a query keyed by where and what name,
   so a change re-runs only the lookups it can affect: adding a definition
   named [count] to a file re-runs the lookups of [count] in that file. *)

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

(* What a name can mean: the definitions that have a name of their own, which
   is every kind but a method, a member constant, an [impl], a test, and a
   law's proof. *)
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

(* A definition, as its file declares it. [ordinal] counts the definitions
   before it in the file with the same path, so only the first, with
   ordinal 0, is what the path names; the others are reported as
   duplicates. [index] is its place among the file's definitions. *)
type declaration = {
  module_ : Path.module_;  (** Where it is written. *)
  path : Path.t;
  ordinal : int;
  index : int;
  kind : kind;
  visibility : visibility;
  generic : bool;
}

(* A definition: its path, where it is written, and its ordinal. The path
   alone does not say where a method is written, since a method may be in
   any file of its type's package. *)
type key = { module_ : Path.module_; path : Path.t; ordinal : int }

let key_of (declaration : declaration) =
  { module_ = declaration.module_; path = declaration.path; ordinal = declaration.ordinal }

let show_key key =
  if key.ordinal = 0 then Path.show key.path
  else Printf.sprintf "%s#%d" (Path.show key.path) key.ordinal

(* Spelling types as written, for naming [impl]s and law proofs. *)
let spell_path (path : path) =
  String.concat "::" (List.map (fun (name : name) -> name.text) path.modules @ [ path.last.text ])

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

let spell_head (head : type_head) =
  let generics =
    List.filter_map
      (fun (generic : generic_parameter) ->
        match generic.kind with
        | Type_parameter (name, _) | Value_parameter (name, _) | Capability_parameter name ->
            Some name.text
        | Generic_error -> None)
      head.generics
  in
  match generics with
  | [] -> spell_path head.path
  | _ -> Printf.sprintf "%s[%s]" (spell_path head.path) (String.concat ", " generics)

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

(* Imports *)

(* The packages a file can name at the start of a path: its own, the
   standard library, and its dependencies. *)
let packages database (module_ : Path.module_) =
  let dependencies =
    match Workspace.package database module_.package with
    | Some package ->
        List.map
          (fun (dependency : Workspace.dependency) -> dependency.package)
          package.dependencies
    | None -> []
  in
  List.sort_uniq compare (module_.package :: Prelude.standard :: dependencies)

(* The module a full path's names give, written in a file of [from]: a
   package's name, which is two of them when it has an owner, and then the
   modules'. [standard::file_system] is the package [standard] and the
   module [file_system], and [acme::geometry::vector] is the package
   [acme::geometry] and the module [vector]. *)
let full_module database ~(from : Path.module_) (names : string list) : Path.module_ =
  match names with
  | owner :: name :: rest when List.mem (owner ^ "::" ^ name) (packages database from) ->
      { package = owner ^ "::" ^ name; modules = rest }
  | package :: rest -> { package; modules = rest }
  | [] -> { package = ""; modules = [] }

(* The module a [use] line names. *)
let used_module database ~from (path : path) =
  full_module database ~from
    (List.map (fun (name : name) -> name.text) path.modules @ [ path.last.text ])

let last_name (module_ : Path.module_) =
  match List.rev (Path.module_parts module_) with last :: _ -> last | [] -> ""

(* The modules a file imports, by the name code writes them with. *)
let imports =
  Query.query ~name:"imports" ~phase:Syntax ~saved:true ~show:Path.show_module
    (fun database module_ ->
      let file = Query.demand database Workspace.file module_ in
      List.map
        (fun (item : path Syntax.item) ->
          let used = used_module database ~from:module_ item.value in
          (last_name used, used))
        file.uses)

let module_exists database (module_ : Path.module_) =
  module_ = Intrinsic.module_ || Query.demand database Workspace.module_exists module_

(* Declarations *)

let top module_ name : Path.t = Top { module_; name }

(* The plain names a file defines, before any type head is resolved, so
   that resolving a method's head can read them. *)
(* An entry carries nothing about where in the file its definition is, so
   that moving a definition changes no lookup of it. *)
type entry = { name : string; kind : named; visibility : visibility; generic : bool }

(* What a definition whose header did not parse was meant to be, by the
   keyword it starts with. *)
let named_of_keyword : Token.keyword option -> named option = function
  | Some Fn -> Some Function
  | Some Type -> Some Type
  | Some Trait -> Some Trait
  | Some Capability -> Some Capability
  | Some Let -> Some Constant
  | Some Theorem -> Some Theorem
  | _ -> None

let plain_items (definitions : definition Syntax.item list) =
  List.concat_map
    (fun (item : definition Syntax.item) ->
      let definition = item.value in
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
      | Definition_error { name = Some (Plain_name name); keyword } -> (
          match named_of_keyword keyword with Some kind -> plain name.text kind false | None -> [])
      | Function _ | Constant _ | Impl _ | Test _ | Law_proof _ | Definition_error _ -> [])
    definitions

let builtin_items () =
  List.map
    (fun builtin ->
      {
        name = Intrinsic.builtin_name builtin;
        kind = Type;
        visibility = Public;
        generic = (match builtin with Array | Storage | View -> true | _ -> false);
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

let entries =
  Query.query ~name:"entries" ~phase:Syntax ~show:Path.show_module (fun database module_ ->
      if module_ = Intrinsic.module_ then builtin_items ()
      else plain_items (Query.demand database Workspace.file module_).definitions)

module String_map = Map.Make (String)

(* A module's entries by name, the first of each name, so that each lookup
   by name is a logarithmic one rather than a pass over the module. *)
let entry_index =
  Query.query ~name:"entry_index" ~phase:Declarations ~show:Path.show_module
    (fun database module_ ->
      List.fold_left
        (fun index (entry : entry) ->
          if String_map.mem entry.name index then index else String_map.add entry.name entry index)
        String_map.empty
        (Query.demand database entries module_))

(* The first definition with that name in the module. *)
let find =
  Query.query ~name:"find" ~phase:Declarations ~saved:true
    ~show:(fun ((module_ : Path.module_), name) -> Path.show_module module_ ^ "::" ^ name)
    (fun database (module_, name) ->
      if module_exists database module_ then
        String_map.find_opt name (Query.demand database entry_index module_)
      else None)

let is_type_kind : named -> bool = function
  | Type | Trait | Capability -> true
  | Function | Constant | Theorem -> false

let is_value_kind kind = not (is_type_kind kind)

(* Whether code in [from] can see a definition of [module_] with this
   visibility. *)
let visible ~(from : Path.module_) (module_ : Path.module_) visibility =
  module_ = from
  ||
  match visibility with
  | Private -> false
  | Internal -> module_.package = from.package
  | Public | Public_opaque -> true

type module_lookup =
  | Found_module of Path.module_ * [ `Import of string | `Package ]
  | Ambiguous_module of Path.module_ * Path.module_
  | No_module of string

(* The module that the names before [::] give, from a file in [from]: the
   first name is a module the file imports, by its last name, or a
   package. *)
let lookup_module database ~(from : Path.module_) (names : string list) =
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
        let module_ = full_module database ~from names in
        if List.mem module_.package (packages database from) then Some module_ else None
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
let head_type database ~(from : Path.module_) (path : path) =
  let found module_ name =
    match Query.demand database find (module_, name) with
    | Some item when is_type_kind item.kind && visible ~from module_ item.visibility ->
        Some (top module_ name)
    | _ -> None
  in
  match path.modules with
  | [] -> (
      match found from path.last.text with
      | Some path -> Some path
      | None -> (
          match Prelude.find_type path.last.text with
          | Some module_ -> found module_ path.last.text
          | None -> None))
  | modules -> (
      match
        lookup_module database ~from (List.map (fun (name : Syntax.name) -> name.text) modules)
      with
      | Found_module (module_, _) -> found module_ path.last.text
      | Ambiguous_module _ | No_module _ -> None)

(* A head that names no type still gets a path, so the definition is
   checked and its error reported once; no other code can name it, since a
   real type of that name in this module would have been found. *)
let owner database ~from (head : type_head) =
  match head_type database ~from head.path with
  | Some path -> path
  | None -> top from (spell_path head.path)

let declarations =
  Query.query ~name:"declarations" ~phase:Declarations ~show:Path.show_module ~saved:true
    (fun database module_ ->
      let file = Query.demand database Workspace.file module_ in
      let counts = Hashtbl.create 16 in
      let declare index (definition : definition) path kind generic =
        let ordinal = Option.value ~default:0 (Hashtbl.find_opt counts path) in
        Hashtbl.replace counts path (ordinal + 1);
        Some { module_; path; ordinal; index; kind; visibility = definition.visibility; generic }
      in
      List.filter_map Fun.id
        (List.mapi
           (fun index (item : definition Syntax.item) ->
             let definition = item.value in
             let declare = declare index definition in
             match definition.kind with
             | Function { signature = { name = Plain_name name; generics; _ }; _ } ->
                 declare (top module_ name.text) Function (generics <> [])
             | Function
                 { signature = { name = Member_name (head, name); generics; parameters; _ }; _ } ->
                 declare
                   (Method
                      {
                        owner = owner database ~from:module_ head;
                        name = name.text;
                        receiver = receiver parameters;
                      })
                   Method (generics <> [])
             | Type_definition { name; generics; _ } ->
                 declare (top module_ name.text) Type (generics <> [])
             | Trait { name; generics; _ } -> declare (top module_ name.text) Trait (generics <> [])
             | Capability { name; _ } -> declare (top module_ name.text) Capability false
             | Constant { name = Plain_name name; _ } ->
                 declare (top module_ name.text) Constant false
             | Constant { name = Member_name (head, name); _ } ->
                 declare
                   (Member_constant { owner = owner database ~from:module_ head; name = name.text })
                   Member_constant false
             | Theorem { name; generics; _ } ->
                 declare (top module_ name.text) Theorem (generics <> [])
             | Impl { trait_; type_; _ } ->
                 declare
                   (Impl { module_; name = spell_path_type trait_ ^ " for " ^ spell_head type_ })
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
                        name =
                          Printf.sprintf "%s.%s for %s" (spell_path_type trait_) law.text
                            (spell_type type_);
                      })
                   Law_proof false
             | Definition_error { name = Some (Plain_name name); keyword } -> (
                 match named_of_keyword keyword with
                 | Some kind -> declare (top module_ name.text) (kind_of_named kind) false
                 | None -> None)
             | Definition_error { name = Some (Member_name (head, name)); keyword } ->
                 let owner = owner database ~from:module_ head in
                 if keyword = Some Let then
                   declare (Member_constant { owner; name = name.text }) Member_constant false
                 else declare (Method { owner; name = name.text; receiver = Static }) Method false
             | Definition_error { name = None; _ } -> None)
           file.definitions))

module Member_map = Map.Make (struct
  type t = Path.t * string

  let compare (left_owner, left_name) (right_owner, right_name) =
    match Path.compare left_owner right_owner with
    | 0 -> String.compare left_name right_name
    | order -> order
end)

(* A package's methods and member constants by owner and name, built in one
   pass over its declarations. *)
let member_index =
  Query.query ~name:"member_index" ~phase:Declarations ~show:Fun.id (fun database package_name ->
      match Workspace.package database package_name with
      | None -> Member_map.empty
      | Some package ->
          List.fold_left
            (fun index module_ ->
              List.fold_left
                (fun index (declaration : declaration) ->
                  match declaration.path with
                  | (Method { owner; name; _ } | Member_constant { owner; name })
                    when declaration.ordinal = 0 ->
                      Member_map.update (owner, name)
                        (fun found -> Some (key_of declaration :: Option.value ~default:[] found))
                        index
                  | _ -> index)
                index
                (Query.demand database declarations module_))
            Member_map.empty package.modules
          |> Member_map.map List.rev)

(* The methods and constants written under a type, with one name, from
   every file of the type's package, where they must be. Their keys carry
   nothing about where in a file they are, so moving one changes nothing
   that looked it up. *)
let members =
  Query.query ~name:"members" ~phase:Declarations ~saved:true
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
  Query.query ~name:"declaration_index" ~phase:Declarations ~show:Path.show_module
    (fun database module_ ->
      List.fold_left
        (fun index (declaration : declaration) ->
          Declaration_map.add (declaration.path, declaration.ordinal) declaration index)
        Declaration_map.empty
        (Query.demand database declarations module_))

(* A module's definitions, by their index in the file. *)
let items =
  Query.query ~name:"items" ~phase:Syntax ~show:Path.show_module (fun database module_ ->
      Array.of_list (Query.demand database Workspace.file module_).definitions)

(* Where a definition is: its module, its declaration, and its place in its
   file. *)
let locate =
  Query.query ~name:"locate" ~phase:Declarations ~show:show_key (fun database key ->
      Option.map
        (fun declaration -> (key.module_, declaration))
        (Declaration_map.find_opt (key.path, key.ordinal)
           (Query.demand database declaration_index key.module_)))

(* A definition's tree, with positions relative to it, so that a definition
   that only moved gives the same tree and changes nothing that reads it. *)
let definition =
  Query.query ~name:"definition" ~phase:Declarations ~show:show_key ~saved:true
    ~about:(fun key -> Some { path = key.path; part = Some "tree" })
    (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some (module_, declaration) ->
          Some (Query.demand database items module_).(declaration.index).value)

(* Where a definition starts in its file, for showing its diagnostics. *)
let base =
  Query.query ~name:"base" ~phase:Declarations ~show:show_key ~saved:true (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some (module_, declaration) ->
          Some (module_, (Query.demand database items module_).(declaration.index).base))

(* A stage's diagnostics for a file: each definition's, which [of_definition]
   gives in the definition's own offsets, moved to the file's, in order. *)
let per_definition database module_ of_definition =
  List.concat_map
    (fun declaration ->
      let key = key_of declaration in
      match Query.demand database base key with
      | Some (_, base) -> List.map (Diagnostic.move base) (of_definition key)
      | None -> [])
    (Query.demand database declarations module_)
  |> List.sort (fun (left : Diagnostic.t) (right : Diagnostic.t) ->
      compare (left.span, left.code) (right.span, right.code))

(* A definition's source text, which fixes quote, apart from the rest of
   its file, so that editing another definition changes nothing that reads
   it. *)
let text =
  Query.query ~name:"text" ~phase:Declarations ~show:show_key (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some (module_, declaration) ->
          Some (Query.demand database items module_).(declaration.index).text)
