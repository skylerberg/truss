(* What each file defines, and finding a definition by name. See
   TYPECHECKER.md, "Name resolution" and "Traces".

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

let kind_name = function
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
  path : Path.t;
  ordinal : int;
  index : int;
  kind : kind;
  visibility : visibility;
  generic : bool;
}

type key = { path : Path.t; ordinal : int }

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

let receiver (parameters : parameter list) : Path.receiver =
  match parameters with
  | { kind = Self_parameter None; _ } :: _ -> Read
  | { kind = Self_parameter (Some Mut); _ } :: _ -> Mut
  | { kind = Self_parameter (Some Own); _ } :: _ -> Own
  | _ -> Static

(* Imports *)

(* The module a [use] line names: [use standard::file_system] is the
   package [standard] and the module [file_system]. *)
let used_module (path : path) : Path.module_ =
  match path.modules with
  | [] -> { package = path.last.text; modules = [] }
  | package :: rest ->
      {
        package = package.text;
        modules = List.map (fun (name : name) -> name.text) rest @ [ path.last.text ];
      }

let last_name (module_ : Path.module_) =
  match List.rev module_.modules with last :: _ -> last | [] -> module_.package

(* The modules a file imports, by the name code writes them with. *)
let imports =
  Query.query ~name:"imports" ~show:Path.show_module (fun database module_ ->
      let file = Query.demand database Workspace.file module_ in
      List.map
        (fun (item : path Syntax.item) ->
          let used = used_module item.value in
          (last_name used, used))
        file.uses)

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

let module_exists database (module_ : Path.module_) =
  module_ = Intrinsic.module_ || Query.demand database Workspace.module_exists module_

(* Declarations *)

let top module_ name : Path.t = Top { module_; name }

(* The plain names a file defines, before any type head is resolved, so
   that resolving a method's head can read them. *)
type entry = { name : string; kind : kind; visibility : visibility; generic : bool; index : int }

let plain_items (definitions : definition Syntax.item list) =
  List.concat
    (List.mapi
       (fun index (item : definition Syntax.item) ->
         let definition = item.value in
         let plain name kind generic =
           [ { name; kind; visibility = definition.visibility; generic; index } ]
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
             match keyword with
             | Some Fn -> plain name.text Function false
             | Some Type -> plain name.text Type false
             | Some Trait -> plain name.text Trait false
             | Some Capability -> plain name.text Capability false
             | Some Let -> plain name.text Constant false
             | Some Theorem -> plain name.text Theorem false
             | _ -> [])
         | Function _ | Constant _ | Impl _ | Test _ | Law_proof _ | Definition_error _ -> [])
       definitions)

let builtin_items () =
  List.map
    (fun builtin ->
      {
        name = Intrinsic.builtin_name builtin;
        kind = Type;
        visibility = Public;
        generic = builtin = Intrinsic.Array;
        index = -1;
      })
    Intrinsic.builtins

let entries =
  Query.query ~name:"entries" ~show:Path.show_module (fun database module_ ->
      if module_ = Intrinsic.module_ then builtin_items ()
      else plain_items (Query.demand database Workspace.file module_).definitions)

(* The first definition with that name in the module. *)
let find =
  Query.query ~name:"find"
    ~show:(fun ((module_ : Path.module_), name) -> Path.show_module module_ ^ "::" ^ name)
    (fun database (module_, name) ->
      if module_exists database module_ then
        List.find_opt
          (fun (entry : entry) -> entry.name = name)
          (Query.demand database entries module_)
      else None)

let is_type_kind = function Type | Trait | Capability -> true | _ -> false
let is_value_kind = function Function | Constant | Theorem -> true | _ -> false

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
        if List.mem first (packages database from) then
          Some ({ package = first; modules = rest } : Path.module_)
        else None
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
  Query.query ~name:"declarations" ~show:Path.show_module (fun database module_ ->
      let file = Query.demand database Workspace.file module_ in
      let counts = Hashtbl.create 16 in
      let declare index (definition : definition) path kind generic =
        let ordinal = Option.value ~default:0 (Hashtbl.find_opt counts path) in
        Hashtbl.replace counts path (ordinal + 1);
        Some { path; ordinal; index; kind; visibility = definition.visibility; generic }
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
                 let kind =
                   match keyword with
                   | Some Fn -> Some Function
                   | Some Type -> Some Type
                   | Some Trait -> Some Trait
                   | Some Capability -> Some Capability
                   | Some Let -> Some Constant
                   | Some Theorem -> Some Theorem
                   | _ -> None
                 in
                 match kind with
                 | Some kind -> declare (top module_ name.text) kind false
                 | None -> None)
             | Definition_error { name = Some (Member_name (head, name)); keyword } ->
                 let owner = owner database ~from:module_ head in
                 if keyword = Some Let then
                   declare (Member_constant { owner; name = name.text }) Member_constant false
                 else declare (Method { owner; name = name.text; receiver = Static }) Method false
             | Definition_error { name = None; _ } -> None)
           file.definitions))

(* The methods and constants written under a type, with one name, from
   every file of the type's package, where they must be. *)
let members =
  Query.query ~name:"members"
    ~show:(fun (owner, name) -> Path.show owner ^ "." ^ name)
    (fun database ((owner : Path.t), name) ->
      let package = (Path.module_of owner).package in
      match Workspace.package database package with
      | None -> []
      | Some package ->
          List.concat_map
            (fun module_ ->
              List.filter
                (fun (declaration : declaration) ->
                  declaration.ordinal = 0
                  &&
                  match declaration.path with
                  | Method { owner = method_owner; name = method_name; _ }
                  | Member_constant { owner = method_owner; name = method_name } ->
                      Path.equal method_owner owner && method_name = name
                  | _ -> false)
                (Query.demand database declarations module_))
            package.modules)

(* Where a definition is: its module, its declaration, and its place in its
   file. *)
let locate =
  Query.query ~name:"locate" ~show:show_key (fun database key ->
      let module_ = Path.module_of key.path in
      let found =
        List.find_opt
          (fun (declaration : declaration) ->
            Path.equal declaration.path key.path && declaration.ordinal = key.ordinal)
          (Query.demand database declarations module_)
      in
      Option.map (fun declaration -> (module_, declaration)) found)

(* A definition's tree, with positions relative to it, so that a definition
   that only moved gives the same tree and changes nothing that reads it. *)
let definition =
  Query.query ~name:"definition" ~show:show_key (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some (module_, declaration) ->
          let file = Query.demand database Workspace.file module_ in
          Some (List.nth file.definitions declaration.index).value)

(* Where a definition starts in its file, for showing its diagnostics. *)
let base =
  Query.query ~name:"base" ~show:show_key (fun database key ->
      match Query.demand database locate key with
      | None -> None
      | Some (module_, declaration) ->
          let file = Query.demand database Workspace.file module_ in
          Some (module_, (List.nth file.definitions declaration.index).base))
