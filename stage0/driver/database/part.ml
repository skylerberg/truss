type input =
  | Source of Path.file
  | Packages
  | Modules of Path.package
  | Files of Path.package
  | Dependencies of Path.package

type name =
  | Module of Path.module_
  | Entry of Path.module_ * string
  | Entries of Path.module_
  | Imports of Resolve.Names.key
  | Declaration of Resolve.Names.key
  | Tree of Resolve.Names.key
  | Text of Resolve.Names.key
  | Place of Resolve.Names.key
  | Container of Resolve.Names.key
  | Contained of Resolve.Names.key
  | Module_declarations of Path.module_
  | File_declarations of Path.file
  | Package_declarations of Path.package
  | Members of Path.t * string
  | Traits_declaring of Path.package * string
  | Impl_index of Path.package
  | Impls_of_type of Path.package * Path.t
  | Impls_of_trait of Path.package * Path.t
  | Law_proofs of Path.package * Resolve.Names.law_proof_name

type parsed = { tree : Syntax.file; diagnostics : Diagnostic.t list; text : string }

type _ stored =
  | Parsed : Path.file -> parsed stored
  | Namespace : Path.package -> Resolve.Namespace.t stored
  | Resolved : Resolve.Names.key * Resolve.section -> Resolve.resolved stored
  | Trait_header : Resolve.Names.key -> Resolve.trait_header stored
  | Constant_value : Path.t -> Z.t option stored
  | Header : Resolve.Names.key -> Interface.Environment.header stored
  | Interface : Resolve.Names.key -> Interface.Environment.elaborated_interface stored
  | Derived_interface : { type_ : Path.t; trait : Path.t } -> Types.impl_interface stored
  | Type_facts : Path.t -> Interface.Environment.type_facts stored
  | Grant : Path.package * Path.package -> Interface.Environment.grant stored
  | Signature_check : Resolve.Names.key -> unit stored
  | Contract : Resolve.Names.key -> Core.t stored
  | Checked_body : Resolve.Names.key -> Infer.checked stored
  | Body_mir : Resolve.Names.key -> Mir.body_part stored
  | Contract_mir : Resolve.Names.key -> Mir.contract_part stored
  | Generated_mir : Path.t -> (Mir.body_part * Mir.contract_part) stored
  | Call_edges : Path.t -> Mir.Call_edges.node stored
  | Usage : Resolve.Names.key -> unit stored
  | Ownership : Resolve.Names.key -> (Core.id list * Core.id list) list stored
  | Import_check : Path.file -> Diagnostic.t list stored
  | Package_check : Path.package * Package_checks.check -> Package_checks.outcome stored
  | Implementations : Path.t * Path.package -> unit stored
  | Recursion_group : Path.t -> Path.t list stored
  | Proof : Resolve.Names.key -> Prover.proof stored
  | Lowered : Lowered.Item.t -> (Lowering.lowered, Lowering.unsupported) result stored
  | Test_key : Lowered.Item.t -> (string, Lowering.unsupported) result stored

type any = Any : 'a stored -> any [@@unboxed]
type t = Input of input | Name of name | Stored of any

let find_type_definition : Ground.ty -> Path.t option = function
  | Named { path; _ } -> Some path
  | Any { trait; _ } -> Some trait
  | Function _ | Never -> None

let find_item_definition : Lowered.Item.t -> Path.t option = function
  | Code { path; _ }
  | Constant path
  | Evaluator path
  | Call_evaluation { function_ = path; _ }
  | Generated
      ( Locked_entry { capability = path; _ }
      | Adapter { function_ = path; _ }
      | Program_main path
      | Test_main path )
  | Table (Impl_table { impl = path; _ } | Any_table { impl = path; _ } | Locked_table path) ->
      Some path
  | Drop ty | Copy ty | Debug ty | Any_drop ty | Any_copy ty | Encode ty -> find_type_definition ty
  | Generated (Entry impl_method | Any_entry impl_method) ->
      Some (Lowered.Item.make_method_path impl_method)

module Storage = struct
  let find_type_equality : type a b. a stored -> b stored -> (a, b) Type.eq option =
   fun left right ->
    match (left, right) with
    | Parsed _, Parsed _ -> Some Equal
    | Namespace _, Namespace _ -> Some Equal
    | Resolved _, Resolved _ -> Some Equal
    | Trait_header _, Trait_header _ -> Some Equal
    | Constant_value _, Constant_value _ -> Some Equal
    | Header _, Header _ -> Some Equal
    | Interface _, Interface _ -> Some Equal
    | Derived_interface _, Derived_interface _ -> Some Equal
    | Type_facts _, Type_facts _ -> Some Equal
    | Grant _, Grant _ -> Some Equal
    | Signature_check _, Signature_check _ -> Some Equal
    | Contract _, Contract _ -> Some Equal
    | Checked_body _, Checked_body _ -> Some Equal
    | Body_mir _, Body_mir _ -> Some Equal
    | Contract_mir _, Contract_mir _ -> Some Equal
    | Generated_mir _, Generated_mir _ -> Some Equal
    | Call_edges _, Call_edges _ -> Some Equal
    | Usage _, Usage _ -> Some Equal
    | Ownership _, Ownership _ -> Some Equal
    | Import_check _, Import_check _ -> Some Equal
    | Package_check _, Package_check _ -> Some Equal
    | Implementations _, Implementations _ -> Some Equal
    | Recursion_group _, Recursion_group _ -> Some Equal
    | Proof _, Proof _ -> Some Equal
    | Lowered _, Lowered _ -> Some Equal
    | Test_key _, Test_key _ -> Some Equal
    | _ -> None

  let locate_stored_package : type a. a stored -> Path.package = function
    | Parsed file | Import_check file -> file.module_.package
    | Namespace package
    | Grant (package, _)
    | Package_check (package, _)
    | Implementations (_, package) ->
        package
    | Resolved (key, _)
    | Trait_header key
    | Header key
    | Interface key
    | Signature_check key
    | Contract key
    | Checked_body key
    | Body_mir key
    | Contract_mir key
    | Usage key
    | Ownership key
    | Proof key ->
        key.module_.package
    | Constant_value path
    | Type_facts path
    | Generated_mir path
    | Call_edges path
    | Recursion_group path
    | Derived_interface { type_ = path; _ } ->
        Path.locate_package path
    | Lowered key | Test_key key ->
        Option.fold ~none:Path.standard_package ~some:Path.locate_package (find_item_definition key)

  let locate_package (Any part) = locate_stored_package part

  let locate_name_package : name -> Path.package = function
    | File_declarations file -> file.module_.package
    | Package_declarations package
    | Traits_declaring (package, _)
    | Impl_index package
    | Impls_of_type (package, _)
    | Impls_of_trait (package, _)
    | Law_proofs (package, _) ->
        package
    | Module module_ | Entry (module_, _) | Entries module_ | Module_declarations module_ ->
        module_.package
    | Imports key
    | Declaration key
    | Tree key
    | Text key
    | Place key
    | Container key
    | Contained key ->
        key.module_.package
    | Members (path, _) -> Path.locate_package path
end

let show_key = Resolve.Names.show_key

let show_input = function
  | Source file -> "source " ^ Path.show_file file
  | Packages -> "packages"
  | Modules package -> "modules " ^ Path.show_package package
  | Files package -> "files " ^ Path.show_package package
  | Dependencies package -> "dependencies " ^ Path.show_package package

let show_name = function
  | Module module_ -> "module " ^ Path.show_module module_
  | Entry (module_, name) -> Printf.sprintf "entry %s %s" (Path.show_module module_) name
  | Entries module_ -> "entries " ^ Path.show_module module_
  | Imports declared -> "imports " ^ show_key declared
  | Declaration declared -> "declaration " ^ show_key declared
  | Tree declared -> "tree " ^ show_key declared
  | Text declared -> "text " ^ show_key declared
  | Place declared -> "place " ^ show_key declared
  | Container declared -> "container " ^ show_key declared
  | Contained declared -> "contained " ^ show_key declared
  | Module_declarations module_ -> "module declarations " ^ Path.show_module module_
  | File_declarations file -> "file declarations " ^ Path.show_file file
  | Package_declarations package -> "package declarations " ^ Path.show_package package
  | Members (owner, name) -> Printf.sprintf "members %s %s" (Path.show owner) name
  | Traits_declaring (package, name) ->
      Printf.sprintf "traits declaring %s %s" (Path.show_package package) name
  | Impl_index package -> "impl index " ^ Path.show_package package
  | Impls_of_type (package, type_) ->
      Printf.sprintf "impls of type %s %s" (Path.show_package package) (Path.show type_)
  | Impls_of_trait (package, trait) ->
      Printf.sprintf "impls of trait %s %s" (Path.show_package package) (Path.show trait)
  | Law_proofs (package, { trait; law; type_head }) ->
      Printf.sprintf "law proofs %s %s.%s for %s" (Path.show_package package) (Path.show trait) law
        (Path.show type_head)

let show_stored : type a. a stored -> string =
 fun part ->
  let show_section : Resolve.section -> string = function
    | Interface -> "interface"
    | Contract -> "contract"
    | Body -> "body"
  in
  match part with
  | Parsed file -> "parsed " ^ Path.show_file file
  | Namespace package -> "namespace " ^ Path.show_package package
  | Resolved (declared, part) ->
      Printf.sprintf "resolved %s %s" (show_section part) (show_key declared)
  | Trait_header declared -> "trait header " ^ show_key declared
  | Constant_value path -> "constant value " ^ Path.show path
  | Header declared -> "header " ^ show_key declared
  | Interface declared -> "interface " ^ show_key declared
  | Derived_interface { type_; trait } ->
      "derived interface " ^ Path.show (Derived { type_; trait })
  | Type_facts path -> "type facts " ^ Path.show path
  | Grant (package, dependency) ->
      Printf.sprintf "grant %s %s" (Path.show_package package) (Path.show_package dependency)
  | Signature_check declared -> "signature check " ^ show_key declared
  | Contract declared -> "contract " ^ show_key declared
  | Checked_body declared -> "checked body " ^ show_key declared
  | Body_mir declared -> "body mir " ^ show_key declared
  | Contract_mir declared -> "contract mir " ^ show_key declared
  | Generated_mir path -> "generated mir " ^ Path.show path
  | Call_edges path -> "call edges " ^ Path.show path
  | Usage declared -> "usage " ^ show_key declared
  | Ownership declared -> "ownership " ^ show_key declared
  | Import_check file -> "import check " ^ Path.show_file file
  | Package_check (package, check) ->
      Printf.sprintf "package check %s %s" (Path.show_package package)
        (match check with
        | Sealed declared -> "sealed " ^ show_key declared
        | Impl declared -> "impl " ^ show_key declared
        | Type declared -> "type " ^ show_key declared
        | Constant declared -> "constant " ^ show_key declared
        | Instantiations -> "instantiations"
        | Tests -> "tests"
        | Unexported -> "unexported"
        | Dependencies -> "dependencies")
  | Implementations (path, package) ->
      Printf.sprintf "implementations %s %s" (Path.show_package package) (Path.show path)
  | Recursion_group path -> "recursion group " ^ Path.show path
  | Proof declared -> "proof " ^ show_key declared
  | Lowered item -> "lowered " ^ Lowered.Item.to_string item
  | Test_key item -> "test key " ^ Lowered.Item.to_string item

let show = function
  | Input part -> show_input part
  | Name part -> show_name part
  | Stored (Any part) -> show_stored part

let find_name_definition = function
  | Module _ | Entries _ | Module_declarations _ | File_declarations _ | Package_declarations _
  | Traits_declaring _ | Impl_index _ ->
      None
  | Entry (module_, name) -> Some (Path.Top { module_; name })
  | Imports key | Declaration key | Tree key | Text key | Place key | Container key | Contained key
    ->
      Some key.path
  | Members (path, _)
  | Impls_of_type (_, path)
  | Impls_of_trait (_, path)
  | Law_proofs (_, { trait = path; _ }) ->
      Some path

let find_stored_definition : type a. a stored -> Path.t option = function
  | Parsed _ | Namespace _ | Grant _ | Import_check _
  | Package_check (_, (Instantiations | Tests | Unexported | Dependencies)) ->
      None
  | Resolved (key, _)
  | Trait_header key
  | Header key
  | Interface key
  | Signature_check key
  | Contract key
  | Checked_body key
  | Body_mir key
  | Contract_mir key
  | Usage key
  | Ownership key
  | Proof key
  | Package_check (_, (Sealed key | Impl key | Type key | Constant key)) ->
      Some key.path
  | Constant_value path
  | Type_facts path
  | Generated_mir path
  | Call_edges path
  | Implementations (path, _)
  | Recursion_group path ->
      Some path
  | Derived_interface { type_; trait } -> Some (Derived { type_; trait })
  | Lowered key | Test_key key -> find_item_definition key

let find_definition = function
  | Input _ -> None
  | Name part -> find_name_definition part
  | Stored (Any part) -> find_stored_definition part

let show_name_kind = function
  | Module _ -> "module"
  | Entry _ -> "namespace entry"
  | Entries _ -> "namespace entries of its module"
  | Imports _ -> "imports"
  | Declaration _ -> "declaration"
  | Tree _ -> "source tree"
  | Text _ -> "text"
  | Place _ -> "place"
  | Container _ -> "container"
  | Contained _ -> "members"
  | Module_declarations _ -> "declarations of a module"
  | File_declarations _ -> "declarations of a file"
  | Package_declarations _ -> "declarations of a package"
  | Members (_, name) -> Printf.sprintf "members named %s" name
  | Traits_declaring (_, name) -> Printf.sprintf "traits that declare %s" name
  | Impl_index _ -> "impls of a package"
  | Impls_of_type _ -> "impls"
  | Impls_of_trait _ -> "impls"
  | Law_proofs (_, { law; type_head; _ }) ->
      Printf.sprintf "proofs of the law %s for %s" law (Path.show type_head)

let show_stored_kind : type a. a stored -> string = function
  | Parsed _ -> "parsed file"
  | Namespace _ -> "namespace"
  | Resolved (_, Interface) -> "resolved names of the interface"
  | Resolved (_, Contract) -> "resolved names of the contract"
  | Resolved (_, Body) -> "resolved names of the body"
  | Trait_header _ -> "trait header"
  | Constant_value _ -> "value"
  | Header _ -> "header"
  | Interface _ -> "interface"
  | Derived_interface _ -> "derived interface"
  | Type_facts _ -> "type facts"
  | Grant _ -> "grant"
  | Signature_check _ -> "signature check"
  | Contract _ -> "contract"
  | Checked_body _ -> "checked body"
  | Body_mir _ -> "MIR of the body"
  | Generated_mir _ -> "generated MIR"
  | Contract_mir _ -> "MIR of the contract"
  | Call_edges _ -> "call edges"
  | Usage _ -> "usage check"
  | Ownership _ -> "ownership check"
  | Import_check _ -> "import check"
  | Package_check _ -> "package check"
  | Implementations _ -> "implementations"
  | Recursion_group _ -> "recursion group"
  | Proof _ -> "proof"
  | Lowered _ -> "lowered code"
  | Test_key _ -> "test key"

let show_kind = function
  | Input (Source _) -> "source"
  | Input Packages -> "packages"
  | Input (Modules _) -> "modules"
  | Input (Files _) -> "files"
  | Input (Dependencies _) -> "dependencies"
  | Name part -> show_name_kind part
  | Stored (Any part) -> show_stored_kind part
