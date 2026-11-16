type input =
  | Source of Path.file
  | Packages
  | Modules of Path.package
  | Dependencies of Path.package

type name =
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

type lowering = Lowered of Instance.key | Test_key of Instance.key

type computed =
  | Parsed of Path.file
  | Namespace of Path.package
  | Resolved of Resolve.Names.key * Resolve.section
  | Trait_header of Resolve.Names.key
  | Constant_value of Path.t
  | Header of Resolve.Names.key
  | Interface of Resolve.Names.key
  | Derived_interface of { type_ : Path.t; trait : Path.t }
  | Type_facts of Path.t
  | Grant of Path.package * Path.package
  | Signature_check of Resolve.Names.key
  | Contract of Resolve.Names.key
  | Checked_body of Resolve.Names.key
  | Derived_form of Path.t
  | Body_mir of Resolve.Names.key
  | Contract_mir of Resolve.Names.key
  | Generated_mir of Path.t
  | Call_edges of Path.t
  | Patterns of Resolve.Names.key
  | Usage of Resolve.Names.key
  | Ownership of Resolve.Names.key
  | Used_packages of Resolve.Names.key
  | Import_check of Path.file
  | Package_check of Path.package * Package_checks.check
  | Callees of Path.t * Path.package
  | Proof of Resolve.Names.key
  | Lowering of lowering

type stored = Computed of computed | Recursion_group of Path.t
type t = Input of input | Name of name | Stored of stored

let type_package : Ground.ty -> Path.package = function
  | Named { path; _ } -> Path.package path
  | Any { trait; _ } -> Path.package trait
  | Function _ | Never -> Path.standard_package

let instance_package : Instance.key -> Path.package = function
  | Code { path; _ }
  | Constant path
  | Evaluator path
  | Template_check { from_template = path; _ }
  | Call_evaluation { function_ = path; _ }
  | Generated
      (Locked_entry { capability = path; _ } | Adapter { function_ = path; _ } | Program_main path)
  | Table (Impl_table { impl = path; _ } | Any_table { impl = path; _ } | Locked_table path) ->
      Path.package path
  | Drop ty | Copy ty | Debug ty | Any_drop ty | Any_copy ty | Encode ty -> type_package ty
  | Generated (Entry impl_method | Any_entry impl_method) ->
      Path.package (Instance.make_method_path impl_method)

let package : computed -> Path.package = function
  | Parsed file | Import_check file -> file.module_.package
  | Namespace package | Grant (package, _) | Package_check (package, _) | Callees (_, package) ->
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
  | Patterns key
  | Usage key
  | Ownership key
  | Used_packages key
  | Proof key ->
      key.module_.package
  | Constant_value path
  | Type_facts path
  | Derived_form path
  | Generated_mir path
  | Call_edges path
  | Derived_interface { type_ = path; _ } ->
      Path.package path
  | Lowering (Lowered key | Test_key key) -> instance_package key

let name_package : name -> Path.package = function
  | File_declarations file -> file.module_.package
  | Package_declarations package
  | Traits_declaring (package, _)
  | Impl_index package
  | Impls_of_type (package, _)
  | Impls_of_trait (package, _)
  | Law_proofs (package, _) ->
      package
  | Entry (module_, _) | Entries module_ | Module_declarations module_ -> module_.package
  | Imports key | Declaration key | Tree key | Text key | Place key | Container key | Contained key
    ->
      key.module_.package
  | Members (path, _) -> Path.package path

let show_key = Resolve.Names.show_key

let show_input = function
  | Source file -> "source " ^ Path.show_file file
  | Packages -> "packages"
  | Modules package -> "modules " ^ Path.show_package package
  | Dependencies package -> "dependencies " ^ Path.show_package package

let show_name = function
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

let show_computed part =
  let section : Resolve.section -> string = function
    | Interface -> "interface"
    | Contract -> "contract"
    | Body -> "body"
  in
  match part with
  | Parsed file -> "parsed " ^ Path.show_file file
  | Namespace package -> "namespace " ^ Path.show_package package
  | Resolved (declared, part) -> Printf.sprintf "resolved %s %s" (section part) (show_key declared)
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
  | Derived_form path -> "derived form " ^ Path.show path
  | Body_mir declared -> "body mir " ^ show_key declared
  | Contract_mir declared -> "contract mir " ^ show_key declared
  | Generated_mir path -> "generated mir " ^ Path.show path
  | Call_edges path -> "call edges " ^ Path.show path
  | Patterns declared -> "patterns " ^ show_key declared
  | Usage declared -> "usage " ^ show_key declared
  | Ownership declared -> "ownership " ^ show_key declared
  | Used_packages declared -> "used packages " ^ show_key declared
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
        | Dependencies -> "dependencies")
  | Callees (path, package) ->
      Printf.sprintf "callees %s %s" (Path.show_package package) (Path.show path)
  | Proof declared -> "proof " ^ show_key declared
  | Lowering (Lowered instance) -> "lowered " ^ Instance.to_string instance
  | Lowering (Test_key instance) -> "test key " ^ Instance.to_string instance

let show = function
  | Input part -> show_input part
  | Name part -> show_name part
  | Stored (Computed part) -> show_computed part
  | Stored (Recursion_group path) -> "recursion group " ^ Path.show path

let type_definition : Ground.ty -> Path.t option = function
  | Named { path; _ } -> Some path
  | Any { trait; _ } -> Some trait
  | Function _ | Never -> None

let instance_definition : Instance.key -> Path.t option = function
  | Code { path; _ }
  | Constant path
  | Evaluator path
  | Template_check { from_template = path; _ }
  | Call_evaluation { function_ = path; _ }
  | Generated
      (Locked_entry { capability = path; _ } | Adapter { function_ = path; _ } | Program_main path)
  | Table (Impl_table { impl = path; _ } | Any_table { impl = path; _ } | Locked_table path) ->
      Some path
  | Drop ty | Copy ty | Debug ty | Any_drop ty | Any_copy ty | Encode ty -> type_definition ty
  | Generated (Entry impl_method | Any_entry impl_method) ->
      Some (Instance.make_method_path impl_method)

let name_definition = function
  | Entries _ | Module_declarations _ | File_declarations _ | Package_declarations _
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

let computed_definition = function
  | Parsed _ | Namespace _ | Grant _ | Import_check _
  | Package_check (_, (Instantiations | Tests | Dependencies)) ->
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
  | Patterns key
  | Usage key
  | Ownership key
  | Used_packages key
  | Proof key
  | Package_check (_, (Sealed key | Impl key | Type key | Constant key)) ->
      Some key.path
  | Constant_value path
  | Type_facts path
  | Derived_form path
  | Generated_mir path
  | Call_edges path
  | Callees (path, _) ->
      Some path
  | Derived_interface { type_; trait } -> Some (Derived { type_; trait })
  | Lowering (Lowered key | Test_key key) -> instance_definition key

let definition = function
  | Input _ -> None
  | Name part -> name_definition part
  | Stored (Computed part) -> computed_definition part
  | Stored (Recursion_group path) -> Some path

let name_kind_name = function
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

let computed_kind_name = function
  | Parsed _ -> "parsed file"
  | Namespace _ -> "namespace"
  | Resolved (_, Interface) -> "resolved names of the interface"
  | Resolved (_, Contract) -> "resolved names of the contract"
  | Resolved (_, Body) -> "resolved names of the body"
  | Trait_header _ -> "trait header"
  | Constant_value _ -> "value"
  | Header _ -> "header"
  | Interface _ | Derived_interface _ -> "interface"
  | Type_facts _ -> "type facts"
  | Grant _ -> "grant"
  | Signature_check _ -> "signature check"
  | Contract _ -> "contract"
  | Checked_body _ | Derived_form _ -> "checked body"
  | Body_mir _ | Generated_mir _ -> "MIR of the body"
  | Contract_mir _ -> "MIR of the contract"
  | Call_edges _ -> "call edges"
  | Patterns _ -> "pattern check"
  | Usage _ -> "usage check"
  | Ownership _ -> "ownership check"
  | Used_packages _ -> "used packages"
  | Import_check _ -> "import check"
  | Package_check _ -> "package check"
  | Callees _ -> "callees"
  | Proof _ -> "proof"
  | Lowering (Lowered _) -> "lowered code"
  | Lowering (Test_key _) -> "test key"

let kind_name = function
  | Input (Source _) -> "source"
  | Input Packages -> "packages"
  | Input (Modules _) -> "modules"
  | Input (Dependencies _) -> "dependencies"
  | Name part -> name_kind_name part
  | Stored (Computed part) -> computed_kind_name part
  | Stored (Recursion_group _) -> "recursion group"
