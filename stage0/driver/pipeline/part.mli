type t =
  | Source of Path.file
  | Parsed of Path.file
  | Packages
  | Module of Path.module_
  | Dependencies of Path.package
  | Entries of Path.module_
  | Entry of Path.module_ * string
  | Namespace of Path.module_
  | Module_index of Path.module_
  | Package_index of Path.package
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
  | Resolved of Resolve.Names.key * Resolve.section
  | Trait_header of Resolve.Names.key
  | Constant_value of Path.t
  | Header of Resolve.Names.key
  | Interface of Resolve.Names.key
  | Derived_interface of Path.t
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
  | Successors of Path.t * Path.package
  | Recursion_group of Path.t
  | Proof of Resolve.Names.key
  | Ground_types of Instance.key
  | Layout of Ground.ty
  | Lowered of Instance.key
  | Test_key of Instance.key

val package : t -> Path.package
val equal : t -> t -> bool
val hash : t -> int
val show : t -> string
val definition : t -> Path.t option
val kind_name : t -> string
