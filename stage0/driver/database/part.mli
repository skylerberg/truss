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

module Storage : sig
  val find_type_equality : 'a stored -> 'b stored -> ('a, 'b) Type.eq option
  val locate_package : any -> Path.package
  val locate_name_package : name -> Path.package
end

val show : t -> string
val find_definition : t -> Path.t option
val show_kind : t -> string
