type stage =
  | Parse
  | Declare
  | Supply
  | Claim_roots
  | Resolve
  | Resolve_grant
  | Check_imports
  | Read_trait_header
  | Evaluate_constant
  | Elaborate_header
  | Elaborate
  | Derive_interface
  | Compute_type_facts
  | Check_signature
  | Check_contract
  | Check_body
  | Build_body_mir
  | Build_contract_mir
  | Generate_mir
  | List_calls
  | Group_recursion
  | Check_usage
  | Check_ownership
  | Check_sealed
  | Check_impl
  | Check_type
  | Check_instantiations
  | Check_tests
  | Check_unexported
  | Check_dependencies
  | Prove
  | Lower
  | Key_tests
  | Decide

val stages : stage list
val rank_stage : stage -> int

type fact =
  | Resolved of Resolve.section
  | Grant
  | Trait_header
  | Constant_value
  | Header
  | Interface
  | Elaboration
  | Derived_interface
  | Type_facts
  | Signature_check
  | Contract
  | Body_form
  | Body_tables
  | Run_forever
  | Ownership_modes
  | Body_mir
  | Contract_mir
  | Generated_mir
  | Call_node
  | Callees
  | Recursion_group
  | Usage_check
  | Ownership
  | Unused_dependencies
  | Proof
  | Lowered
  | Test_key

type lookup =
  | Source
  | Packages
  | Files
  | Dependencies
  | Module
  | Entry
  | Entries
  | Imports
  | Declaration
  | Tree
  | Text
  | Place
  | Container
  | Contained
  | Module_declarations
  | File_declarations
  | Package_declarations
  | Members
  | Traits_declaring
  | Impl_index
  | Impls_of_type
  | Impls_of_trait
  | Law_proofs

type entity = Definition | Import | Package | Unknown_implementation | Item

type selection =
  | Unresolved
  | Import_references
  | Unchecked_bodies
  | Body_uses
  | Instantiations
  | Package_references

type target = Fact of fact | Lookup of lookup | Entity of entity | Selection of selection

val rank_target : target -> int
val find_target : int -> target option
val show_stage : stage -> string
val show_fact : fact -> string
val show_lookup : lookup -> string
val is_signature : fact -> bool
val lookups_of_definition : lookup list
val facts_of_definition : fact list

type marker = Reads | References | Calls | Instantiates | Grows | Claims | Implements

val encode_markers : marker list -> int
val has_marker : int -> marker -> bool
