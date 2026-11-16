type t =
  | Parse
  | Namespaces
  | Resolution
  | Import_checks
  | Trait_headers
  | Constant_values
  | Headers
  | Interfaces
  | Derived_interfaces
  | Type_facts
  | Grants
  | Signature_checks
  | Contracts
  | Checked_bodies
  | Derived_forms
  | Mir
  | Call_edges
  | Body_checks
  | Package_checks
  | Successors
  | Recursion_groups
  | Proofs
  | Folded_constants
  | Lowered_code
  | Test_keys

val all : t list
val of_part : Part.computed -> t
val is_lowering : t -> bool
val drains : through:t -> t -> bool
