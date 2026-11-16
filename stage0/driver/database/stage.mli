type t =
  | Input
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
  | Callees
  | Recursion_groups
  | Proofs
  | Lowered_code
  | Test_keys

val all : t list
val of_part : Part.t -> t
val is_lowering : t -> bool
val drains : through:t -> t -> bool
