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
  | Mir_call_edges
  | Body_checks
  | Package_checks
  | Call_edges
  | Recursion_groups
  | Proofs
  | Lowered_code
  | Test_keys

val all : t list
val of_part : Part.computed -> t
val is_lowering : t -> bool
val drains : through:t -> t -> bool
