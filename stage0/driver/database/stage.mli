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
  | Signature_checks
  | Contracts
  | Checked_bodies
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
val compare : t -> t -> int
val of_part : Part.any -> t
val is_lowering : t -> bool
val drains : through:t -> t -> bool
