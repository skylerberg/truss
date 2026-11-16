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
  | Callees
  | Recursion_groups
  | Proofs
  | Folded_constants
  | Lowered_code
  | Test_keys

let all =
  [
    Parse;
    Namespaces;
    Resolution;
    Import_checks;
    Trait_headers;
    Constant_values;
    Headers;
    Interfaces;
    Derived_interfaces;
    Type_facts;
    Grants;
    Signature_checks;
    Contracts;
    Checked_bodies;
    Derived_forms;
    Mir;
    Call_edges;
    Body_checks;
    Package_checks;
    Callees;
    Recursion_groups;
    Proofs;
    Folded_constants;
    Lowered_code;
    Test_keys;
  ]

let position stage =
  match List.find_index (fun candidate -> candidate = stage) all with
  | Some position -> position
  | None -> Compiler_bug.bug ~stage:"Database" "a stage is missing from the order of stages"

let precedes earlier later = position earlier <= position later

let is_lowering = function
  | Folded_constants | Lowered_code | Test_keys -> true
  | Parse | Namespaces | Resolution | Import_checks | Trait_headers | Constant_values | Headers
  | Interfaces | Derived_interfaces | Type_facts | Grants | Signature_checks | Contracts
  | Checked_bodies | Derived_forms | Mir | Call_edges | Body_checks | Package_checks | Callees
  | Recursion_groups | Proofs ->
      false

let drains ~through stage =
  precedes stage through
  && ((not (is_lowering through))
     || is_lowering stage || precedes stage Call_edges || stage = Callees)

let of_part : Part.computed -> t = function
  | Parsed _ -> Parse
  | Namespace _ -> Namespaces
  | Resolved _ -> Resolution
  | Import_check _ -> Import_checks
  | Trait_header _ -> Trait_headers
  | Constant_value _ -> Constant_values
  | Header _ -> Headers
  | Interface _ -> Interfaces
  | Derived_interface _ -> Derived_interfaces
  | Type_facts _ -> Type_facts
  | Grant _ -> Grants
  | Signature_check _ -> Signature_checks
  | Contract _ -> Contracts
  | Checked_body _ -> Checked_bodies
  | Derived_form _ -> Derived_forms
  | Body_mir _ | Contract_mir _ | Generated_mir _ -> Mir
  | Call_edges _ -> Call_edges
  | Patterns _ | Usage _ | Ownership _ | Used_packages _ -> Body_checks
  | Package_check _ -> Package_checks
  | Callees _ -> Callees
  | Proof _ -> Proofs
  | Lowering (Folded_constants _) -> Folded_constants
  | Lowering (Lowered _) -> Lowered_code
  | Lowering (Test_key _) -> Test_keys
