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

let all =
  [
    Input;
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
    Lowered_code;
    Test_keys;
  ]

let position stage =
  match List.find_index (fun candidate -> candidate = stage) all with
  | Some position -> position
  | None -> Compiler_bug.bug ~stage:"Database" "a stage is missing from the order of stages"

let precedes earlier later = position earlier <= position later

let is_lowering = function
  | Lowered_code | Test_keys -> true
  | Input | Parse | Namespaces | Resolution | Import_checks | Trait_headers | Constant_values
  | Headers | Interfaces | Derived_interfaces | Type_facts | Grants | Signature_checks | Contracts
  | Checked_bodies | Derived_forms | Mir | Call_edges | Body_checks | Package_checks | Callees
  | Recursion_groups | Proofs ->
      false

let drains ~through stage =
  precedes stage through
  && ((not (is_lowering through))
     || is_lowering stage || precedes stage Call_edges || stage = Callees)

let of_part : Part.t -> t = function
  | Source _ | Packages | Modules _ | Dependencies _ -> Input
  | Parsed _ -> Parse
  | Namespace _ | Entry _ | Entries _ | Imports _ | Declaration _ | Tree _ | Text _ | Place _
  | Container _ | Contained _ | Module_declarations _ | File_declarations _ | Package_declarations _
  | Members _ | Traits_declaring _ | Impl_index _ | Impls_of_type _ | Impls_of_trait _
  | Law_proofs _ ->
      Namespaces
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
  | Recursion_group _ -> Recursion_groups
  | Proof _ -> Proofs
  | Lowered _ -> Lowered_code
  | Test_key _ -> Test_keys
