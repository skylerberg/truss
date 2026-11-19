type t =
  | Parse
  | Namespaces
  | Resolution
  | Import_checks
  | Trait_headers
  | Folded_integers
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

let all =
  [
    Parse;
    Namespaces;
    Resolution;
    Import_checks;
    Trait_headers;
    Folded_integers;
    Headers;
    Interfaces;
    Derived_interfaces;
    Type_facts;
    Signature_checks;
    Contracts;
    Checked_bodies;
    Mir;
    Mir_call_edges;
    Body_checks;
    Package_checks;
    Call_edges;
    Recursion_groups;
    Proofs;
    Lowered_code;
    Test_keys;
  ]

let rank_stage stage =
  match List.find_index (fun candidate -> candidate = stage) all with
  | Some position -> position
  | None -> Compiler_bug.raise_bug ~stage:"Database" "a stage is missing from the order of stages"

let compare earlier later = Int.compare (rank_stage earlier) (rank_stage later)
let precedes earlier later = compare earlier later <= 0

let is_lowering = function
  | Lowered_code | Test_keys -> true
  | Parse | Namespaces | Resolution | Import_checks | Trait_headers | Folded_integers | Headers
  | Interfaces | Derived_interfaces | Type_facts | Signature_checks | Contracts | Checked_bodies
  | Mir | Mir_call_edges | Body_checks | Package_checks | Call_edges | Recursion_groups | Proofs ->
      false

let drains ~through stage =
  precedes stage through
  && ((not (is_lowering through))
     || is_lowering stage || precedes stage Mir_call_edges || stage = Call_edges)

let of_part (Part.Any part) =
  match part with
  | Parsed _ -> Parse
  | Namespace _ -> Namespaces
  | Resolved _ | Grant _ -> Resolution
  | Import_check _ -> Import_checks
  | Trait_header _ -> Trait_headers
  | Folded_integer _ -> Folded_integers
  | Header _ -> Headers
  | Interface _ -> Interfaces
  | Derived_interface _ -> Derived_interfaces
  | Type_facts _ -> Type_facts
  | Signature_check _ -> Signature_checks
  | Contract _ -> Contracts
  | Checked_body _ -> Checked_bodies
  | Body_mir _ | Contract_mir _ | Generated_mir _ -> Mir
  | Mir_call_edges _ -> Mir_call_edges
  | Usage _ | Ownership _ -> Body_checks
  | Package_check _ -> Package_checks
  | Call_edges _ -> Call_edges
  | Recursion_group _ -> Recursion_groups
  | Proof _ -> Proofs
  | Lowered _ -> Lowered_code
  | Test_key _ -> Test_keys
