type stage =
  | Parse
  | Declare
  | Synthesize
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
  | Find_aborts
  | Check_usage
  | Check_ownership
  | Check_sealed
  | Check_impl
  | Check_type
  | Check_instantiation
  | Check_test
  | Check_unexported
  | Check_dependency
  | Prove
  | Lower
  | Key_tests
  | Evaluate
  | Run_test
  | Render of Profile.t
  | Decide

let stages =
  [
    Parse;
    Declare;
    Synthesize;
    Claim_roots;
    Resolve;
    Resolve_grant;
    Check_imports;
    Read_trait_header;
    Evaluate_constant;
    Elaborate_header;
    Elaborate;
    Derive_interface;
    Compute_type_facts;
    Check_signature;
    Check_contract;
    Check_body;
    Build_body_mir;
    Build_contract_mir;
    Generate_mir;
    List_calls;
    Group_recursion;
    Find_aborts;
    Check_usage;
    Check_ownership;
    Check_sealed;
    Check_impl;
    Check_type;
    Check_instantiation;
    Check_test;
    Check_unexported;
    Check_dependency;
    Prove;
    Lower;
    Key_tests;
    Evaluate;
    Run_test;
    Render Development;
    Render Release;
    Decide;
  ]

let make_ranker values =
  let ranks = Hashtbl.create 64 in
  List.iteri (fun rank value -> Hashtbl.replace ranks value rank) values;
  fun value ->
    match Hashtbl.find_opt ranks value with
    | Some rank -> rank
    | None ->
        Compiler_bug.raise_bug ~stage:"Database" "a kind is missing from the list of its kinds"

let rank_stage = make_ranker stages

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
  | Checked_interface
  | Contract
  | Body_form
  | Body_tables
  | Run_forever
  | Ownership_modes
  | Body_mir
  | Contract_mir
  | Generated_mir
  | Callees
  | Size_changes
  | Recursion_group
  | Proof_group
  | Calls_without_decrease
  | Aborts_outside_group
  | May_abort
  | Usage_check
  | Ownership
  | Dependency_use
  | Proof
  | Lowered
  | Test_key
  | Evaluation
  | Test_run
  | Unit of Profile.t

let facts =
  [
    Resolved Interface;
    Resolved Contract;
    Resolved Body;
    Grant;
    Trait_header;
    Constant_value;
    Header;
    Interface;
    Elaboration;
    Derived_interface;
    Type_facts;
    Signature_check;
    Checked_interface;
    Contract;
    Body_form;
    Body_tables;
    Run_forever;
    Ownership_modes;
    Body_mir;
    Contract_mir;
    Generated_mir;
    Callees;
    Size_changes;
    Recursion_group;
    Proof_group;
    Calls_without_decrease;
    Aborts_outside_group;
    May_abort;
    Usage_check;
    Ownership;
    Dependency_use;
    Proof;
    Lowered;
    Test_key;
    Evaluation;
    Test_run;
    Unit Development;
    Unit Release;
  ]

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
  | Members
  | Traits_declaring
  | Impls_of_type
  | Impls_of_trait
  | Law_proofs
  | Tests

let lookups =
  [
    Source;
    Packages;
    Files;
    Dependencies;
    Module;
    Entry;
    Entries;
    Imports;
    Declaration;
    Tree;
    Text;
    Place;
    Container;
    Contained;
    Module_declarations;
    File_declarations;
    Members;
    Traits_declaring;
    Impls_of_type;
    Impls_of_trait;
    Law_proofs;
    Tests;
  ]

type entity = Definition | Import | Package | Item
type selection = Unresolved | Import_references | Package_references

let entities = [ Definition; Import; Package; Item ]
let selections = [ Unresolved; Import_references; Package_references ]

type target = Fact of fact | Lookup of lookup | Entity of entity | Selection of selection

let rank_fact = make_ranker facts
let rank_lookup = make_ranker lookups
let rank_entity = make_ranker entities
let rank_selection = make_ranker selections

let rank_target = function
  | Fact fact -> 100 + rank_fact fact
  | Lookup lookup -> 1000 + rank_lookup lookup
  | Entity entity -> 2000 + rank_entity entity
  | Selection selection -> 3000 + rank_selection selection

let find_target rank =
  let find_in values first make =
    if rank >= first && rank < first + List.length values then
      Some (make (List.nth values (rank - first)))
    else None
  in
  List.find_map Fun.id
    [
      find_in facts 100 (fun fact -> Fact fact);
      find_in lookups 1000 (fun lookup -> Lookup lookup);
      find_in entities 2000 (fun entity -> Entity entity);
      find_in selections 3000 (fun selection -> Selection selection);
    ]

let show_stage = function
  | Parse -> "parsed file"
  | Declare -> "declarations"
  | Synthesize -> "synthesized methods"
  | Claim_roots -> "roots of lowering"
  | Resolve -> "resolved names"
  | Resolve_grant -> "grant"
  | Check_imports -> "import check"
  | Read_trait_header -> "trait header"
  | Evaluate_constant -> "value"
  | Elaborate_header -> "header"
  | Elaborate -> "interface"
  | Derive_interface -> "derived interface"
  | Compute_type_facts -> "type facts"
  | Check_signature -> "signature check"
  | Check_contract -> "contract"
  | Check_body -> "checked body"
  | Build_body_mir -> "MIR of the body"
  | Build_contract_mir -> "MIR of the contract"
  | Generate_mir -> "generated MIR"
  | List_calls -> "call edges"
  | Group_recursion -> "recursion group"
  | Find_aborts -> "abort sites"
  | Check_usage -> "usage check"
  | Check_ownership -> "ownership check"
  | Check_sealed | Check_impl | Check_type | Check_instantiation | Check_test | Check_unexported
  | Check_dependency ->
      "package check"
  | Prove -> "proof"
  | Lower -> "lowered code"
  | Key_tests -> "test key"
  | Evaluate -> "evaluation"
  | Run_test -> "test run"
  | Render Development -> "development unit"
  | Render Release -> "release unit"
  | Decide -> "verdicts"

let show_fact = function
  | Resolved Interface -> "resolved names of the interface"
  | Resolved Contract -> "resolved names of the contract"
  | Resolved Body -> "resolved names of the body"
  | Grant -> "grant"
  | Trait_header -> "trait header"
  | Constant_value -> "value"
  | Header -> "header"
  | Interface | Elaboration | Checked_interface -> "interface"
  | Derived_interface -> "derived interface"
  | Type_facts -> "type facts"
  | Signature_check -> "signature check"
  | Contract -> "contract"
  | Body_form | Body_tables | Run_forever | Ownership_modes -> "checked body"
  | Body_mir -> "MIR of the body"
  | Contract_mir -> "MIR of the contract"
  | Generated_mir -> "generated MIR"
  | Callees -> "call edges"
  | Size_changes -> "size-change graphs"
  | Recursion_group -> "recursion group"
  | Proof_group -> "proof group"
  | Calls_without_decrease -> "calls without a decrease"
  | Aborts_outside_group | May_abort -> "abort sites"
  | Usage_check -> "usage check"
  | Ownership -> "ownership check"
  | Dependency_use -> "package check"
  | Proof -> "proof"
  | Lowered -> "lowered code"
  | Test_key -> "test key"
  | Evaluation -> "evaluation"
  | Test_run -> "test run"
  | Unit Development -> "development unit"
  | Unit Release -> "release unit"

let show_lookup = function
  | Source -> "source"
  | Packages -> "packages"
  | Files -> "files"
  | Dependencies -> "dependencies"
  | Module -> "module"
  | Entry -> "namespace entry"
  | Entries -> "namespace entries of its module"
  | Imports -> "imports"
  | Declaration -> "declaration"
  | Tree -> "source tree"
  | Text -> "text"
  | Place -> "place"
  | Container -> "container"
  | Contained -> "members"
  | Module_declarations -> "declarations of a module"
  | File_declarations -> "declarations of a file"
  | Members -> "members"
  | Traits_declaring -> "traits that declare a member"
  | Impls_of_type | Impls_of_trait -> "impls"
  | Law_proofs -> "proofs of a law"
  | Tests -> "tests of a name"

let is_signature = function
  | Header | Trait_header | Constant_value | Interface | Elaboration | Derived_interface
  | Type_facts | Signature_check | Checked_interface | Contract | Contract_mir ->
      true
  | Resolved _ | Grant | Body_form | Body_tables | Run_forever | Ownership_modes | Body_mir
  | Generated_mir | Callees | Size_changes | Recursion_group | Proof_group | Calls_without_decrease
  | Aborts_outside_group | May_abort | Usage_check | Ownership | Dependency_use | Proof | Lowered
  | Test_key | Evaluation | Test_run | Unit _ ->
      false

let list_read_targets = function
  | Interface -> [ Interface; Checked_interface ]
  | Signature_check -> [ Checked_interface ]
  | ( Resolved _ | Grant | Trait_header | Constant_value | Header | Elaboration | Derived_interface
    | Type_facts | Checked_interface | Contract | Body_form | Body_tables | Run_forever
    | Ownership_modes | Body_mir | Contract_mir | Generated_mir | Callees | Size_changes
    | Recursion_group | Proof_group | Calls_without_decrease | Aborts_outside_group | May_abort
    | Usage_check | Ownership | Dependency_use | Proof | Lowered | Test_key | Evaluation | Test_run
    | Unit _ ) as fact ->
      [ fact ]

let lookups_of_definition = [ Imports; Declaration; Tree; Text; Place; Container; Contained ]
let facts_of_definition = facts

type marker = Reads | References | Calls | Assumes | Instantiates | Grows | Claims

let rank_marker = function
  | Reads -> 1
  | References -> 2
  | Calls -> 4
  | Instantiates -> 8
  | Grows -> 16
  | Claims -> 32
  | Assumes -> 64

let encode_markers markers =
  List.fold_left (fun encoded marker -> encoded lor rank_marker marker) 0 markers

let has_marker encoded marker = encoded land rank_marker marker <> 0
