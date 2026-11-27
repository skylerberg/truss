let rank_section : Resolve.section -> int = function Interface -> 0 | Contract -> 1 | Body -> 2

let resolved =
  let make section : Resolve.resolved Tracker.fact =
    Tracker.make_fact ~stage:Resolve ~table:"resolved" ~id_column:"definition"
      ~fixed:[ ("section", Integer (rank_section section)) ]
      ~groups:[ (Resolved section, [ "names"; "brackets"; "holes" ]) ]
      ~encode:(fun (resolved : Resolve.resolved) ->
        [
          Tracker.marshal resolved.names;
          Tracker.marshal resolved.brackets;
          Tracker.marshal resolved.holes;
        ])
      ~decode:(fun cells ->
        {
          names = Tracker.unmarshal cells.(0);
          brackets = Tracker.unmarshal cells.(1);
          holes = Tracker.unmarshal cells.(2);
        })
  in
  let interface = make Interface and contract = make Contract and body = make Body in
  function Resolve.Interface -> interface | Contract -> contract | Body -> body

let make_marshaled ~stage ~table ~id_column target =
  Tracker.make_fact ~stage ~table ~id_column ~fixed:[]
    ~groups:[ (target, [ "value" ]) ]
    ~encode:(fun value -> [ Tracker.marshal value ])
    ~decode:(fun cells -> Tracker.unmarshal cells.(0))

let grant : Interface.Environment.grant Tracker.fact =
  Tracker.make_fact ~stage:Resolve_grant ~table:"grant" ~id_column:"dependency" ~fixed:[]
    ~groups:[ (Grant, [ "capabilities"; "unknown" ]) ]
    ~encode:(fun (grant : Interface.Environment.grant) ->
      [ Tracker.marshal grant.capabilities; Tracker.marshal grant.unknown ])
    ~decode:(fun cells ->
      { capabilities = Tracker.unmarshal cells.(0); unknown = Tracker.unmarshal cells.(1) })

let trait_header : Resolve.trait_header Tracker.fact =
  make_marshaled ~stage:Read_trait_header ~table:"trait_header" ~id_column:"definition" Trait_header

let constant_value : Interface.Constants.outcome Tracker.fact =
  make_marshaled ~stage:Evaluate_constant ~table:"constant_value" ~id_column:"path" Constant_value

let header : Interface.Environment.header Tracker.fact =
  make_marshaled ~stage:Elaborate_header ~table:"header" ~id_column:"definition" Header

let elaborated : Interface.Environment.elaborated_interface Tracker.fact =
  Tracker.make_fact ~stage:Elaborate ~table:"interface" ~id_column:"definition" ~fixed:[]
    ~groups:[ (Interface, [ "value" ]); (Elaboration, [ "applications"; "scope" ]) ]
    ~encode:(fun (elaborated : Interface.Environment.elaborated_interface) ->
      [
        Tracker.marshal elaborated.interface;
        Tracker.marshal elaborated.applications;
        Tracker.marshal elaborated.scope;
      ])
    ~decode:(fun cells ->
      {
        interface = Tracker.unmarshal cells.(0);
        diagnostics = [];
        applications = Tracker.unmarshal cells.(1);
        scope = Tracker.unmarshal cells.(2);
      })

let interface : Interface.Environment.interface Tracker.view =
  Tracker.make_view ~stage:Elaborate ~table:"interface" ~id_column:"definition" ~fixed:[]
    ~target:Interface ~columns:[ "value" ] ~decode:(fun cells -> Tracker.unmarshal cells.(0))

let require_checked_signature view ~targets =
  Tracker.guard_view view ~stage:Check_signature ~table:"signature_check" ~targets
    ~id_column:"definition"

let checked_interface = require_checked_signature interface ~targets:[ Checked_interface ]

let checked_elaborated =
  require_checked_signature elaborated.whole ~targets:[ Checked_interface; Elaboration ]

let derived_interface : Types.impl_interface Tracker.fact =
  make_marshaled ~stage:Derive_interface ~table:"derived_interface" ~id_column:"path"
    Derived_interface

let type_facts : Interface.Environment.type_facts Tracker.fact =
  Tracker.make_fact ~stage:Compute_type_facts ~table:"type_facts" ~id_column:"path" ~fixed:[]
    ~groups:
      [ (Type_facts, [ "generics"; "copyable"; "plain"; "view"; "holds_function"; "contains" ]) ]
    ~encode:(fun (facts : Interface.Environment.type_facts) ->
      [
        Tracker.marshal facts.generics;
        Tracker.marshal facts.copyable;
        Tracker.marshal facts.plain;
        Tracker.marshal facts.view;
        Tracker.marshal facts.holds_function;
        Tracker.marshal facts.contains;
      ])
    ~decode:(fun cells ->
      {
        generics = Tracker.unmarshal cells.(0);
        copyable = Tracker.unmarshal cells.(1);
        plain = Tracker.unmarshal cells.(2);
        view = Tracker.unmarshal cells.(3);
        holds_function = Tracker.unmarshal cells.(4);
        contains = Tracker.unmarshal cells.(5);
      })

let signature_check : unit Tracker.fact =
  Tracker.make_fact ~stage:Check_signature ~table:"signature_check" ~id_column:"definition"
    ~fixed:[]
    ~groups:[ (Signature_check, []) ]
    ~encode:(fun () -> [])
    ~decode:(fun _ -> ())

let contract : Core.t Tracker.fact =
  Tracker.make_fact ~stage:Check_contract ~table:"contract" ~id_column:"definition" ~fixed:[]
    ~groups:[ (Contract, [ "form" ]) ]
    ~encode:(fun form -> [ Tracker.marshal form ])
    ~decode:(fun cells -> Tracker.unmarshal cells.(0))

let decode_boolean : Store.cell -> bool = function
  | Integer value -> value <> 0
  | Blob _ | Text _ | Null ->
      Compiler_bug.raise_bug ~stage:"Database" "a column that holds a boolean holds none"

let body : Infer.checked Tracker.fact =
  Tracker.make_fact ~stage:Check_body ~table:"body" ~id_column:"definition" ~fixed:[]
    ~groups:
      [
        (Body_form, [ "form" ]);
        (Body_tables, [ "tables" ]);
        (Capability_uses, [ "capability_uses" ]);
        (Ownership_modes, [ "places_without_keyword"; "mode_keywords" ]);
      ]
    ~encode:(fun (checked : Infer.checked) ->
      [
        Tracker.marshal checked.form;
        Tracker.marshal checked.tables;
        Tracker.marshal checked.capability_uses;
        Tracker.marshal checked.places_without_keyword;
        Tracker.marshal checked.mode_keywords;
      ])
    ~decode:(fun cells ->
      {
        form = Tracker.unmarshal cells.(0);
        tables = Tracker.unmarshal cells.(1);
        used_packages = [];
        capability_uses = Tracker.unmarshal cells.(2);
        places_without_keyword = Tracker.unmarshal cells.(3);
        mode_keywords = Tracker.unmarshal cells.(4);
      })

let make_body_view target columns decode =
  Tracker.make_view ~stage:Check_body ~table:"body" ~id_column:"definition" ~fixed:[] ~target
    ~columns ~decode

let body_form : Core.t Tracker.view =
  make_body_view Body_form [ "form" ] (fun cells -> Tracker.unmarshal cells.(0))

let body_tables : Infer.tables Tracker.view =
  make_body_view Body_tables [ "tables" ] (fun cells -> Tracker.unmarshal cells.(0))

let capability_uses : Infer.capability_use list Tracker.view =
  make_body_view Capability_uses [ "capability_uses" ] (fun cells -> Tracker.unmarshal cells.(0))

let ownership_modes : ((Syntax.id * Language.Mode.t) list * Core.mode_keyword list) Tracker.view =
  make_body_view Ownership_modes [ "places_without_keyword"; "mode_keywords" ] (fun cells ->
      (Tracker.unmarshal cells.(0), Tracker.unmarshal cells.(1)))

let make_graph_fact ~stage ~table target =
  Tracker.make_fact ~stage ~table ~id_column:"definition" ~fixed:[]
    ~groups:[ (target, [ "graph" ]) ]
    ~encode:(fun value -> [ Tracker.marshal value ])
    ~decode:(fun cells -> Tracker.unmarshal cells.(0))

let body_mir : Mir.body_part Tracker.fact =
  make_graph_fact ~stage:Build_body_mir ~table:"body_mir" Body_mir

let contract_mir : Mir.contract_part Tracker.fact =
  make_graph_fact ~stage:Build_contract_mir ~table:"contract_mir" Contract_mir

let usage_check : unit Tracker.fact =
  Tracker.make_fact ~stage:Check_usage ~table:"usage_check" ~id_column:"definition" ~fixed:[]
    ~groups:[ (Usage_check, []) ]
    ~encode:(fun () -> [])
    ~decode:(fun _ -> ())

let ownership : (Core.id list * Core.id list) list Tracker.fact =
  Tracker.make_fact ~stage:Check_ownership ~table:"ownership" ~id_column:"definition" ~fixed:[]
    ~groups:[ (Ownership, [ "must_be_disjoint" ]) ]
    ~encode:(fun pairs -> [ Tracker.marshal pairs ])
    ~decode:(fun cells -> Tracker.unmarshal cells.(0))

let generated_mir : (Mir.body_part * Mir.contract_part) Tracker.fact =
  Tracker.make_fact ~stage:Generate_mir ~table:"generated_mir" ~id_column:"path" ~fixed:[]
    ~groups:[ (Generated_mir, [ "body"; "contract" ]) ]
    ~encode:(fun (body, contract) -> [ Tracker.marshal body; Tracker.marshal contract ])
    ~decode:(fun cells -> (Tracker.unmarshal cells.(0), Tracker.unmarshal cells.(1)))

type call_node = { callees : Path.t list; size_changes : Mir.Size_change.summary }

let call_node : call_node Tracker.fact =
  Tracker.make_fact ~stage:List_calls ~table:"call_node" ~id_column:"path" ~fixed:[]
    ~groups:[ (Callees, [ "callees" ]); (Size_changes, [ "size_changes" ]) ]
    ~encode:(fun { callees; size_changes } ->
      [ Tracker.marshal callees; Tracker.marshal size_changes ])
    ~decode:(fun cells ->
      { callees = Tracker.unmarshal cells.(0); size_changes = Tracker.unmarshal cells.(1) })

let make_call_node_view target column =
  Tracker.make_view ~stage:List_calls ~table:"call_node" ~id_column:"path" ~fixed:[] ~target
    ~columns:[ column ] ~decode:(fun cells -> Tracker.unmarshal cells.(0))

let callees : Path.t list Tracker.view = make_call_node_view Callees "callees"

let size_changes : Mir.Size_change.summary Tracker.view =
  make_call_node_view Size_changes "size_changes"

let make_group ~table target : Path.t list Tracker.fact =
  Tracker.make_fact ~stage:Group_recursion ~table ~id_column:"path" ~fixed:[]
    ~groups:[ (target, [ "representative"; "members" ]) ]
    ~encode:(fun members : Store.cell list ->
      [
        (match members with first :: _ -> Integer (Ids.of_path first) | [] -> Null);
        Tracker.marshal members;
      ])
    ~decode:(fun cells -> Tracker.unmarshal cells.(1))

let recursion_group = make_group ~table:"recursion_group" Recursion_group
let proof_group = make_group ~table:"proof_group" Proof_group

let termination : Mir.Size_change.verdict Tracker.fact =
  make_marshaled ~stage:Group_recursion ~table:"termination" ~id_column:"path" Termination

let make_abort_fact ~table target : bool Tracker.fact =
  Tracker.make_fact ~stage:Find_aborts ~table ~id_column:"path" ~fixed:[]
    ~groups:[ (target, [ "value" ]) ]
    ~encode:(fun value -> [ Integer (Bool.to_int value) ])
    ~decode:(fun cells -> decode_boolean cells.(0))

let aborts_outside_group = make_abort_fact ~table:"aborts_outside_group" Aborts_outside_group
let may_abort = make_abort_fact ~table:"may_abort" May_abort

let proof : Prover.proof Tracker.fact =
  make_marshaled ~stage:Prove ~table:"proof" ~id_column:"definition" Proof

let dependency_use : bool Tracker.fact =
  Tracker.make_fact ~stage:Check_dependency ~table:"dependency_use" ~id_column:"dependency"
    ~fixed:[]
    ~groups:[ (Dependency_use, [ "is_used" ]) ]
    ~encode:(fun is_used -> [ Integer (Bool.to_int is_used) ])
    ~decode:(fun cells -> decode_boolean cells.(0))

let lowered : (Lowering.lowered, Lowering.unbuildable) result Tracker.fact =
  Tracker.make_fact ~stage:Lower ~table:"lowered" ~id_column:"item" ~fixed:[]
    ~groups:[ (Lowered, [ "code"; "is_evaluated"; "sites" ]) ]
    ~encode:(fun code ->
      let is_evaluated, sites =
        match code with
        | Ok lowered -> (Lowering.is_evaluated lowered, Lowering.list_sites lowered)
        | Error _ -> (false, [])
      in
      [ Tracker.marshal code; Integer (Bool.to_int is_evaluated); Tracker.marshal sites ])
    ~decode:(fun cells -> Tracker.unmarshal cells.(0))

let test_key : (string, Lowering.unbuildable) result Tracker.fact =
  Tracker.make_fact ~stage:Key_tests ~table:"test_key" ~id_column:"item" ~fixed:[]
    ~groups:[ (Test_key, [ "key" ]) ]
    ~encode:(fun key -> [ Tracker.marshal key ])
    ~decode:(fun cells -> Tracker.unmarshal cells.(0))

let evaluation : Lowering.evaluation Tracker.fact =
  make_marshaled ~stage:Evaluate ~table:"evaluation" ~id_column:"item" Evaluation

let test_run : Lowering.test_pass Tracker.fact =
  Tracker.make_fact ~stage:Run_test ~table:"test_run" ~id_column:"item" ~fixed:[]
    ~groups:[ (Test_run, [ "compiler_fingerprint"; "microseconds" ]) ]
    ~encode:(fun (pass : Lowering.test_pass) ->
      [ Blob pass.compiler_fingerprint; Integer pass.microseconds ])
    ~decode:(function
      | [| Blob compiler_fingerprint; Integer microseconds |] ->
          { compiler_fingerprint; microseconds }
      | _ -> Compiler_bug.raise_bug ~stage:"Database" "a row of test_run holds no test pass")

let rank_profile : Profile.t -> int = function Development -> 0 | Release -> 1

let unit =
  let make profile : string Tracker.fact =
    Tracker.make_fact ~stage:(Render profile) ~table:"unit" ~id_column:"item"
      ~fixed:[ ("profile", Integer (rank_profile profile)) ]
      ~groups:[ (Unit profile, [ "text_hash" ]) ]
      ~encode:(fun text_hash -> [ Tracker.marshal text_hash ])
      ~decode:(fun cells -> Tracker.unmarshal cells.(0))
  in
  let development = make Development and release = make Release in
  function Profile.Development -> development | Release -> release
