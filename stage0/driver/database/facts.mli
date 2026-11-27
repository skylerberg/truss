val resolved : Resolve.section -> Resolve.resolved Tracker.fact
val grant : Interface.Environment.grant Tracker.fact
val trait_header : Resolve.trait_header Tracker.fact
val constant_value : Interface.Constants.outcome Tracker.fact
val header : Interface.Environment.header Tracker.fact
val elaborated : Interface.Environment.elaborated_interface Tracker.fact
val interface : Interface.Environment.interface Tracker.view
val checked_interface : Interface.Environment.interface Tracker.view
val checked_elaborated : Interface.Environment.elaborated_interface Tracker.view
val derived_interface : Types.impl_interface Tracker.fact
val type_facts : Interface.Environment.type_facts Tracker.fact
val signature_check : unit Tracker.fact
val contract : Core.t Tracker.fact
val body : Infer.checked Tracker.fact
val body_form : Core.t Tracker.view
val body_tables : Infer.tables Tracker.view
val capability_uses : Infer.capability_use list Tracker.view
val ownership_modes : ((Syntax.id * Language.Mode.t) list * Core.mode_keyword list) Tracker.view
val body_mir : Mir.body_part Tracker.fact
val contract_mir : Mir.contract_part Tracker.fact
val generated_mir : (Mir.body_part * Mir.contract_part) Tracker.fact

type call_node = { callees : Path.t list; size_changes : Mir.Size_change.summary }

val call_node : call_node Tracker.fact
val callees : Path.t list Tracker.view
val size_changes : Mir.Size_change.summary Tracker.view
val recursion_group : Path.t list Tracker.fact
val proof_group : Path.t list Tracker.fact
val termination : Mir.Size_change.verdict Tracker.fact
val aborts_outside_group : bool Tracker.fact
val may_abort : bool Tracker.fact
val usage_check : unit Tracker.fact
val ownership : (Core.id list * Core.id list) list Tracker.fact
val dependency_use : bool Tracker.fact
val proof : Prover.proof Tracker.fact
val lowered : (Lowering.lowered, Lowering.unbuildable) result Tracker.fact
val test_key : (string, Lowering.unbuildable) result Tracker.fact
val evaluation : Lowering.evaluation Tracker.fact
val test_run : Lowering.test_pass Tracker.fact
val rank_profile : Profile.t -> int
val unit : Profile.t -> string Tracker.fact
