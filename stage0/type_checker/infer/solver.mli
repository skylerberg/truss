val flatten :
  State.state -> State.cause -> ?projections:(Types.ty * Types.ty) list ref -> Types.ty -> Types.ty

val require :
  State.state ->
  State.cause ->
  ?outputs:(string * Types.ty) list ->
  ?projections:(Types.ty * Types.ty) list ref ->
  Types.ty ->
  Types.trait_reference ->
  unit

val require_within :
  State.state ->
  Types.ty ->
  Language.Builtin_type.t list ->
  reason:(Types.ty -> Catalog.reported) ->
  Types.ty

val resolve_associated_type :
  State.state ->
  Types.ty ->
  Types.trait_reference ->
  Well_known.associated ->
  at:Core.origin ->
  Types.ty

val list_sealed_closures :
  State.state ->
  Types.ty ->
  includes:(Language.Builtin_type.t list -> bool) ->
  (Types.trait_reference * Types.trait_reference list) list

val decide_default :
  State.state -> site:State.decision_site -> at:Core.origin -> Types.ty -> Types.ty

val solve_head : State.state -> ?default_at:Core.origin -> int -> unit
val run_in_statement : State.state -> State.env -> Core.origin -> (unit -> 'a) -> 'a
