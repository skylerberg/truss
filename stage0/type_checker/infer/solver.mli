val require :
  State.state ->
  State.cause ->
  ?outputs:(string * Types.ty) list ->
  Types.ty ->
  Types.trait_reference ->
  unit

val require_within :
  State.state ->
  Types.ty ->
  Language.Builtin_type.t list ->
  reason:(Types.ty -> Diagnostic.reported) ->
  Types.ty

val decide_default :
  State.state -> site:State.decision_site -> at:Source.Definition_span.t -> Types.ty -> Types.ty

val solve_head : State.state -> ?default_at:Source.Definition_span.t -> int -> unit
val run_in_statement : State.state -> State.env -> Source.Definition_span.t -> (unit -> 'a) -> 'a
