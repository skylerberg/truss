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
  Intrinsic.builtin list ->
  reason:(Types.ty -> Diagnostic.reported) ->
  Types.ty

val run_in_statement : State.state -> State.env -> Source.Definition_span.t -> (unit -> 'a) -> 'a
