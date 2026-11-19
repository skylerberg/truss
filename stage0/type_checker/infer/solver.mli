val run_in_statement :
  State.state -> State.env -> Source.Definition_span.t -> (unit -> unit) -> unit

val infer_in_statement : State.state -> State.env -> Syntax.expression -> Types.ty

val require :
  State.state ->
  Types.ty ->
  Types.trait_reference ->
  on_met:(Interface.Impls.evidence -> unit) ->
  on_unmet:(Types.ty -> (string * Types.ty) option -> Diagnostic.reported) ->
  unit

val require_type :
  State.state ->
  Types.ty ->
  holds:(Types.ty -> bool) ->
  ?on_met:(Types.ty -> unit) ->
  on_unmet:(Types.ty -> Diagnostic.reported) ->
  unit ->
  Types.ty

val check_solved : State.state -> Types.ty -> (Types.ty -> unit) -> unit
val decide_for_method_call : State.state -> at:Source.Definition_span.t -> Types.ty -> Types.ty
