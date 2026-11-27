val make_float_literal : int * int -> float -> Logic.term
val compare_terms : Types.ty -> Language.Comparison.t -> Logic.term -> Logic.term -> Logic.term
val check_widened : Obligation.location -> is_written:bool -> Types.ty -> Types.ty -> unit
val convert_from_integer : State.frame -> Invocation.site -> Logic.term -> Logic.term
val list_impl_packages : State.environment -> Types.ty -> Path.package list
val make_equality : State.frame -> Types.ty -> Logic.term -> Logic.term -> Logic.term
val make_power : State.frame -> Logic.term -> Logic.term -> Logic.term

val translate_primitive_operation :
  State.frame ->
  site:Invocation.site ->
  Intrinsic.scalar ->
  Types.ty list ->
  Logic.term list ->
  arguments:Core.origin option list ->
  fallback:(unit -> Logic.term) ->
  Logic.term
