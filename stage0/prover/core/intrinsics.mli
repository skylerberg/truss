(** Slices, calls of the C library, buffers, and the intrinsics. *)

val apply_slice :
  State.context ->
  State.frame ->
  Invocation.site ->
  base_type:Types.ty ->
  collection:Logic.term ->
  low:Logic.term ->
  high:Logic.term option ->
  State.frame * Logic.term * Logic.term * Logic.term

val element_at : State.context -> Types.ty -> Logic.term -> Logic.term -> Logic.term

val run_replaced :
  State.context ->
  State.frame ->
  Types.ty ->
  before:Logic.term ->
  after:Logic.term ->
  start:Logic.term ->
  stop:Logic.term ->
  run:Logic.term option ->
  unit

val slice_place :
  State.context ->
  Invocation.site ->
  owner:State.passed_place ->
  owner_type:(State.frame -> Types.ty) ->
  low:Logic.term ->
  high:Logic.term ->
  State.passed_place

val buffer_capacity : State.context -> Types.ty -> Logic.term -> Logic.term
val buffer_model : State.context -> Intrinsic.builtin -> Types.ty -> Logic.term -> Logic.term
val measure_type : Types.ty -> Types.function_type
val sequence_sum : State.context -> Types.ty -> Logic.term -> Logic.term -> Logic.term
val appended : State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term -> Logic.term

val intrinsic :
  State.context ->
  State.frame ->
  site:Invocation.site ->
  Intrinsic.operation ->
  Types.ty list ->
  Logic.term list ->
  arguments:Core.origin option list ->
  changed:Logic.term list ->
  Types.ty ->
  Logic.term
