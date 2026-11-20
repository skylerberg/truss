val declare_buffer_slack : State.context -> Types.ty -> Logic.term -> Logic.term

val assume_same_length :
  State.context -> State.frame -> Types.ty -> before:Logic.term -> after:Logic.term -> unit

val find_sequence_element : State.context -> State.frame -> Types.ty -> Types.ty

val read_sequence_element :
  State.context ->
  State.frame ->
  Types.ty ->
  Logic.term ->
  Logic.term ->
  node:Core.id ->
  origin:Core.origin ->
  Logic.term

val write_sequence_element :
  State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term -> Logic.term -> Logic.term

val write_sequence_range :
  State.context ->
  State.frame ->
  Types.ty ->
  Logic.term ->
  start:Logic.term ->
  stop:Logic.term ->
  Logic.term ->
  Logic.term

val apply_slice :
  State.context ->
  State.frame ->
  node:Core.id ->
  Invocation.site ->
  base_type:Types.ty ->
  collection:Logic.term ->
  low:Logic.term ->
  high:Logic.term option ->
  State.frame * Logic.term * Logic.term * Logic.term

val make_buffer_capacity : State.context -> Types.ty -> Logic.term -> Logic.term

val make_buffer_model :
  State.context -> Language.Builtin_type.t -> Types.ty -> Logic.term -> Logic.term

val measure_type : Types.ty -> Types.function_type
val make_sequence_sum : State.context -> Types.ty -> Logic.term -> Logic.term -> Logic.term
val make_empty_parts : State.context -> State.frame -> Types.ty -> Logic.term
val append_part : State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term -> Logic.term

val translate_intrinsic :
  State.context ->
  State.frame ->
  site:Invocation.site ->
  Intrinsic.operation ->
  Types.ty list ->
  State.passed list ->
  changed:Logic.term list ->
  Types.ty ->
  Logic.term
